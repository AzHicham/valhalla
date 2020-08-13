#include "mjolnir/bssbuilder.h"
#include "mjolnir/graphtilebuilder.h"

#include <algorithm>
#include <fstream>
#include <future>
#include <iostream>
#include <list>
#include <mutex>
#include <queue>
#include <set>
#include <thread>
#include <tuple>
#include <unordered_map>
#include <vector>

#include <boost/algorithm/string.hpp>
#include <boost/foreach.hpp>
#include <boost/range/algorithm.hpp>

#include <valhalla/proto/options.pb.h>

#include "baldr/datetime.h"
#include "baldr/graphreader.h"
#include "baldr/graphtile.h"
#include "baldr/tilehierarchy.h"
#include "filesystem.h"
#include "midgard/distanceapproximator.h"
#include "midgard/logging.h"
#include "midgard/sequence.h"
#include "midgard/util.h"
#include "mjolnir/osmnode.h"

using namespace valhalla::midgard;
using namespace valhalla::baldr;
using namespace valhalla::mjolnir;

namespace {

// We store in this struct all information about the bss connections which
// connect the bss node and the way node
struct BSSConnection {
  PointLL bss_ll = {};
  GraphId bss_node_id = {};
  GraphId way_node_id = {};
  // oppo_edgelocalidx of the outbound edge from bss node to way node
  uint32_t bss_oppo_edgelocalidx = -1;
  // oppo_edgelocalidx of the outbound edge from way node to bss node
  uint32_t way_oppo_edgelocalidx = -1;
  uint64_t wayid = -1;
  uint32_t speed = 0;
  std::vector<std::string> names = {};
  std::vector<PointLL> shape = {};
  bool is_forward = true;
  Surface surface = Surface::kCompacted;
  CycleLane cycle_lane = CycleLane::kNone;
  RoadClass road_class = RoadClass::kUnclassified;
  Use use = Use::kOther;

  uint32_t forward_access = kPedestrianAccess | kBicycleAccess;
  uint32_t reverse_access = kPedestrianAccess | kBicycleAccess;

  // operator < for sorting
  bool operator<(const BSSConnection& other) const {
    if (way_node_id.tileid() != other.way_node_id.tileid()) {
      return way_node_id.tileid() < other.way_node_id.tileid();
    }
    return way_node_id.id() < other.way_node_id.id();
  }
};

template <typename T> struct Finally {
  T t;
  explicit Finally(T t) : t(t){};
  Finally() = delete;
  Finally(Finally&& f) = default;
  Finally(const Finally&) = delete;
  Finally& operator=(const Finally&) = delete;
  Finally& operator=(Finally&&) = delete;
  ~Finally() {
    t();
  };
};

template <typename T> Finally<T> make_finally(T t) {
  return Finally<T>{t};
};

DirectedEdge make_directed_edge(const GraphId endnode,
                                const std::vector<PointLL>& shape,
                                const BSSConnection& conn,
                                const bool is_forward,
                                const uint32_t localedgeidx,
                                const uint32_t oppo_local_idx) {
  DirectedEdge directededge;
  directededge.set_endnode(endnode);
  directededge.set_length(std::max(1.0f, valhalla::midgard::length(shape)));
  directededge.set_use(conn.use);
  directededge.set_speed(conn.speed);
  directededge.set_surface(conn.surface);
  directededge.set_cyclelane(conn.cycle_lane);
  directededge.set_classification(conn.road_class);
  directededge.set_localedgeidx(localedgeidx);

  auto accesses = std::vector<uint32_t>{conn.forward_access, conn.reverse_access};
  directededge.set_forwardaccess(accesses[static_cast<size_t>(!is_forward)]);
  directededge.set_reverseaccess(accesses[static_cast<size_t>(is_forward)]);

  directededge.set_named(conn.names.size());
  directededge.set_forward(is_forward);
  directededge.set_opp_local_idx(oppo_local_idx);
  directededge.set_bss_connection(true);
  return directededge;
}

using bss_by_tile_t = std::unordered_map<GraphId, std::vector<OSMNode>>;

std::vector<BSSConnection> project(const GraphTile& local_tile,
                                       GraphReader& reader_local_level,
                                       const std::vector<OSMNode>& osm_bss) {
  auto t1 = std::chrono::high_resolution_clock::now();
  auto scoped_finally = make_finally([&t1, size = osm_bss.size()]() {
    auto t2 = std::chrono::high_resolution_clock::now();
    uint32_t secs = std::chrono::duration_cast<std::chrono::seconds>(t2 - t1).count();
    LOG_INFO("Projection Finished - Projection of " + std::to_string(size) + " bike station  took " +
             std::to_string(secs) + " secs");
  });

  std::vector<BSSConnection> res;
  auto local_level = TileHierarchy::levels().rbegin()->first;
  // In this loop, we try to find the way on which to project the bss node by iterating all nodes in
  // its corresponding tile... Not a good idea in term of performance... any better idea???
  for (const auto& bss : osm_bss) {

    auto latlng = bss.latlng();
    auto bss_ll = PointLL{latlng.first, latlng.second};

    float mindist = std::numeric_limits<float>::max();

    const DirectedEdge* best_directededge = nullptr;
    uint32_t best_startnode_index = -1;
    std::vector<PointLL> closest_shape;
    std::tuple<PointLL, float, int> closest;
    uint32_t bss_oppo_edgelocalidx = -1;

    // Loop over all nodes in the tile to find the nearest edge
    for (uint32_t i = 0; i < local_tile.header()->nodecount(); ++i) {
      const NodeInfo* node = local_tile.node(i);
      for (uint32_t j = 0; j < node->edge_count(); ++j) {
        const DirectedEdge* directededge = local_tile.directededge(node->edge_index() + j);
        auto edgeinfo = local_tile.edgeinfo(directededge->edgeinfo_offset());

        if (directededge->use() == Use::kTransitConnection ||
            directededge->use() == Use::kEgressConnection ||
            directededge->use() == Use::kPlatformConnection) {
          continue;
        }
        if ((!(directededge->forwardaccess() & kBicycleAccess) &&
             !(directededge->forwardaccess() & kPedestrianAccess)) ||
            directededge->is_shortcut()) {
          continue;
        }

        std::vector<PointLL> this_shape = edgeinfo.shape();
        if (!directededge->forward()) { 
            std::reverse(this_shape.begin(), this_shape.end());
        }
        auto this_closest = bss_ll.Project(this_shape);

        if (std::get<1>(this_closest) < mindist) {
          mindist = std::get<1>(this_closest);
          closest = this_closest;
          closest_shape = this_shape;
          best_directededge = directededge;
          best_startnode_index = i;
          bss_oppo_edgelocalidx = node->edge_count();
        }
      }
    }

    BSSConnection bss_conn_start = {};
    {
      bss_conn_start.bss_ll = bss_ll;
      bss_conn_start.way_oppo_edgelocalidx = 0;

      auto edgeinfo = local_tile.edgeinfo(best_directededge->edgeinfo_offset());
      bss_conn_start.speed = local_tile.GetSpeed(best_directededge);
      bss_conn_start.names = edgeinfo.GetNames();
      bss_conn_start.surface = best_directededge->surface();
      bss_conn_start.cycle_lane = best_directededge->cyclelane();
      bss_conn_start.road_class = best_directededge->classification();
      bss_conn_start.use = best_directededge->use();
      bss_conn_start.forward_access = best_directededge->forwardaccess();
      bss_conn_start.reverse_access = best_directededge->reverseaccess();

      bss_conn_start.is_forward = true;
    }

    BSSConnection bss_conn_end = {};
    {
      bss_conn_end.bss_ll = bss_ll;
      bss_conn_end.way_oppo_edgelocalidx = 1;
      auto edgeinfo = local_tile.edgeinfo(best_directededge->edgeinfo_offset());
      bss_conn_end.speed = local_tile.GetSpeed(best_directededge);
      bss_conn_end.names = edgeinfo.GetNames();
      bss_conn_end.surface = best_directededge->surface();
      bss_conn_end.cycle_lane = best_directededge->cyclelane();
      bss_conn_end.road_class = best_directededge->classification();
      bss_conn_end.use = best_directededge->use();
      bss_conn_end.forward_access = best_directededge->forwardaccess();
      bss_conn_end.reverse_access = best_directededge->reverseaccess();
      bss_conn_end.is_forward = false;
    }

    auto closest_point = std::get<0>(closest);
    auto cloest_index = std::get<2>(closest);

    std::copy(closest_shape.begin(), closest_shape.begin() + cloest_index + 1,
              std::back_inserter(bss_conn_start.shape));
    bss_conn_start.shape.push_back(closest_point);
    bss_conn_start.shape.push_back(bss_ll);

    bss_conn_end.shape.push_back(bss_ll);
    bss_conn_end.shape.push_back(closest_point);
    std::copy(closest_shape.begin() + cloest_index + 1, closest_shape.end(),
              std::back_inserter(bss_conn_end.shape));
    
    // store the attributes of the best directed edge where to project the bss
    bss_conn_start.way_node_id = {local_tile.id().tileid(), local_level, best_startnode_index};
    bss_conn_start.bss_oppo_edgelocalidx = bss_oppo_edgelocalidx;

    bss_conn_end.way_node_id = best_directededge->endnode();

    // we have to check if bss connection's end node is in the same tile as its start node and bss node
    if (bss_conn_end.way_node_id.tileid() == bss_conn_start.way_node_id.tileid()) {
      const NodeInfo* node = local_tile.node(bss_conn_end.way_node_id.id());
      bss_conn_end.bss_oppo_edgelocalidx = node->edge_count();
    } else {
      auto end_local_tile = reader_local_level.GetGraphTile(bss_conn_end.way_node_id);
      bss_conn_end.bss_oppo_edgelocalidx =
          end_local_tile->node(bss_conn_end.way_node_id.id())->edge_count();
    }

    if (!bss_conn_start.way_node_id.Is_Valid() && !bss_conn_end.way_node_id.Is_Valid()) {
      LOG_ERROR("Cannot find any edge to project");
      continue;
    }
    res.push_back(std::move(bss_conn_start));
    res.push_back(std::move(bss_conn_end));
  }

  return res;
}

void add_bss_nodes_and_edges(GraphTileBuilder& tilebuilder_local,
                             const GraphTile& tile,
                             std::mutex& lock,
                             std::vector<BSSConnection>& new_connections) {
  auto local_level = TileHierarchy::levels().rbegin()->first;
  auto scoped_finally = make_finally([&tilebuilder_local, &tile, &lock]() {
    LOG_INFO("Storing local tile data with bss nodes, tile id: " +
             std::to_string(tile.id().tileid()));
    std::lock_guard<std::mutex> l(lock);
    tilebuilder_local.StoreTileData();
  });
  for (auto it = new_connections.begin(); it < new_connections.end(); std::advance(it, 2)) {
    auto& bss_to_start = *it;
    auto& bss_to_end = *(it + 1);
    size_t bss_node_id = tilebuilder_local.nodes().size();

    size_t edge_index = tilebuilder_local.directededges().size();
    NodeInfo new_bss_node{tile.header()->base_ll(), bss_to_start.bss_ll,
                          bss_to_start.road_class,  (kPedestrianAccess | kBicycleAccess),
                          NodeType::kBikeShare,     false};
    new_bss_node.set_mode_change(true);
    new_bss_node.set_edge_index(edge_index);
    // there should be two outbound edge for the bss node
    new_bss_node.set_edge_count(2);

    GraphId new_bss_node_graphid{tile.header()->graphid().tileid(), local_level,
                                 static_cast<uint32_t>(tilebuilder_local.nodes().size())};

    bss_to_start.bss_node_id = bss_to_end.bss_node_id = new_bss_node_graphid;

    tilebuilder_local.nodes().emplace_back(std::move(new_bss_node));
    {
      bool added;
      auto reversed_shape = bss_to_start.shape;
      auto directededge = make_directed_edge(bss_to_start.way_node_id, reversed_shape, bss_to_start,
    		                                false, 0, bss_to_start.bss_oppo_edgelocalidx);

      uint32_t edge_info_offset =
          tilebuilder_local.AddEdgeInfo(0, new_bss_node_graphid, bss_to_start.way_node_id,
                                        bss_to_start.wayid, 0, 0, 0, reversed_shape,
                                        bss_to_start.names, 0, added);
      directededge.set_edgeinfo_offset(edge_info_offset);
      tilebuilder_local.directededges().emplace_back(std::move(directededge));
    }

    {
      bool added;
      auto reversed_shape = bss_to_end.shape;
      auto directededge = make_directed_edge(bss_to_end.way_node_id, reversed_shape, bss_to_end, true,
                                             0, bss_to_end.bss_oppo_edgelocalidx);
      uint32_t edge_info_offset =
          tilebuilder_local.AddEdgeInfo(0, new_bss_node_graphid, bss_to_end.way_node_id,
                                        bss_to_end.wayid, 0, 0, 0, reversed_shape, bss_to_end.names,
                                        0, added);
      directededge.set_edgeinfo_offset(edge_info_offset);
      tilebuilder_local.directededges().emplace_back(std::move(directededge));
    }
  }
}

void project_and_add_bss_nodes(const boost::property_tree::ptree& pt,
                               std::mutex& lock,
                               bss_by_tile_t::const_iterator tile_start,
                               bss_by_tile_t::const_iterator tile_end,
                               std::vector<BSSConnection>& all) {

  GraphReader reader_local_level(pt);
  for (; tile_start != tile_end; ++tile_start) {

    const GraphTile* local_tile = nullptr;
    std::unique_ptr<GraphTileBuilder> tilebuilder_local = nullptr;
    {
      std::lock_guard<std::mutex> l(lock);

      auto tile_id = tile_start->first;
      local_tile = reader_local_level.GetGraphTile(tile_id);
      tilebuilder_local.reset(new GraphTileBuilder{reader_local_level.tile_dir(), tile_id, true});
    }

    auto new_connections = project(*local_tile, reader_local_level, tile_start->second);
    add_bss_nodes_and_edges(*tilebuilder_local, *local_tile, lock, new_connections);
    {
      std::lock_guard<std::mutex> l{lock};
      std::move(new_connections.begin(), new_connections.end(), std::back_inserter(all));
    }
  }
}

void create_edges(GraphTileBuilder& tilebuilder_local,
                  const GraphTile& tile,
                  std::mutex& lock,
                  const std::vector<BSSConnection>& bss_connections) {
  // GraphTileBuilder tilebuilder_local(reader.tile_dir(), tile.header()->graphid(), true);
  auto local_level = TileHierarchy::levels().rbegin()->first;

  auto t1 = std::chrono::high_resolution_clock::now();

  auto scoped_finally = make_finally([&tilebuilder_local, &tile, &lock, t1]() {
    auto t2 = std::chrono::high_resolution_clock::now();
    uint32_t secs = std::chrono::duration_cast<std::chrono::seconds>(t2 - t1).count();

    LOG_INFO("Tile id: " + std::to_string(tile.id().tileid()) + " It took " + std::to_string(secs) +
             " seconds to create edges. Now storing local tile data with new edges");
    std::lock_guard<std::mutex> l(lock);
    tilebuilder_local.StoreTileData();
  });

  // Move existing nodes and directed edge builder vectors and clear the lists
  std::vector<NodeInfo> currentnodes(std::move(tilebuilder_local.nodes()));
  uint32_t nodecount = currentnodes.size();

  tilebuilder_local.nodes().clear();
  std::vector<DirectedEdge> currentedges(std::move(tilebuilder_local.directededges()));
  uint32_t edgecount = currentedges.size();
  tilebuilder_local.directededges().clear();

  // Get the directed edge index of the first sign. If no signs are
  // present in this tile set a value > number of directed edges
  uint32_t signidx = 0;
  uint32_t nextsignidx = (tilebuilder_local.header()->signcount() > 0)
                             ? tilebuilder_local.sign(0).index()
                             : currentedges.size() + 1;
  uint32_t signcount = tilebuilder_local.header()->signcount();

  // Get the directed edge index of the first access restriction.
  uint32_t residx = 0;
  uint32_t nextresidx = (tilebuilder_local.header()->access_restriction_count() > 0)
                            ? tilebuilder_local.accessrestriction(0).edgeindex()
                            : currentedges.size() + 1;
  uint32_t rescount = tilebuilder_local.header()->access_restriction_count();

  // Iterate through the nodes - add back any stored edges and insert any
  // connections from a node to a transit stop. Update each nodes edge index.
  uint32_t added_edges = 0;
  uint32_t added_nodes = 0;

  for (auto& nb : currentnodes) {
    size_t nodeid = tilebuilder_local.nodes().size();
    size_t edge_index = tilebuilder_local.directededges().size();

    // recreate the node and its edges
    {
      // Copy existing directed edges from this node and update any signs using
      // the directed edge index
      for (uint32_t i = 0, idx = nb.edge_index(); i < nb.edge_count(); i++, idx++) {
        tilebuilder_local.directededges().emplace_back(std::move(currentedges[idx]));

        // Update any signs that use this idx - increment their index by the
        // number of added edges
        while (idx == nextsignidx && signidx < signcount) {
          if (!currentedges[idx].sign()) {
            LOG_ERROR("Signs for this index but directededge says no sign");
          }
          tilebuilder_local.sign_builder(signidx).set_index(idx + added_edges);

          // Increment to the next sign and update next signidx
          signidx++;
          nextsignidx = (signidx >= signcount) ? 0 : tilebuilder_local.sign(signidx).index();
        }

        // Add any restrictions that use this idx - increment their index by the
        // number of added edges
        while (idx == nextresidx && residx < rescount) {
          if (!currentedges[idx].access_restriction()) {
            LOG_ERROR("Access restrictions for this index but directededge says none");
          }
          tilebuilder_local.accessrestriction_builder(residx).set_edgeindex(idx + added_edges);

          // Increment to the next restriction and update next residx
          residx++;
          nextresidx =
              (residx >= rescount) ? 0 : tilebuilder_local.accessrestriction(residx).edgeindex();
        }
      }
    }

    auto target = BSSConnection{};
    target.way_node_id = {0, 0, static_cast<uint32_t>(nodeid)};

    auto comp = [](const BSSConnection& lhs, const BSSConnection& rhs) {
      return lhs.way_node_id.id() < rhs.way_node_id.id();
    };
    auto lower = std::lower_bound(bss_connections.begin(), bss_connections.end(), target, comp);
    auto upper = std::upper_bound(bss_connections.begin(), bss_connections.end(), target, comp);

    while (lower != upper && lower != bss_connections.end()) {
      size_t local_idx = tilebuilder_local.directededges().size() - edge_index;

      auto directededge =
          make_directed_edge(lower->bss_node_id, lower->shape, *lower, lower->is_forward, local_idx,
                             lower->way_oppo_edgelocalidx);

      bool added;
      uint32_t edge_info_offset =
          tilebuilder_local.AddEdgeInfo(0, lower->way_node_id, lower->bss_node_id, lower->wayid, 0, 0,
                                        0, lower->shape, lower->names, 0, added);
      directededge.set_edgeinfo_offset(edge_info_offset);

      tilebuilder_local.directededges().emplace_back(std::move(directededge));
      added_edges++;
      std::advance(lower, 1);
    };

    // Add the node and directed edges
    nb.set_edge_index(edge_index);
    nb.set_edge_count(tilebuilder_local.directededges().size() - edge_index);
    tilebuilder_local.nodes().emplace_back(std::move(nb));
  }

  LOG_INFO(std::string("Added: ") + std::to_string(added_edges) + " edges");
}

void create_edges_from_way_node(
    const boost::property_tree::ptree& pt,
    std::mutex& lock,
    std::unordered_map<GraphId, std::vector<BSSConnection>>::const_iterator tile_start,
    std::unordered_map<GraphId, std::vector<BSSConnection>>::const_iterator tile_end) {

  GraphReader reader_local_level(pt);
  for (; tile_start != tile_end; ++tile_start) {

    const GraphTile* local_tile = nullptr;
    std::unique_ptr<GraphTileBuilder> tilebuilder_local = nullptr;
    {
      std::lock_guard<std::mutex> l(lock);

      auto tile_id = tile_start->first;
      local_tile = reader_local_level.GetGraphTile(tile_id);
      tilebuilder_local.reset(new GraphTileBuilder{reader_local_level.tile_dir(), tile_id, true});
    }
    create_edges(*tilebuilder_local, *local_tile, lock, tile_start->second);
  }
}

} // namespace

namespace valhalla {
namespace mjolnir {

// Add bss to the graph
void BssBuilder::Build(const boost::property_tree::ptree& pt, const std::string& bss_nodes_bin) {

  if (!pt.get<bool>("mjolnir.import_bike_share_stations", false)) {
    return;
  }

  LOG_INFO("Importing Bike Share station");

  auto t1 = std::chrono::high_resolution_clock::now();

  auto scoped_finally = make_finally([&t1]() {
    auto t2 = std::chrono::high_resolution_clock::now();
    uint32_t secs = std::chrono::duration_cast<std::chrono::seconds>(t2 - t1).count();
    LOG_INFO("Finished - BssBuilder took " + std::to_string(secs) + " secs");
  });

  midgard::sequence<mjolnir::OSMNode> osm_nodes{bss_nodes_bin, false};

  // bss_by_tile_t bss_by_tile;
  bss_by_tile_t bss_by_tile;

  GraphReader reader(pt.get_child("mjolnir"));
  auto local_level = TileHierarchy::levels().rbegin()->first;

  // Group the nodes by their tiles. In the next step, we will work on each tile only once
  for (const auto& node : osm_nodes) {
    auto latlng = node.latlng();
    auto tile_id = TileHierarchy::GetGraphId({latlng.first, latlng.second}, local_level);
    const GraphTile* local_tile = reader.GetGraphTile(tile_id);
    if (!local_tile) {
      LOG_INFO("Cannot find node in tiles");
      continue;
    }
    bss_by_tile[tile_id].push_back(node);
  }

  size_t nb_threads =
      std::max(static_cast<uint32_t>(1),
               pt.get<uint32_t>("mjolnir.concurrency", std::thread::hardware_concurrency()));
  std::vector<std::shared_ptr<std::thread>> threads(nb_threads);

  // An atomic object we can use to do the synchronization
  std::mutex lock;

  // Start the threads
  LOG_INFO("Adding " + std::to_string(osm_nodes.size()) + " bike share stations to " +
           std::to_string(bss_by_tile.size()) + " local graphs with " + std::to_string(nb_threads) +
           " thread(s)");

  std::vector<BSSConnection> all;
  {
    size_t floor = bss_by_tile.size() / threads.size();
    size_t at_ceiling = bss_by_tile.size() - (threads.size() * floor);
    bss_by_tile_t::const_iterator tile_start, tile_end = bss_by_tile.begin();

    for (size_t i = 0; i < threads.size(); ++i) {
      // Figure out how many this thread will work on (either ceiling or floor)
      size_t tile_count = (i < at_ceiling ? floor + 1 : floor);
      // Where the range begins
      tile_start = tile_end;
      // Where the range ends
      std::advance(tile_end, tile_count);
      // Make the thread
      threads[i].reset(new std::thread(project_and_add_bss_nodes, std::cref(pt.get_child("mjolnir")),
                                       std::ref(lock), tile_start, tile_end, std::ref(all)));
    }

    for (auto& thread : threads) {
      thread->join();
    }
  }

  boost::sort(all);

  std::unordered_map<GraphId, std::vector<BSSConnection>> map;

  auto chunk_start = all.begin();
  do {
    auto tileid = chunk_start->way_node_id.tileid();
    auto chunk_end = std::stable_partition(chunk_start, all.end(), [tileid](const auto& conn) {
      return tileid == conn.way_node_id.tileid();
    });

    std::move(chunk_start, chunk_end, std::back_inserter(map[{tileid, local_level, 0}]));

    chunk_start = chunk_end;

  } while (chunk_start != all.end());

  {
    size_t floor = map.size() / threads.size();
    size_t at_ceiling = map.size() - (threads.size() * floor);
    std::unordered_map<GraphId, std::vector<BSSConnection>>::const_iterator tile_start,
        tile_end = map.begin();

    for (size_t i = 0; i < threads.size(); ++i) {
      // Figure out how many this thread will work on (either ceiling or floor)
      size_t tile_count = (i < at_ceiling ? floor + 1 : floor);
      // Where the range begins
      tile_start = tile_end;
      // Where the range ends
      std::advance(tile_end, tile_count);
      // Make the thread
      threads[i].reset(new std::thread(create_edges_from_way_node, std::cref(pt.get_child("mjolnir")),
                                       std::ref(lock), tile_start, tile_end));
    }

    for (auto& thread : threads) {
      thread->join();
    }
  }
}

} // namespace mjolnir
} // namespace valhalla
