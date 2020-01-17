#include "mjolnir/bssbuilder.h"
#include "mjolnir/graphtilebuilder.h"

#include <boost/filesystem/operations.hpp>
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

struct BSSConnectionEdge {

  PointLL bss_ll = {};
  GraphId waynode = {};

  uint64_t wayid = -1;
  uint32_t speed = 0;
  std::vector<std::string> names = {};
  std::vector<PointLL> shape = {};
  Surface surface = Surface::kCompacted;
  CycleLane cycle_lane = CycleLane::kNone;
  RoadClass road_class = RoadClass::kUnclassified;
  Use use = Use::kOther;

  uint32_t forward_access = 0;
  uint32_t reverse_access = 0;

  uint32_t waynode_to_bss_edge_idx = -1;
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

std::tuple<BSSConnectionEdge, BSSConnectionEdge>
make_bss_conncection_edges(const PointLL& bss_ll,
                           const GraphTile& local_tile,
                           GraphId start_waynode,
                           const DirectedEdge& edge,
                           const PointLL& closest_point,
                           const size_t& closest_index,
                           uint16_t access) {

  auto edgeinfo = local_tile.edgeinfo(edge.edgeinfo_offset());
  auto speed = local_tile.GetSpeed(&edge);
  auto shape = edgeinfo.shape();

  if (!edge.forward()) {
    std::reverse(shape.begin(), shape.end());
  }
  std::vector<PointLL> startshape;
  std::vector<PointLL> endshape;

  std::copy(shape.begin(), shape.begin() + closest_index + 1, std::back_inserter(startshape));
  startshape.push_back(closest_point);
  startshape.push_back(bss_ll);

  endshape.push_back(bss_ll);
  endshape.push_back(closest_point);
  std::copy(shape.begin() + closest_index + 1, shape.end(), std::back_inserter(endshape));

  std::reverse(endshape.begin(), endshape.end());

  auto start2bss = BSSConnectionEdge{
      bss_ll,
      start_waynode,
      edgeinfo.wayid(),
      speed,
      edgeinfo.GetNames(),
      std::move(startshape),
      edge.surface(),
      edge.cyclelane(),
      edge.classification(),
      edge.use(),
      edge.forwardaccess() & access,
      edge.reverseaccess() & access,
      static_cast<uint32_t>(-1) // to be updated
  };

  auto end2bss = BSSConnectionEdge{
      bss_ll, edge.endnode(), edgeinfo.wayid(), speed, edgeinfo.GetNames(), std::move(endshape),
      edge.surface(), edge.cyclelane(), edge.classification(), edge.use(),
      // Note the accesses are opposite to those of start2bss
      edge.reverseaccess() & access, edge.forwardaccess() & access,
      static_cast<uint32_t>(-1) // to be updated
  };
  return {std::move(start2bss), std::move(end2bss)};
}

std::vector<BSSConnectionEdge> project(const GraphTile& local_tile,
                                       const std::vector<OSMNode>& osm_bss) {

  auto t1 = std::chrono::high_resolution_clock::now();
  auto scoped_finally = make_finally([&t1]() {
    auto t2 = std::chrono::high_resolution_clock::now();
    uint32_t secs = std::chrono::duration_cast<std::chrono::seconds>(t2 - t1).count();
    LOG_INFO("Finished - Projection took " + std::to_string(secs) + " secs");
  });

  std::vector<BSSConnectionEdge> res;

  auto local_level = TileHierarchy::levels().rbegin()->first;
  // In this loop, we try to find the way on which to project the bss node by iterating all nodes in
  // its corresponding tile... Not a good idea in term of performance... any better idea???
  for (const auto& bss : osm_bss) {

    // in/out connection between waynode to bss for pedestrian
    BSSConnectionEdge start_to_bss_ped{}, end_to_bss_ped{};

    // in/out connection between waynode to bss for bicycle
    BSSConnectionEdge start_to_bss_bicycle{}, end_to_bss_bicycle{};

    auto latlng = bss.latlng();
    auto bss_ll = PointLL{latlng.first, latlng.second};

    float mindist_ped = std::numeric_limits<float>::max();
    const DirectedEdge* best_directededge_ped = nullptr;
    uint32_t best_startnode_index_ped = 0;
    std::vector<PointLL> closest_shape_ped;
    std::tuple<PointLL, float, int> closest_ped;

    float mindist_bicycle = std::numeric_limits<float>::max();
    const DirectedEdge* best_directededge_bicycle = nullptr;
    uint32_t best_startnode_index_bicycle = 0;
    std::vector<PointLL> closest_shape_bicycle;
    std::tuple<PointLL, float, int> closest_bicycle;

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
        // This edge is not accessible neither to pedestrian nor to bicycle
        if (!(directededge->forwardaccess() & (kPedestrianAccess | kBicycleAccess)) ||
            directededge->is_shortcut()) {
          continue;
        }

        std::vector<PointLL> this_shape = edgeinfo.shape();
        if (!directededge->forward()) {
          std::reverse(this_shape.begin(), this_shape.end());
        }

        boost::optional<std::tuple<PointLL, float, int>> closest;

        if ((directededge->forwardaccess() & kPedestrianAccess)) {
          closest = bss_ll.Project(this_shape);
          if (std::get<1>(*closest) < mindist_ped) {
            mindist_ped = std::get<1>(*closest);
            closest_ped = *closest;
            closest_shape_ped = this_shape;
            best_directededge_ped = directededge;
            best_startnode_index_ped = i;
          }
        }
        if ((directededge->forwardaccess() & kBicycleAccess)) {
          if (!closest) {
            closest = bss_ll.Project(this_shape);
          }
          if (std::get<1>(*closest) < mindist_bicycle) {
            mindist_bicycle = std::get<1>(*closest);
            closest_bicycle = *closest;
            closest_shape_bicycle = this_shape;
            best_directededge_bicycle = directededge;
            best_startnode_index_bicycle = i;
          }
        }
      }
    }

    // store the attributes of the best directed edge where to project the bss

    GraphId startnode_ped = GraphId{local_tile.id().tileid(), local_level, best_startnode_index_ped};

    std::tie(start_to_bss_ped, end_to_bss_ped) =
        make_bss_conncection_edges(bss_ll, local_tile, startnode_ped, *best_directededge_ped,
                                   // Projected PointLL on the best edge
                                   std::get<0>(closest_ped),
                                   // Best shape index
                                   std::get<2>(closest_ped), kPedestrianAccess);

    if (!start_to_bss_ped.waynode.Is_Valid() && !end_to_bss_ped.waynode.Is_Valid()) {
      LOG_ERROR("Cannot find any pedestrian/bicycle edge to project");
      continue;
    }

    GraphId startnode_bicycle =
        GraphId{local_tile.id().tileid(), local_level, best_startnode_index_bicycle};
    std::tie(start_to_bss_bicycle, end_to_bss_bicycle) =
        make_bss_conncection_edges(bss_ll, local_tile, startnode_bicycle, *best_directededge_bicycle,
                                   // Projected PointLL on the best edge
                                   std::get<0>(closest_bicycle),
                                   // Best shape index
                                   std::get<2>(closest_bicycle), kBicycleAccess);

    if (!start_to_bss_bicycle.waynode.Is_Valid() && !end_to_bss_bicycle.waynode.Is_Valid()) {
      LOG_ERROR("Cannot find any pedestrian/bicycle edge to project");
      continue;
    }

    res.push_back(std::move(start_to_bss_ped));
    res.push_back(std::move(end_to_bss_ped));
    res.push_back(std::move(start_to_bss_bicycle));
    res.push_back(std::move(end_to_bss_bicycle));
  }

  assert(res.size() % 4 == 0);

  return res;
}

DirectedEdge make_directed_edge(const GraphId endnode,
                                const std::vector<PointLL>& shape,
                                const BSSConnectionEdge& conn,
                                const bool is_forward,
                                const uint32_t localedgeidx,
                                const uint32_t oppo_local_idx) {
  DirectedEdge directededge;
  directededge.set_endnode(endnode);
  directededge.set_length(std::max(1.0f, valhalla::midgard::length(conn.shape)));
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

void create_bss_node_and_edges(GraphTileBuilder& tilebuilder_local,
                               const GraphTile& tile,
                               std::mutex& lock,
                               std::vector<BSSConnectionEdge> new_osmconnections) {

  std::unordered_map<uint64_t, std::vector<size_t>> in_edges;
  std::unordered_map<PointLL, std::vector<size_t>> out_edges;

  for (size_t i = 0; i < new_osmconnections.size(); ++i) {
    const auto& osm = new_osmconnections[i];
    in_edges[osm.waynode.id()].push_back(i);
    out_edges[osm.bss_ll].push_back(i);
  }

  auto local_level = TileHierarchy::levels().rbegin()->first;

  auto scoped_finally = make_finally([&tilebuilder_local, &tile, &lock]() {
    LOG_INFO("Storing local tile data with bss nodes, tile id: " +
             std::to_string(tile.id().tileid()));
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
    auto it = in_edges.find(nodeid);
    if (it != in_edges.end()) {
      for (auto idx : it->second) {
        auto& conn = new_osmconnections[idx];
        size_t oppo_local_idx = 0; // to be updated
        size_t local_idx = tilebuilder_local.directededges().size() - edge_index;

        auto directededge = make_directed_edge({}, conn.shape, conn, true, local_idx, oppo_local_idx);
        conn.waynode_to_bss_edge_idx = tilebuilder_local.directededges().size();
        tilebuilder_local.directededges().emplace_back(std::move(directededge));
        ++added_edges;
      }
    }

    // Add the node and directed edges
    nb.set_edge_index(edge_index);
    nb.set_edge_count(tilebuilder_local.directededges().size() - edge_index);
    tilebuilder_local.nodes().emplace_back(std::move(nb));
  }

  for (const auto& bss_conns : out_edges) {
    auto bss_ll = bss_conns.first;
    const auto& conns = bss_conns.second;

    NodeInfo new_bss_node{tile.header()->base_ll(),
                          bss_ll,
                          RoadClass::kUnclassified,
                          static_cast<uint32_t>(kPedestrianAccess | kBicycleAccess),
                          NodeType::kBikeShare,
                          false};
    new_bss_node.set_mode_change(true);
    new_bss_node.set_edge_index(tilebuilder_local.directededges().size());
    // there should be 4 out edge from the bss node
    new_bss_node.set_edge_count(4);
    GraphId new_bss_node_graphid{tile.header()->graphid().tileid(), local_level,
                                 static_cast<uint32_t>(tilebuilder_local.nodes().size())};

    tilebuilder_local.nodes().emplace_back(std::move(new_bss_node));
    ++added_nodes;
    size_t edge_index = tilebuilder_local.directededges().size();

    assert(conns.size() == 4);

    for (auto idx : conns) {
      const auto& conn = new_osmconnections[idx];
      // get the directededge: waynode -> bssnode
      auto& in_edge = tilebuilder_local.directededges()[conn.waynode_to_bss_edge_idx];

      uint32_t out_edge_local_idx = tilebuilder_local.directededges().size() - edge_index;

      {
        in_edge.set_opp_local_idx(out_edge_local_idx);
        in_edge.set_endnode(new_bss_node_graphid);
        bool added;
        uint32_t edge_info_offset =
            tilebuilder_local.AddEdgeInfo(conn.waynode_to_bss_edge_idx, conn.waynode,
                                          new_bss_node_graphid, conn.wayid, 0, 0, 0, conn.shape,
                                          conn.names, 0, added);
        in_edge.set_edgeinfo_offset(edge_info_offset);
      }

      // create bssnode -> waynode
      {

        auto out_edge = make_directed_edge(conn.waynode, conn.shape, conn, false, out_edge_local_idx,
                                           in_edge.localedgeidx());
        bool added;
        uint32_t edge_info_offset =
            tilebuilder_local.AddEdgeInfo(tilebuilder_local.directededges().size(),
                                          new_bss_node_graphid, conn.waynode, conn.wayid, 0, 0, 0,
                                          conn.shape, conn.names, 0, added);

        out_edge.set_edgeinfo_offset(edge_info_offset);
        tilebuilder_local.directededges().emplace_back(std::move(out_edge));
        ++added_edges;
      }
    }
  };

  LOG_INFO(std::string("Added: ") + std::to_string(added_edges) + " edges and " +
           std::to_string(added_nodes) + " bss nodes");
}

using bss_by_tile_t = std::unordered_map<GraphId, std::vector<OSMNode>>;

void build(const boost::property_tree::ptree& pt,
           std::mutex& lock,
           bss_by_tile_t::const_iterator tile_start,
           bss_by_tile_t::const_iterator tile_end) {

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

    auto new_connections = project(*local_tile, tile_start->second);
    create_bss_node_and_edges(*tilebuilder_local, *local_tile, lock, std::move(new_connections));
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
    threads[i].reset(new std::thread(build, std::cref(pt.get_child("mjolnir")), std::ref(lock),
                                     tile_start, tile_end));
  }

  for (auto& thread : threads) {
    thread->join();
  }
}

} // namespace mjolnir
} // namespace valhalla
