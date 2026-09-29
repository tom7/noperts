// split-chart_test.cc: Rigorous tests for split-chart tree partitioning logic
// and Move-To-Front (MTF) shard assignment verification pass.

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "split-chart.h"

#ifdef CHECK
#undef CHECK
#endif
#define CHECK(expr)                                                        \
  do {                                                                     \
    if (!(expr)) {                                                         \
      fprintf(stderr, "FAILED at %s:%d: %s\n", __FILE__, __LINE__, #expr); \
      abort();                                                             \
    }                                                                      \
  } while (0)

static void PopulateChildCounts(std::unordered_map<int64_t, InternalNode> &map) {
  for (auto &[id, node] : map) node.num_children = 0;
  for (const auto &[id, node] : map) {
    if (node.parent_id != -1 && map.count(node.parent_id)) {
      map[node.parent_id].num_children++;
    }
  }
}

static void TestBalancedBinaryTree() {
  printf("Testing balanced binary tree partitioning...\n");

  std::unordered_map<int64_t, InternalNode> node_map;
  for (int64_t i = 1; i <= 63; i++) {
    int64_t parent = (i == 1) ? -1 : (i / 2);
    int depth = 0;
    for (int64_t p = i; p > 1; p /= 2) depth++;
    node_map[i] = InternalNode{
        .parent_id = parent,
        .count = 0,
        .depth = depth,
    };
  }

  // Each of nodes 32..63 has 2 direct leaves
  int64_t total_leaves = 0;
  for (int64_t i = 32; i <= 63; i++) {
    node_map[i].count += 2;
    total_leaves += 2;
  }
  CHECK(total_leaves == 64);
  PopulateChildCounts(node_map);

  // Test target T = 8
  {
    SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 8, 1000);
    CHECK(res.subcharts.size() == 8);
    CHECK(res.sum_subchart_leaves == 64);
    CHECK(res.skeleton_leaves == 0);
    for (const auto &s : res.subcharts) {
      CHECK(s.count == 8);
      CHECK(s.depth == 3);
    }
    CHECK(res.stats.min_count == 8);
    CHECK(res.stats.max_count == 8);
    CHECK(res.stats.ratio == 1.0);
  }

  // Test target T = 16
  {
    SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 16, 1000);
    CHECK(res.subcharts.size() == 16);
    CHECK(res.sum_subchart_leaves == 64);
    for (const auto &s : res.subcharts) {
      CHECK(s.count == 4);
      CHECK(s.depth == 4);
    }
  }

  // Test target T = 32
  {
    SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 32, 1000);
    CHECK(res.subcharts.size() == 32);
    CHECK(res.sum_subchart_leaves == 64);
    for (const auto &s : res.subcharts) {
      CHECK(s.count == 2);
      CHECK(s.depth == 5);
    }
  }

  printf("  Balanced binary tree tests PASSED.\n");
}

static void TestViewTreeQuadSplits() {
  printf("Testing 4-way view split tree...\n");

  std::unordered_map<int64_t, InternalNode> node_map;
  node_map[0] = InternalNode{.parent_id = -1, .count = 0, .depth = 0};
  for (int64_t i = 1; i <= 4; i++) {
    node_map[i] = InternalNode{.parent_id = 0, .count = 0, .depth = 1};
  }
  int64_t total_leaves = 0;
  for (int64_t i = 5; i <= 20; i++) {
    int64_t p = 1 + (i - 5) / 4;
    node_map[i] = InternalNode{.parent_id = p, .count = 10, .depth = 2};
    total_leaves += 10;
  }
  CHECK(total_leaves == 160);
  PopulateChildCounts(node_map);

  // Split with T = 4
  SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 4, 1000);
  CHECK(res.subcharts.size() == 4);
  CHECK(res.sum_subchart_leaves == 160);
  for (const auto &s : res.subcharts) {
    CHECK(s.count == 40);
    CHECK(s.depth == 1);
  }

  printf("  4-way view tree tests PASSED.\n");
}

static void TestTwoPhaseCoarseRollup() {
  printf("Testing two-phase coarse rollup and Huffman priority...\n");

  std::unordered_map<int64_t, InternalNode> node_map;
  int64_t total_leaves = 0;

  for (int64_t i = 1; i <= 1023; i++) {
    int64_t parent = (i == 1) ? -1 : (i / 2);
    node_map[i] = InternalNode{
        .parent_id = parent,
        .count = 0,
        .depth = 1,
    };
  }

  for (int64_t i = 512; i <= 1023; i++) {
    node_map[i].count = 1;
    total_leaves += 1;
  }
  PopulateChildCounts(node_map);

  SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 16, 64);
  CHECK(res.coarse_waves > 0);
  CHECK(res.subcharts.size() == 16);
  CHECK(res.sum_subchart_leaves == total_leaves);
  for (const auto &s : res.subcharts) {
    CHECK(s.count == 32);
  }

  printf("  Two-phase coarse rollup tests PASSED.\n");
}

static void TestSkeletonLeavesPreserved() {
  printf("Testing preservation of skeleton leaves...\n");

  std::unordered_map<int64_t, InternalNode> node_map;
  node_map[0] = InternalNode{.parent_id = -1, .count = 5, .depth = 0};
  node_map[1] = InternalNode{.parent_id = 0, .count = 50, .depth = 1};
  node_map[2] = InternalNode{.parent_id = 0, .count = 50, .depth = 1};
  int64_t total_leaves = 105;
  PopulateChildCounts(node_map);

  SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 2, 100);
  CHECK(res.subcharts.size() == 2);
  CHECK(res.sum_subchart_leaves == 100);
  CHECK(res.skeleton_leaves == 5);
  CHECK(res.skeleton_splits == 1);
  CHECK(res.sum_subchart_leaves + res.skeleton_leaves == total_leaves);

  printf("  Preservation of skeleton leaves tests PASSED.\n");
}

static void TestLookupShardMTF() {
  printf("Testing Move-To-Front shard lookup...\n");

  std::vector<std::unordered_set<int64_t>> shard_sets(4);
  shard_sets[0].insert({10, 11});
  shard_sets[1].insert({20, 21});
  shard_sets[2].insert({30, 31});
  shard_sets[3].insert({40, 41});

  std::vector<int> mtf_order = {0, 1, 2, 3};
  std::vector<int64_t> mtf_hits(4, 0);

  // Probe 30 -> found in shard 2 at pos 2
  int s = LookupShardMTF(30, shard_sets, mtf_order, mtf_hits);
  CHECK(s == 2);
  CHECK(mtf_hits[2] == 1);
  CHECK(mtf_order[0] == 2);
  CHECK(mtf_order[1] == 0);
  CHECK(mtf_order[2] == 1);
  CHECK(mtf_order[3] == 3);

  // Probe 31 -> found in shard 2 at pos 0!
  s = LookupShardMTF(31, shard_sets, mtf_order, mtf_hits);
  CHECK(s == 2);
  CHECK(mtf_hits[0] == 1);
  CHECK(mtf_order[0] == 2);

  // Probe not found
  s = LookupShardMTF(999, shard_sets, mtf_order, mtf_hits);
  CHECK(s == -1);

  printf("  Move-To-Front shard lookup tests PASSED.\n");
}

static void TestStreamAndAssignShards() {
  printf("Testing StreamAndAssignShards on synthetic chart...\n");

  // Create temporary chart file:
  // Root 0 splits into 1 and 2
  // Node 1 splits into 3 and 4
  // Node 2 splits into 5 and 6
  // Leaves under 3, 4, 5, 6 (10 leaves each, total 40 leaves)
  const char *test_file = "/tmp/test_chart_assignment.rows.log";
  {
    std::ofstream f(test_file);
    f << "sp 0 -1 0 1 2\n";
    f << "sp 1 0 1 3 4\n";
    f << "sp 2 0 1 5 6\n";
    f << "sp 3 1 2 7 8\n";
    f << "sp 4 1 2 9 a\n";
    f << "sp 5 2 2 b c\n";
    f << "sp 6 2 2 d e\n";
    // 10 leaves under 3
    for (int i = 0; i < 10; i++) f << "ce 10" << i << " 3 3 0 0.05 1 2 3\n";
    // 10 leaves under 4
    for (int i = 0; i < 10; i++) f << "ce 20" << i << " 4 3 0 0.05 1 2 3\n";
    // 10 leaves under 5
    for (int i = 0; i < 10; i++) f << "ce 30" << i << " 5 3 0 0.05 1 2 3\n";
    // 10 leaves under 6
    for (int i = 0; i < 10; i++) f << "ce 40" << i << " 6 3 0 0.05 1 2 3\n";
  }

  // Suppose subchart roots are nodes 1 and 2 (T = 2)
  SplitResult split_res;
  split_res.subcharts = {
      SubchartInfo{.id = 1, .parent_id = 0, .depth = 1, .count = 20},
      SubchartInfo{.id = 2, .parent_id = 0, .depth = 1, .count = 20},
  };
  split_res.skeleton_split_ids = {0};

  AssignmentResult assign = StreamAndAssignShards(test_file, split_res, nullptr);
  CHECK(assign.error.empty());
  CHECK(assign.passes_needed == 1);
  CHECK(assign.unassigned_rows == 0);
  CHECK(assign.skeleton_splits == 1);
  CHECK(assign.skeleton_leaves == 0);
  CHECK(assign.shards.size() == 2);
  CHECK(assign.shards[0].assigned_leaves == 20);
  CHECK(assign.shards[0].assigned_splits == 3);  // 1, 3, 4
  CHECK(assign.shards[1].assigned_leaves == 20);
  CHECK(assign.shards[1].assigned_splits == 3);  // 2, 5, 6
  CHECK(assign.is_exact_match);
  CHECK(assign.pos0_hit_rate > 50.0);

  std::remove(test_file);
  printf("  StreamAndAssignShards synthetic tests PASSED.\n");
}

static void TestOutOfOrderAssignment() {
  printf("Testing out-of-order row assignment multi-pass convergence...\n");

  // Create temporary chart file with deliberately inverted order:
  // Leaves appear BEFORE their split parents!
  const char *test_file = "/tmp/test_chart_out_of_order.rows.log";
  {
    std::ofstream f(test_file);
    // Leaf under 3 appears first!
    f << "ce 100 3 3 0 0.05 1 2 3\n";
    // Split 3 appears second!
    f << "sp 3 1 2 7 8\n";
    // Split 1 (the subchart root) appears third!
    f << "sp 1 0 1 3 4\n";
    // Skeleton split 0 appears last!
    f << "sp 0 -1 0 1 2\n";
  }

  SplitResult split_res;
  split_res.subcharts = {
      SubchartInfo{.id = 1, .parent_id = 0, .depth = 1, .count = 1},
  };
  split_res.skeleton_split_ids = {0};

  AssignmentResult assign = StreamAndAssignShards(test_file, split_res, nullptr);
  CHECK(assign.error.empty());
  // Because 3 appeared before 1, and leaf appeared before 3,
  // Pass 1 resolved split 1 and seeded it into set;
  // Pass 2 resolved split 3 and inserted it into set;
  // Pass 3 resolved leaf 100!
  CHECK(assign.unassigned_rows == 0);
  CHECK(assign.shards[0].assigned_leaves == 1);
  CHECK(assign.shards[0].assigned_splits == 2);  // 1 and 3
  CHECK(assign.skeleton_splits == 1);           // 0
  CHECK(assign.is_exact_match);

  std::remove(test_file);
  printf("  Out-of-order row assignment multi-pass tests PASSED.\n");
}

void TestDuplicateSplitRows() {
  printf("Testing duplicate split row handling and disjoint sets...\n");
  const char *test_file = "/tmp/test_chart_dup_splits.rows";
  {
    std::ofstream f(test_file);
    f << "sp 0 -1 0 1 2\n";
    f << "sp 1 0 1 10 11\n";
    f << "sp 2 0 1 20 21\n";
    // Duplicate split node 10 appears under parent 1, then under parent 2
    f << "sp 10 1 2 100 101\n";
    f << "ce 100 10 3 0 0.05 1 2 3\n";
    f << "ce 101 10 3 0 0.05 1 2 3\n";
    f << "sp 10 2 2 100 101\n";
    f << "ce 102 10 3 0 0.05 1 2 3\n";
    f << "ce 103 10 3 0 0.05 1 2 3\n";
    f << "ce 20 2 2 0 0.05 1 2 3\n";
  }

  SplitResult split_res;
  split_res.subcharts = {
      SubchartInfo{.id = 1, .parent_id = 0, .depth = 1, .count = 4},
      SubchartInfo{.id = 2, .parent_id = 0, .depth = 1, .count = 1},
  };
  split_res.skeleton_split_ids = {0};
  split_res.duplicate_split_ids = {0x10};

  AssignmentResult assign = StreamAndAssignShards(test_file, split_res, nullptr);
  CHECK(assign.error.empty());
  CHECK(assign.unassigned_rows == 0);
  CHECK(assign.duplicate_rows_dropped == 1);
  CHECK(assign.shards[0].assigned_leaves == 4);
  CHECK(assign.shards[1].assigned_leaves == 1);
  CHECK(assign.is_exact_match);

  std::remove(test_file);
  printf("  Duplicate split row handling tests PASSED.\n");
}

void TestSkeletonSplitsAndGeometryPropagation() {
  printf("Testing skeleton split collection and geometry propagation...\n");
  const char *test_file = "/tmp/test_chart_skeleton.rows";
  {
    std::ofstream f(test_file);
    // Root 0 splits view (chart 0) into 1, 2, 3, 4
    f << "sv 0 -1 0 1 2 3 4\n";
    // Node 1 splits Cayley box along widest axis into 10 and 11
    f << "sp 1 0 1 10 11\n";
    // Leaves under 10
    f << "ce 100 10 2 0 0.05 1 2 3\n";
    f << "ce 101 10 2 0 0.05 1 2 3\n";
    // Leaves under 11
    f << "ce 110 11 2 0 0.05 1 2 3\n";
    // Leaves under 2, 3, 4
    f << "ce 20 2 1 0 0.05 1 2 3\n";
    f << "ce 30 3 1 0 0.05 1 2 3\n";
    f << "ce 40 4 1 0 0.05 1 2 3\n";
  }

  SplitResult split_res;
  split_res.subcharts = {
      SubchartInfo{.id = 0x10, .parent_id = 1, .depth = 2, .count = 2},
      SubchartInfo{.id = 0x11, .parent_id = 1, .depth = 2, .count = 1},
      SubchartInfo{.id = 2, .parent_id = 0, .depth = 1, .count = 1},
      SubchartInfo{.id = 3, .parent_id = 0, .depth = 1, .count = 1},
      SubchartInfo{.id = 4, .parent_id = 0, .depth = 1, .count = 1},
  };
  split_res.skeleton_split_ids = {0, 1};

  auto skeleton_splits = CollectSkeletonSplits(test_file, split_res.skeleton_split_ids);
  CHECK(skeleton_splits.size() == 2);
  CHECK(skeleton_splits.contains(0));
  CHECK(skeleton_splits.contains(1));
  CHECK(skeleton_splits[0].type == SkeletonSplitNode::VIEW);
  CHECK(skeleton_splits[0].children.size() == 4);
  CHECK(skeleton_splits[1].type == SkeletonSplitNode::BOX);
  CHECK(skeleton_splits[1].children.size() == 2);

  auto geoms = ComputeRootGeometries(0, skeleton_splits, split_res);
  CHECK(geoms.size() == 5);
  CHECK(geoms.contains(0x10));
  CHECK(geoms.contains(0x11));
  CHECK(geoms.contains(2));
  CHECK(geoms.contains(3));
  CHECK(geoms.contains(4));

  // Check geometries for 0x10 and 0x11:
  // Node 1 got tri[0].
  // Node 1 box split along WidestAxis() (for chart 0, radii are {1, 1, 1/3}, widest is axis 0).
  // Left child (10) has rx = 0.5, cx = -0.5.
  // Right child (11) has rx = 0.5, cx = +0.5.
  const auto &g10 = geoms[0x10];
  CHECK(g10.depth == 2);
  CHECK(g10.box_depth == 1);
  CHECK(g10.view_depth == 1);
  CHECK(std::abs(g10.cx - (-0.5)) < 1e-9);
  CHECK(std::abs(g10.rx - 0.5) < 1e-9);

  const auto &g11 = geoms[0x11];
  CHECK(g11.depth == 2);
  CHECK(g11.box_depth == 1);
  CHECK(g11.view_depth == 1);
  CHECK(std::abs(g11.cx - 0.5) < 1e-9);
  CHECK(std::abs(g11.rx - 0.5) < 1e-9);

  std::remove(test_file);
  printf("  Skeleton split collection and geometry propagation tests PASSED.\n");
}

void TestStreamAndWriteShardsAndFaithfulRecreation() {
  printf("Testing shard writing and faithful recreation verification...\n");
  const char *test_file = "/tmp/test_chart_write_shards.rows";
  const char *out_dir = "/tmp/test_subcharts_out";
  std::filesystem::create_directories(out_dir);

  {
    std::ofstream f(test_file);
    // Chart 0: Root 0 splits view into 1, 2, 3, 4
    f << "sv 0 -1 0 1 2 3 4\n";
    // Node 1 splits box into 10 and 11
    f << "sp 1 0 1 10 11\n";
    // Node 2 splits box into 20 and 21
    f << "sp 2 0 1 20 21\n";
    // Skeleton leaves under root 0
    f << "ce 3 0 1 0 0.05 1 2 3\n";
    f << "ce 4 0 1 0 0.05 1 2 3\n";
    // Subchart 10: split node 10 + leaves
    f << "sp 10 1 2 100 101\n";
    f << "ce 100 10 3 0 0.05 1 2 3\n";
    f << "ce 101 10 3 0 0.05 1 2 3\n";
    // Subchart 11: split node 11 + leaves
    f << "sp 11 1 2 110 111\n";
    f << "ce 110 11 3 0 0.05 1 2 3\n";
    f << "ce 111 11 3 0 0.05 1 2 3\n";
    // Subchart 20: split node 20 + leaves
    f << "sp 20 2 2 200 201\n";
    f << "ce 200 20 3 0 0.05 1 2 3\n";
    f << "ce 201 20 3 0 0.05 1 2 3\n";
    // Subchart 21: split node 21 + leaves
    f << "sp 21 2 2 210 211\n";
    f << "ce 210 21 3 0 0.05 1 2 3\n";
    f << "ce 211 21 3 0 0.05 1 2 3\n";
  }

  SplitResult split_res;
  split_res.subcharts = {
      SubchartInfo{.id = 0x10, .parent_id = 1, .depth = 2, .count = 2},
      SubchartInfo{.id = 0x11, .parent_id = 1, .depth = 2, .count = 2},
      SubchartInfo{.id = 0x20, .parent_id = 2, .depth = 2, .count = 2},
      SubchartInfo{.id = 0x21, .parent_id = 2, .depth = 2, .count = 2},
  };
  split_res.skeleton_split_ids = {0, 1, 2};

  auto skeleton_splits = CollectSkeletonSplits(test_file, split_res.skeleton_split_ids);
  auto geoms = ComputeRootGeometries(0, skeleton_splits, split_res);
  CHECK(geoms.size() == 4);

  std::string repl_path = std::string(out_dir) + "/chart0.replacement.rows.log";
  WriteShardsResult wres = StreamAndWriteShards(
      test_file, split_res, geoms, out_dir, repl_path, 0, nullptr);

  CHECK(wres.error.empty());
  CHECK(wres.shards_written == 4);
  CHECK(wres.is_exact_match);
  CHECK(wres.total_leaf_certificates == 10);  // 8 in subcharts + 2 in skeleton
  CHECK(wres.skeleton_leaves_written == 2);
  for (int i = 0; i < 4; i++) {
    CHECK(wres.shard_leaves_written[i] == 2);
  }

  // Run the faithful recreation verification
  VerificationResult vres = VerifyFaithfulRecreation(
      repl_path, wres.subchart_paths, 10, geoms);

  CHECK(vres.ok);
  CHECK(vres.verified_shards == 4);
  CHECK(vres.total_recreated_leaves == 10);
  CHECK(vres.total_skeleton_leaves == 2);
  CHECK(vres.total_subchart_leaves == 8);

  // Clean up test files
  std::remove(test_file);
  std::remove(repl_path.c_str());
  for (const auto &p : wres.subchart_paths) {
    std::remove(p.c_str());
  }
  std::filesystem::remove(out_dir);

  printf("  Shard writing and faithful recreation verification tests PASSED.\n");
}

int main() {
  TestBalancedBinaryTree();
  TestViewTreeQuadSplits();
  TestTwoPhaseCoarseRollup();
  TestSkeletonLeavesPreserved();
  TestLookupShardMTF();
  TestStreamAndAssignShards();
  TestOutOfOrderAssignment();
  TestDuplicateSplitRows();
  TestSkeletonSplitsAndGeometryPropagation();
  TestStreamAndWriteShardsAndFaithfulRecreation();

  printf("\nAll split-chart, sharding, and recreation tests PASSED successfully!\n");
  return 0;
}


