// split-chart_test.cc: Rigorous tests for split-chart tree partitioning logic.

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "split-chart.h"

#define CHECK(expr)                                                        \
  do {                                                                     \
    if (!(expr)) {                                                         \
      fprintf(stderr, "FAILED at %s:%d: %s\n", __FILE__, __LINE__, #expr); \
      abort();                                                             \
    }                                                                      \
  } while (0)

static void TestBalancedBinaryTree() {
  printf("Testing balanced binary tree partitioning...\n");

  // Complete binary tree of depth 6:
  // Root = 1
  // Internal nodes: 1 .. 63
  // Leaves: 64 .. 127 (64 leaves)
  std::unordered_map<int64_t, InternalNode> node_map;
  for (int64_t i = 1; i <= 63; i++) {
    int64_t parent = (i == 1) ? -1 : (i / 2);
    int depth = 0;
    for (int64_t p = i; p > 1; p /= 2) depth++;
    node_map[i] = InternalNode{
        .parent_id = parent,
        .count = 0,
        .depth = depth,
        .is_split_row = true,
    };
  }

  // Each of nodes 32..63 has 2 direct leaves
  int64_t total_leaves = 0;
  for (int64_t i = 32; i <= 63; i++) {
    node_map[i].count += 2;
    total_leaves += 2;
  }
  CHECK(total_leaves == 64);

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

  // Root = 0
  // 4 children: 1, 2, 3, 4 (depth 1)
  // Each child has 4 children: 5..20 (depth 2)
  // Total 16 leaves at depth 2, each with 10 leaf certificates
  std::unordered_map<int64_t, InternalNode> node_map;
  node_map[0] = InternalNode{.parent_id = -1, .count = 0, .depth = 0, .is_split_row = true};
  for (int64_t i = 1; i <= 4; i++) {
    node_map[i] = InternalNode{.parent_id = 0, .count = 0, .depth = 1, .is_split_row = true};
  }
  int64_t total_leaves = 0;
  for (int64_t i = 5; i <= 20; i++) {
    int64_t p = 1 + (i - 5) / 4;
    node_map[i] = InternalNode{.parent_id = p, .count = 10, .depth = 2, .is_split_row = true};
    total_leaves += 10;
  }
  CHECK(total_leaves == 160);

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

  // Build a deep tree with 1,000 internal nodes
  // Let max_nodes = 50, so coarse rollup must trigger
  std::unordered_map<int64_t, InternalNode> node_map;
  int64_t total_leaves = 0;

  for (int64_t i = 1; i <= 1023; i++) {
    int64_t parent = (i == 1) ? -1 : (i / 2);
    node_map[i] = InternalNode{
        .parent_id = parent,
        .count = 0,
        .depth = 1,
        .is_split_row = true,
    };
  }

  // The 512 leaves of the full binary tree have count = 1
  for (int64_t i = 512; i <= 1023; i++) {
    node_map[i].count = 1;
    total_leaves += 1;
  }

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

  // Node 0 splits into 1 and 2
  // Node 0 has 5 direct leaf certificates!
  // Node 1 has 50 leaves, Node 2 has 50 leaves
  std::unordered_map<int64_t, InternalNode> node_map;
  node_map[0] = InternalNode{.parent_id = -1, .count = 5, .depth = 0, .is_split_row = true};
  node_map[1] = InternalNode{.parent_id = 0, .count = 50, .depth = 1, .is_split_row = true};
  node_map[2] = InternalNode{.parent_id = 0, .count = 50, .depth = 1, .is_split_row = true};
  int64_t total_leaves = 105;

  // Split into T = 2 subcharts (should choose nodes 1 and 2)
  SplitResult res = ComputeBalancedSplit(node_map, total_leaves, 2, 100);
  CHECK(res.subcharts.size() == 2);
  CHECK(res.sum_subchart_leaves == 100);
  CHECK(res.skeleton_leaves == 5);
  CHECK(res.skeleton_splits == 1);
  CHECK(res.sum_subchart_leaves + res.skeleton_leaves == total_leaves);

  printf("  Preservation of skeleton leaves tests PASSED.\n");
}

int main() {
  TestBalancedBinaryTree();
  TestViewTreeQuadSplits();
  TestTwoPhaseCoarseRollup();
  TestSkeletonLeavesPreserved();

  printf("\nAll split-chart tests PASSED successfully!\n");
  return 0;
}
