#ifndef _NOPERT229_SPLIT_CHART_H
#define _NOPERT229_SPLIT_CHART_H

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "status-bar.h"

struct InternalNode {
  int64_t parent_id = -1;
  int64_t count = 0;  // Subtree leaf count rolled up into this node
  int depth = 0;
  bool is_split_row = false;
};

struct SubchartInfo {
  int64_t id = 0;
  int64_t parent_id = -1;
  int depth = 0;
  int64_t count = 0;
};

struct SplitStats {
  int64_t total_leaves = 0;
  int64_t min_count = 0;
  int64_t max_count = 0;
  double mean_count = 0.0;
  double median_count = 0.0;
  double std_dev = 0.0;
  double cv = 0.0;
  double ratio = 1.0;
  int min_depth = 0;
  int max_depth = 0;
  double avg_depth = 0.0;
};

struct SplitResult {
  std::vector<SubchartInfo> subcharts;
  int64_t total_leaf_rows = 0;
  int64_t sum_subchart_leaves = 0;
  int64_t skeleton_leaves = 0;
  int64_t skeleton_splits = 0;
  int coarse_waves = 0;
  int64_t huffman_steps = 0;
  SplitStats stats;
};

inline SplitStats ComputeStats(const std::vector<SubchartInfo> &subcharts, int64_t total_leaves) {
  SplitStats stats;
  stats.total_leaves = total_leaves;
  if (subcharts.empty()) return stats;

  stats.min_count = subcharts.front().count;
  stats.max_count = subcharts.front().count;
  stats.min_depth = subcharts.front().depth;
  stats.max_depth = subcharts.front().depth;

  double depth_sum = 0.0;
  std::vector<int64_t> counts;
  counts.reserve(subcharts.size());

  for (const auto &s : subcharts) {
    stats.min_count = std::min(stats.min_count, s.count);
    stats.max_count = std::max(stats.max_count, s.count);
    stats.min_depth = std::min(stats.min_depth, s.depth);
    stats.max_depth = std::max(stats.max_depth, s.depth);
    depth_sum += s.depth;
    counts.push_back(s.count);
  }

  stats.mean_count = (double)total_leaves / subcharts.size();
  stats.avg_depth = depth_sum / subcharts.size();
  if (stats.min_count > 0) {
    stats.ratio = (double)stats.max_count / (double)stats.min_count;
  }

  std::sort(counts.begin(), counts.end());
  if (counts.size() % 2 == 1) {
    stats.median_count = counts[counts.size() / 2];
  } else {
    stats.median_count = 0.5 * (counts[counts.size() / 2 - 1] + counts[counts.size() / 2]);
  }

  double var_sum = 0.0;
  for (int64_t c : counts) {
    double diff = c - stats.mean_count;
    var_sum += diff * diff;
  }
  stats.std_dev = std::sqrt(var_sum / subcharts.size());
  if (stats.mean_count > 0.0) {
    stats.cv = (stats.std_dev / stats.mean_count) * 100.0;
  }

  return stats;
}

inline SplitResult ComputeBalancedSplit(
    std::unordered_map<int64_t, InternalNode> node_map,
    int64_t total_leaf_rows,
    int target_subcharts,
    size_t max_nodes,
    StatusBar *status = nullptr) {

  SplitResult result;
  result.total_leaf_rows = total_leaf_rows;

  if (total_leaf_rows == 0 || node_map.empty()) {
    return result;
  }

  // Phase 1: Coarse rollup
  // Repeatedly roll up leaf nodes of node_map into their parents until
  // node_map.size() <= max_nodes.
  while (node_map.size() > max_nodes && node_map.size() > (size_t)(2 * target_subcharts)) {
    result.coarse_waves++;
    std::unordered_set<int64_t> internal_ids;
    internal_ids.reserve(node_map.size());

    for (const auto &[id, node] : node_map) {
      if (node.parent_id != -1 && node_map.count(node.parent_id)) {
        internal_ids.insert(node.parent_id);
      }
    }

    std::vector<int64_t> leaves_to_rollup;
    leaves_to_rollup.reserve(node_map.size() - internal_ids.size());

    for (const auto &[id, node] : node_map) {
      if (internal_ids.count(id) == 0 && node.parent_id != -1 && node_map.count(node.parent_id)) {
        leaves_to_rollup.push_back(id);
      }
    }

    if (leaves_to_rollup.empty()) {
      break;
    }

    // Guard against overshooting below target_subcharts
    if (node_map.size() - leaves_to_rollup.size() < (size_t)target_subcharts) {
      break;
    }

    for (int64_t id : leaves_to_rollup) {
      auto it = node_map.find(id);
      if (it != node_map.end()) {
        auto parent_it = node_map.find(it->second.parent_id);
        if (parent_it != node_map.end()) {
          parent_it->second.count += it->second.count;
        }
        node_map.erase(it);
      }
    }

    if (status) {
      status->Status("Phase 1 coarse rollup wave {}: {:L} nodes remaining in map...",
                     result.coarse_waves, node_map.size());
    }
  }

  // Phase 2: Prioritized Huffman-style subtree rollup down to T subcharts.
  std::unordered_map<int64_t, std::vector<int64_t>> children;
  children.reserve(node_map.size());

  for (const auto &[id, node] : node_map) {
    if (node.parent_id != -1 && node_map.count(node.parent_id)) {
      children[node.parent_id].push_back(id);
    }
  }

  // Count current leaves in node_map
  size_t leaf_count = 0;
  for (const auto &[id, node] : node_map) {
    auto it = children.find(id);
    if (it == children.end() || it->second.empty()) {
      leaf_count++;
    }
  }

  struct ReadyParent {
    int64_t combined_count;
    int64_t parent_id;
    bool operator>(const ReadyParent &other) const {
      if (combined_count != other.combined_count) {
        return combined_count > other.combined_count;
      }
      return parent_id > other.parent_id;
    }
  };

  std::unordered_map<int64_t, size_t> leaf_children_count;
  leaf_children_count.reserve(node_map.size());

  for (const auto &[id, node] : node_map) {
    auto it = children.find(id);
    if (it == children.end() || it->second.empty()) {
      if (node.parent_id != -1 && node_map.count(node.parent_id)) {
        leaf_children_count[node.parent_id]++;
      }
    }
  }

  std::priority_queue<ReadyParent, std::vector<ReadyParent>, std::greater<ReadyParent>> pq;

  auto CheckAndEnqueue = [&](int64_t p_id) {
    auto ch_it = children.find(p_id);
    if (ch_it == children.end() || ch_it->second.empty()) return;
    if (leaf_children_count[p_id] == ch_it->second.size()) {
      int64_t sum_count = node_map[p_id].count;
      for (int64_t c_id : ch_it->second) {
        sum_count += node_map[c_id].count;
      }
      pq.push(ReadyParent{
          .combined_count = sum_count,
          .parent_id = p_id,
      });
    }
  };

  for (const auto &[p_id, ch_list] : children) {
    if (!ch_list.empty() && leaf_children_count[p_id] == ch_list.size()) {
      CheckAndEnqueue(p_id);
    }
  }

  while (leaf_count > (size_t)target_subcharts && !pq.empty()) {
    auto top = pq.top();
    pq.pop();
    int64_t p_id = top.parent_id;

    auto p_it = node_map.find(p_id);
    if (p_it == node_map.end()) continue;

    auto ch_it = children.find(p_id);
    if (ch_it == children.end() || ch_it->second.empty()) continue;
    if (leaf_children_count[p_id] != ch_it->second.size()) continue;

    size_t k = ch_it->second.size();
    // Check if stopping here is closer to target than collapsing
    if (leaf_count - (k - 1) < (size_t)target_subcharts) {
      size_t dist_before = leaf_count - target_subcharts;
      size_t dist_after = target_subcharts - (leaf_count - (k - 1));
      if (dist_before <= dist_after) {
        break;
      }
    }

    // Collapse parent: merge all children into p_id
    for (int64_t c_id : ch_it->second) {
      auto c_it = node_map.find(c_id);
      if (c_it != node_map.end()) {
        p_it->second.count += c_it->second.count;
        node_map.erase(c_it);
      }
    }
    ch_it->second.clear();
    leaf_count -= (k - 1);
    result.huffman_steps++;

    // p_id is now a leaf!
    int64_t gp_id = p_it->second.parent_id;
    if (gp_id != -1 && node_map.count(gp_id)) {
      leaf_children_count[gp_id]++;
      CheckAndEnqueue(gp_id);
    }

    if (status && (result.huffman_steps % 1000 == 0)) {
      status->Status("Phase 2 prioritized rollup: {:L} subcharts remaining (target: {})...",
                     leaf_count, target_subcharts);
    }
  }

  // Collect final subchart roots and skeleton leaves
  result.subcharts.reserve(leaf_count);

  for (const auto &[id, node] : node_map) {
    auto it = children.find(id);
    if (it == children.end() || it->second.empty()) {
      result.subcharts.push_back(SubchartInfo{
          .id = id,
          .parent_id = node.parent_id,
          .depth = node.depth,
          .count = node.count,
      });
      result.sum_subchart_leaves += node.count;
    } else {
      result.skeleton_splits++;
      result.skeleton_leaves += node.count;
    }
  }

  std::sort(result.subcharts.begin(), result.subcharts.end(),
            [](const SubchartInfo &a, const SubchartInfo &b) {
              if (a.count != b.count) return a.count > b.count;
              return a.id < b.id;
            });

  result.stats = ComputeStats(result.subcharts, result.sum_subchart_leaves);
  return result;
}

#endif  // _NOPERT229_SPLIT_CHART_H
