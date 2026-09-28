#ifndef _NOPERT229_SPLIT_CHART_H
#define _NOPERT229_SPLIT_CHART_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <queue>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

#include "chart229.h"
#include "periodically.h"
#include "status-bar.h"
#include "timer.h"

struct InternalNode {
  int64_t parent_id = -1;
  int64_t count = 0;  // Subtree leaf count rolled up into this node
  int depth = -1;
  int num_children = 0;
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
  std::unordered_set<int64_t> skeleton_split_ids;
  std::unordered_set<int64_t> duplicate_split_ids;
  int64_t duplicate_rows_dropped = 0;
  int64_t total_leaf_rows = 0;
  int64_t sum_subchart_leaves = 0;
  int64_t skeleton_leaves = 0;
  int64_t skeleton_splits = 0;
  int coarse_waves = 0;
  int64_t huffman_steps = 0;
  SplitStats stats;
};

struct ShardAssignmentStats {
  int64_t root_id = 0;
  int64_t parent_id = -1;
  int depth = 0;
  int64_t expected_leaves = 0;
  int64_t assigned_leaves = 0;
  int64_t assigned_splits = 0;
};

struct AssignmentResult {
  std::vector<ShardAssignmentStats> shards;
  int64_t skeleton_splits = 0;
  int64_t skeleton_leaves = 0;
  int64_t total_lines = 0;
  int64_t total_leaves = 0;
  int64_t total_splits = 0;
  int64_t duplicate_rows_dropped = 0;
  int64_t unassigned_rows = 0;
  int passes_needed = 1;
  std::vector<int64_t> mtf_hits;
  int64_t total_mtf_lookups = 0;
  double pos0_hit_rate = 0.0;
  double avg_mtf_depth = 0.0;
  bool is_exact_match = false;
  std::string error;
};

inline std::string FormatBytes(int64_t bytes) {
  if (bytes >= 1024LL * 1024 * 1024 * 1024) {
    return std::format("{:.2f} TB", bytes / (1024.0 * 1024.0 * 1024.0 * 1024.0));
  } else if (bytes >= 1024LL * 1024 * 1024) {
    return std::format("{:.2f} GB", bytes / (1024.0 * 1024.0 * 1024.0));
  } else if (bytes >= 1024LL * 1024) {
    return std::format("{:.2f} MB", bytes / (1024.0 * 1024.0));
  } else if (bytes >= 1024) {
    return std::format("{:.2f} KB", bytes / 1024.0);
  } else {
    return std::format("{} B", bytes);
  }
}

// Fast buffered chart reader iterating over each line in chart_path.
template <typename Fn>
inline bool ForEachChartLine(const std::string &chart_path, Fn &&fn, StatusBar *status, const char *status_prefix) {
  FILE *in_file = std::fopen(chart_path.c_str(), "rb");
  if (!in_file) {
    if (status) status->Print("Error opening '{}': {}\n", chart_path, std::strerror(errno));
    return false;
  }

  int64_t total_bytes = -1;
  if (fseeko(in_file, 0, SEEK_END) == 0) {
    total_bytes = ftello(in_file);
    fseeko(in_file, 0, SEEK_SET);
  }

  static constexpr size_t CHUNK_SIZE = 1024 * 1024;  // 1 MB
  std::vector<char> in_buf(CHUNK_SIZE);
  std::string remainder;
  int64_t bytes_in = 0;
  int64_t lines_read = 0;

  Periodically progress_per(0.25);
  Timer timer;

  while (true) {
    size_t n = std::fread(in_buf.data(), 1, in_buf.size(), in_file);
    if (n == 0) {
      if (std::ferror(in_file)) {
        if (status) status->Print("Error reading input file: {}\n", std::strerror(errno));
        std::fclose(in_file);
        return false;
      }
      break;
    }
    bytes_in += n;

    const char *ptr = in_buf.data();
    const char *end = ptr + n;
    const char *line_start = ptr;

    if (!remainder.empty()) {
      const char *nl = static_cast<const char *>(std::memchr(ptr, '\n', n));
      if (nl != nullptr) {
        remainder.append(ptr, nl - ptr);
        if (!remainder.empty() && remainder.back() == '\r') remainder.pop_back();
        lines_read++;
        fn(std::string_view(remainder));
        remainder.clear();
        line_start = nl + 1;
      } else {
        remainder.append(ptr, n);
        line_start = end;
      }
    }

    while (line_start < end) {
      const char *nl = static_cast<const char *>(std::memchr(line_start, '\n', end - line_start));
      if (nl != nullptr) {
        std::string_view line(line_start, nl - line_start);
        if (!line.empty() && line.back() == '\r') line.remove_suffix(1);
        lines_read++;
        fn(line);
        line_start = nl + 1;
      } else {
        remainder.assign(line_start, end - line_start);
        break;
      }
    }

    if (status && progress_per.ShouldRun()) {
      double elapsed = timer.Seconds();
      double mb_s = (bytes_in / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);
      if (total_bytes > 0) {
        status->Progress(bytes_in, total_bytes, "{}: lines: {:L} | {:.1f} MB/s",
                         status_prefix, lines_read, mb_s);
      } else {
        status->Status("{}: {} | lines: {:L} | {:.1f} MB/s",
                       status_prefix, FormatBytes(bytes_in), lines_read, mb_s);
      }
    }
  }

  if (!remainder.empty()) {
    if (remainder.back() == '\r') remainder.pop_back();
    lines_read++;
    fn(std::string_view(remainder));
    remainder.clear();
  }

  std::fclose(in_file);
  return true;
}

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

  // Phase 1: Coarse rollup using child-count wave peeling (O(N), minimal memory)
  std::vector<int64_t> current_leaves;
  current_leaves.reserve(std::min(node_map.size() / 2, (size_t)10000000));
  for (const auto &[id, node] : node_map) {
    if (node.num_children == 0 && node.parent_id != -1 && node_map.count(node.parent_id)) {
      current_leaves.push_back(id);
    }
  }

  while (!current_leaves.empty() &&
         node_map.size() > max_nodes &&
         node_map.size() > (size_t)(2 * target_subcharts)) {
    result.coarse_waves++;

    // Guard against overshooting below target_subcharts
    if (node_map.size() - current_leaves.size() < (size_t)target_subcharts) {
      break;
    }

    std::vector<int64_t> next_leaves;
    for (int64_t id : current_leaves) {
      auto it = node_map.find(id);
      if (it != node_map.end()) {
        auto parent_it = node_map.find(it->second.parent_id);
        if (parent_it != node_map.end()) {
          parent_it->second.count += it->second.count;
          parent_it->second.num_children--;
          if (parent_it->second.num_children == 0 &&
              parent_it->second.parent_id != -1 &&
              node_map.count(parent_it->second.parent_id)) {
            next_leaves.push_back(parent_it->first);
          }
        }
        node_map.erase(it);
      }
    }
    current_leaves = std::move(next_leaves);

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

  // Collect final subchart roots and skeleton splits/leaves
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
      result.skeleton_split_ids.insert(id);
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

// Move-To-Front query over shard sets.
// Returns the shard index (0..T-1), or -1 if parent_id is not in any shard set.
inline int LookupShardMTF(
    int64_t parent_id,
    const std::vector<std::unordered_set<int64_t>> &shard_sets,
    std::vector<int> &mtf_order,
    std::vector<int64_t> &mtf_hits) {
  for (size_t pos = 0; pos < mtf_order.size(); pos++) {
    int s = mtf_order[pos];
    if (shard_sets[s].contains(parent_id)) {
      mtf_hits[pos]++;
      if (pos > 0) {
        int hit = mtf_order[pos];
        for (size_t j = pos; j > 0; j--) {
          mtf_order[j] = mtf_order[j - 1];
        }
        mtf_order[0] = hit;
      }
      return s;
    }
  }
  return -1;
}

// Second pass: streams the chart file and assigns every row to its disjoint shard
// or to the main skeleton using a Move-to-Front list of T unordered_sets.
// Multi-pass capable: repeats streaming until all out-of-order nodes are resolved.
inline AssignmentResult StreamAndAssignShards(
    const std::string &chart_path,
    const SplitResult &split_res,
    StatusBar *status = nullptr) {

  AssignmentResult res;
  int T = split_res.subcharts.size();
  if (T == 0) {
    res.error = "No subcharts provided for assignment";
    return res;
  }

  std::unordered_map<int64_t, int> root_to_shard;
  root_to_shard.reserve(T);

  std::vector<std::unordered_set<int64_t>> shard_sets(T);
  res.shards.resize(T);
  for (int i = 0; i < T; i++) {
    const auto &sc = split_res.subcharts[i];
    root_to_shard[sc.id] = i;
    shard_sets[i].insert(sc.id);

    res.shards[i].root_id = sc.id;
    res.shards[i].parent_id = sc.parent_id;
    res.shards[i].depth = sc.depth;
    res.shards[i].expected_leaves = sc.count;
  }

  std::unordered_set<int64_t> skeleton_ids = split_res.skeleton_split_ids;
  std::vector<int> mtf_order(T);
  for (int i = 0; i < T; i++) mtf_order[i] = i;
  res.mtf_hits.assign(T, 0);

  int max_passes = 10;
  for (int pass = 1; pass <= max_passes; pass++) {
    res.passes_needed = pass;
    res.total_lines = 0;
    res.total_leaves = 0;
    res.total_splits = 0;
    res.skeleton_splits = 0;
    res.skeleton_leaves = 0;
    res.duplicate_rows_dropped = 0;
    res.unassigned_rows = 0;
    for (int i = 0; i < T; i++) {
      res.shards[i].assigned_leaves = 0;
      res.shards[i].assigned_splits = 0;
    }
    std::unordered_set<int64_t> seen_duplicate_ids;

    std::string prefix = (pass == 1)
        ? "Assigning shards"
        : std::format("Pass {} resolving out-of-order rows", pass);

    bool ok = ForEachChartLine(
        chart_path,
        [&](std::string_view line) {
          res.total_lines++;
          Chart229::Row row = Chart229::Parse(line);
          if (std::holds_alternative<Chart229::ParseError>(row) ||
              std::holds_alternative<Chart229::EmptyRow>(row) ||
              std::holds_alternative<Chart229::CommentRow>(row)) {
            return;
          }

          std::visit([&](const auto &r) {
            using RowType = std::decay_t<decltype(r)>;
            if constexpr (std::is_same_v<RowType, Chart229::SplitRow> ||
                          std::is_same_v<RowType, Chart229::SplitOriginRow> ||
                          std::is_same_v<RowType, Chart229::SplitViewRow>) {
              res.total_splits++;

              // 1. Drop duplicate split rows (guarantees disjoint shards)
              if (split_res.duplicate_split_ids.contains(r.id)) {
                if (seen_duplicate_ids.contains(r.id)) {
                  res.duplicate_rows_dropped++;
                  return;
                }
                seen_duplicate_ids.insert(r.id);
              }

              // 2. Is r.id one of the subchart roots?
              auto root_it = root_to_shard.find(r.id);
              if (root_it != root_to_shard.end()) {
                int s = root_it->second;
                res.shards[s].assigned_splits++;
                return;
              }

              // 3. Is r.id in the main chart skeleton?
              if (skeleton_ids.contains(r.id)) {
                res.skeleton_splits++;
                return;
              }

              // 4. Query parent in MTF shard sets
              int s = LookupShardMTF(r.parent_id, shard_sets, mtf_order, res.mtf_hits);
              if (s >= 0) {
                res.shards[s].assigned_splits++;
                shard_sets[s].insert(r.id);
              } else if (skeleton_ids.contains(r.parent_id) || r.parent_id == -1) {
                res.skeleton_splits++;
                skeleton_ids.insert(r.id);
              } else {
                res.unassigned_rows++;
              }
            } else if constexpr (std::is_same_v<RowType, Chart229::CertRow> ||
                                 std::is_same_v<RowType, Chart229::MixedCertRow> ||
                                 std::is_same_v<RowType, Chart229::PruneRadiusRow> ||
                                 std::is_same_v<RowType, Chart229::PruneFundamentalRow> ||
                                 std::is_same_v<RowType, Chart229::TubeRow> ||
                                 std::is_same_v<RowType, Chart229::DifficultRow>) {
              if (root_to_shard.contains(r.id)) {
                std::fprintf(stderr,
                             "FATAL: Subchart root 0x%lx (%ld) is a leaf row! Aborting.\n",
                             r.id, r.id);
                std::abort();
              }
              res.total_leaves++;
              int s = LookupShardMTF(r.parent_id, shard_sets, mtf_order, res.mtf_hits);
              if (s >= 0) {
                res.shards[s].assigned_leaves++;
              } else if (skeleton_ids.contains(r.parent_id) || r.parent_id == -1) {
                res.skeleton_leaves++;
              } else {
                res.unassigned_rows++;
              }
            }
          }, row);
        },
        status, prefix.c_str());

    if (!ok) {
      res.error = "Error streaming file during shard assignment";
      return res;
    }

    if (res.unassigned_rows == 0) {
      break;
    }
    if (status) {
      status->Print("Pass {} finished with {:L} unassigned rows; repeating...\n",
                    pass, res.unassigned_rows);
    }
  }

  // Compute MTF stats
  for (int64_t h : res.mtf_hits) {
    res.total_mtf_lookups += h;
  }
  if (res.total_mtf_lookups > 0) {
    res.pos0_hit_rate = (double)res.mtf_hits[0] / res.total_mtf_lookups * 100.0;
    double weighted_depth = 0;
    for (size_t pos = 0; pos < res.mtf_hits.size(); pos++) {
      weighted_depth += (double)pos * res.mtf_hits[pos];
    }
    res.avg_mtf_depth = weighted_depth / res.total_mtf_lookups;
  }

  // Verification checks
  res.is_exact_match = (res.unassigned_rows == 0);
  for (int i = 0; i < T; i++) {
    if (res.shards[i].assigned_leaves != res.shards[i].expected_leaves) {
      res.is_exact_match = false;
    }
  }

  return res;
}

#endif  // _NOPERT229_SPLIT_CHART_H
