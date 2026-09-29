// split-chart.cc: Analyzes and computes a balanced split of a chart file
// into T subcharts using streaming and a two-phase rollup (coarse rollup
// followed by Huffman-style prioritized subtree merging).
//
// Then, performs a second streaming assignment pass using a Move-To-Front (MTF)
// list of T hash sets to verify that every row is disjointly and completely
// assigned to its subchart or to the main skeleton, testing the cleave
// without writing any files out yet.

#include <malloc.h>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <format>
#include <fstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

#include "chart229.h"
#include "periodically.h"
#include "split-chart.h"
#include "status-bar.h"
#include "timer.h"

int main(int argc, char **argv) {
  int target_subcharts = 64;
  size_t max_nodes = 131072;  // 128k
  std::string chart_path;
  std::string output_roots_path;
  bool show_all = false;
  bool skip_assignment_pass = false;
  bool write_shards = false;
  std::string out_dir;
  std::string replacement_chart_path;
  int chart_override = -1;

  for (int i = 1; i < argc; i++) {
    std::string_view arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      std::fprintf(stderr,
                   "Usage: %s [options] <chart.rows.log> [target_subcharts]\n\n"
                   "Computes a balanced split of a chart into T subcharts and\n"
                   "verifies or executes the disjoint cleave across all rows.\n\n"
                   "Options:\n"
                   "  -T, --target <N>     Target number of subcharts (default: 64)\n"
                   "  -N, --max_nodes <N>  Threshold for Huffman prioritized rollup (default: 131072)\n"
                   "  -o, --output <file>  Optional path to write list of chosen subchart root IDs\n"
                   "  --write_shards       Emit .subchart files and replacement skeleton chart\n"
                   "  --out_dir <dir>      Output directory for .subchart files (default: chart directory)\n"
                   "  --replacement <file> Output path for replacement chart (default: <dir>/<chart>.replacement.rows.log)\n"
                   "  --chart <N>          Explicit chart number (0..3, auto-detected from filename if omitted)\n"
                   "  --show_all           Print all subcharts in table (not just top/bottom)\n"
                   "  --skip_assignment    Skip second-pass shard assignment verification\n",
                   argv[0]);
      return 0;
    } else if ((arg == "-T" || arg == "--target") && i + 1 < argc) {
      target_subcharts = std::atoi(argv[++i]);
    } else if ((arg == "-N" || arg == "--max_nodes") && i + 1 < argc) {
      max_nodes = std::strtoull(argv[++i], nullptr, 10);
    } else if ((arg == "-o" || arg == "--output") && i + 1 < argc) {
      output_roots_path = argv[++i];
    } else if (arg == "--write_shards") {
      write_shards = true;
    } else if ((arg == "--out_dir") && i + 1 < argc) {
      out_dir = argv[++i];
    } else if ((arg == "--replacement") && i + 1 < argc) {
      replacement_chart_path = argv[++i];
    } else if ((arg == "--chart") && i + 1 < argc) {
      chart_override = std::atoi(argv[++i]);
    } else if (arg == "--show_all") {
      show_all = true;
    } else if (arg == "--skip_assignment") {
      skip_assignment_pass = true;
    } else if (chart_path.empty()) {
      chart_path = argv[i];
    } else {
      int t = std::atoi(argv[i]);
      if (t > 0) {
        target_subcharts = t;
      } else {
        std::fprintf(stderr, "Unknown argument: %s\n", argv[i]);
        return 1;
      }
    }
  }

  if (chart_path.empty()) {
    std::fprintf(stderr, "Error: chart file argument required. Use --help for usage.\n");
    return 1;
  }

  if (target_subcharts < 1) {
    std::fprintf(stderr, "Error: target subcharts T must be >= 1 (got %d)\n", target_subcharts);
    return 1;
  }

  StatusBar status(1);
  Timer pass1_timer;

  std::unordered_map<int64_t, InternalNode> node_map;
  std::unordered_set<int64_t> duplicate_split_ids;
  int64_t total_lines = 0;
  int64_t total_leaf_rows = 0;
  int64_t total_split_rows = 0;
  int64_t parse_errors = 0;
  int64_t duplicate_rows_dropped = 0;

  bool read_ok = ForEachChartLine(
      chart_path,
      [&](std::string_view line) {
        total_lines++;
        Chart229::Row row = Chart229::Parse(line);
        if (std::holds_alternative<Chart229::ParseError>(row)) {
          parse_errors++;
          return;
        }

        std::visit([&](const auto &r) {
          using T = std::decay_t<decltype(r)>;
          if constexpr (std::is_same_v<T, Chart229::SplitRow> ||
                        std::is_same_v<T, Chart229::SplitOriginRow> ||
                        std::is_same_v<T, Chart229::SplitViewRow>) {
            total_split_rows++;
            auto &node = node_map[r.id];
            if (node.depth != -1) {
              std::fprintf(stderr, "\nDUPLICATE SPLIT ROW ID: 0x%lx (depth was %d, now %d; parent was 0x%lx, now 0x%lx)\n",
                           r.id, node.depth, r.depth, node.parent_id, r.parent_id);
              duplicate_split_ids.insert(r.id);
              duplicate_rows_dropped++;
              return;
            }
            node.parent_id = r.parent_id;
            node.depth = r.depth;
            if (r.parent_id != -1) {
              node_map[r.parent_id].num_children++;
            }
          } else if constexpr (std::is_same_v<T, Chart229::CertRow> ||
                               std::is_same_v<T, Chart229::MixedCertRow> ||
                               std::is_same_v<T, Chart229::PruneRadiusRow> ||
                               std::is_same_v<T, Chart229::PruneFundamentalRow> ||
                               std::is_same_v<T, Chart229::TubeRow> ||
                               std::is_same_v<T, Chart229::DifficultRow>) {
            total_leaf_rows++;
            if (r.parent_id != -1) {
              node_map[r.parent_id].count++;
            }
          }
        }, row);
      },
      &status, "Pass 1: Streaming chart");

  if (!read_ok) {
    status.Print("Error reading input chart file.\n");
    return 1;
  }

  status.Print("Pass 1 complete in {:.2f}s: {:L} lines read.\n"
               "  Internal split nodes: {:L}\n"
               "  Leaf certificate/prune rows: {:L}\n"
               "  Initial node map size: {:L}\n",
               pass1_timer.Seconds(), total_lines, total_split_rows, total_leaf_rows,
               node_map.size());

  if (total_leaf_rows == 0) {
    status.Print("Error: chart contains no leaf rows to split.\n");
    return 1;
  }

  SplitResult split_res = ComputeBalancedSplit(
      std::move(node_map), total_leaf_rows, target_subcharts, max_nodes, &status);
  split_res.duplicate_split_ids = std::move(duplicate_split_ids);
  split_res.duplicate_rows_dropped = duplicate_rows_dropped;

  // Free Pass 1 node_map memory and trim heap back to the OS
  node_map.clear();
  malloc_trim(0);

  // Cleanly remove status bar for the Pass 1 summary
  status.Remove();

  int64_t total_accounted = split_res.sum_subchart_leaves + split_res.skeleton_leaves;

  std::printf("\n");
  std::printf("================================================================================\n");
  std::printf("Pass 1: Subtree Rollup Analysis for: %s\n", chart_path.c_str());
  std::printf("================================================================================\n");
  std::printf("Target subcharts (T):       %d\n", target_subcharts);
  std::printf("Actual subcharts:           %zu\n", split_res.subcharts.size());
  std::printf("Total input lines:          %s\n", std::format("{:L}", total_lines).c_str());
  std::printf("Total leaf certificates:    %s\n", std::format("{:L}", total_leaf_rows).c_str());
  std::printf("Leaves in subcharts:        %s (%.2f%%)\n",
              std::format("{:L}", split_res.sum_subchart_leaves).c_str(),
              100.0 * split_res.sum_subchart_leaves / total_leaf_rows);
  std::printf("Leaves in main skeleton:    %s (%.2f%%)\n",
              std::format("{:L}", split_res.skeleton_leaves).c_str(),
              100.0 * split_res.skeleton_leaves / total_leaf_rows);
  std::printf("Main skeleton splits:       %s\n",
              std::format("{:L}", split_res.skeleton_splits).c_str());
  std::printf("Duplicate rows dropped:     %s\n",
              std::format("{:L}", split_res.duplicate_rows_dropped).c_str());
  std::printf("Verification check:         %s (sum: %s)\n",
              total_accounted == total_leaf_rows ? "EXACT MATCH ✓" : "MISMATCH ✗",
              std::format("{:L}", total_accounted).c_str());
  if (split_res.coarse_waves > 0) {
    std::printf("Phase 1 coarse waves:       %d\n", split_res.coarse_waves);
  }
  std::printf("Phase 2 Huffman merges:     %s\n",
              std::format("{:L}", split_res.huffman_steps).c_str());
  if (parse_errors > 0) {
    std::printf("Parse errors encountered:   %s\n", std::format("{:L}", parse_errors).c_str());
  }
  std::printf("\n");
  std::printf("Subchart Size Balance:\n");
  std::printf("  Minimum size:             %s leaves (%.2f%% of total)\n",
              std::format("{:L}", split_res.stats.min_count).c_str(),
              100.0 * split_res.stats.min_count / total_leaf_rows);
  std::printf("  Maximum size:             %s leaves (%.2f%% of total)\n",
              std::format("{:L}", split_res.stats.max_count).c_str(),
              100.0 * split_res.stats.max_count / total_leaf_rows);
  std::printf("  Mean size:                %s leaves\n",
              std::format("{:.1f}", split_res.stats.mean_count).c_str());
  std::printf("  Median size:              %s leaves\n",
              std::format("{:.1f}", split_res.stats.median_count).c_str());
  std::printf("  Std Deviation:            %s (CV: %.1f%%)\n",
              std::format("{:.1f}", split_res.stats.std_dev).c_str(), split_res.stats.cv);
  std::printf("  Max / Min Ratio:          %.2fx\n", split_res.stats.ratio);
  std::printf("\n");
  std::printf("Depth Distribution:\n");
  std::printf("  Min Depth:                %d\n", split_res.stats.min_depth);
  std::printf("  Max Depth:                %d\n", split_res.stats.max_depth);
  std::printf("  Avg Depth:                %.2f\n", split_res.stats.avg_depth);
  std::printf("================================================================================\n");
  if (!output_roots_path.empty()) {
    std::ofstream ofs(output_roots_path);
    if (ofs.is_open()) {
      for (const auto &sc : split_res.subcharts) {
        ofs << std::format("0x{:x} {}\n", sc.id, sc.count);
      }
      std::printf("Subchart roots written to: %s\n", output_roots_path.c_str());
    } else {
      std::fprintf(stderr, "Warning: failed to open '%s' for writing roots.\n",
                   output_roots_path.c_str());
    }
  }

  if (skip_assignment_pass) {
    return 0;
  }

  int chart_num = (chart_override >= 0) ? chart_override : InferChartNumber(chart_path);
  std::printf("\nChart index: %d\n", chart_num);

  // Collect skeleton split rows
  std::printf("Collecting %zu ancestor skeleton split rows...\n",
              split_res.skeleton_split_ids.size());
  Timer skel_timer;
  auto skeleton_splits = CollectSkeletonSplits(chart_path, split_res.skeleton_split_ids, &status);
  status.Remove();
  std::printf("Collected %zu skeleton splits in %.3fs.\n",
              skeleton_splits.size(), skel_timer.Seconds());

  // Propagate geometry down the skeleton tree
  std::printf("Propagating Cayley box and projective triangle geometry to subchart roots...\n");
  auto root_geometries = ComputeRootGeometries(chart_num, skeleton_splits, split_res);
  std::printf("Computed geometry for %zu subchart roots.\n", root_geometries.size());

  if (write_shards) {
    if (out_dir.empty()) {
      std::filesystem::path p(chart_path);
      out_dir = p.parent_path().string();
      if (out_dir.empty()) out_dir = ".";
    }
    if (replacement_chart_path.empty()) {
      std::filesystem::path p(chart_path);
      std::string stem = p.stem().string();
      if (stem.ends_with(".rows")) stem = stem.substr(0, stem.size() - 5);
      replacement_chart_path = out_dir + "/" + stem + ".replacement.rows.log";
    }

    std::printf("\nWriting %zu subcharts to '%s' and replacement chart to '%s'...\n",
                split_res.subcharts.size(), out_dir.c_str(), replacement_chart_path.c_str());

    Timer write_timer;
    WriteShardsResult write_res = StreamAndWriteShards(
        chart_path, split_res, root_geometries, out_dir, replacement_chart_path,
        chart_num, &status);
    status.Remove();

    if (!write_res.error.empty()) {
      std::fprintf(stderr, "Error during shard emission: %s\n", write_res.error.c_str());
      return 1;
    }

    std::printf("\n");
    std::printf("================================================================================\n");
    std::printf("Shard Cleave Emission Summary for: %s\n", chart_path.c_str());
    std::printf("================================================================================\n");
    std::printf("Emission Runtime:           %.2fs\n", write_timer.Seconds());
    std::printf("Total rows read:            %s\n", std::format("{:L}", write_res.total_rows_read).c_str());
    std::printf("Duplicate rows dropped:     %s\n", std::format("{:L}", write_res.duplicate_rows_dropped).c_str());
    std::printf("Replacement skeleton rows:  %s\n", std::format("{:L}", write_res.skeleton_rows_written).c_str());
    std::printf("Skeleton leaves written:    %s\n", std::format("{:L}", write_res.skeleton_leaves_written).c_str());
    std::printf("Subcharts emitted:          %d\n", write_res.shards_written);
    std::printf("Replacement chart path:     %s\n", write_res.replacement_chart_path.c_str());

    std::printf("\nVerifying faithful recreation from replacement skeleton and subcharts...\n");
    Timer verify_timer;
    VerificationResult vres = VerifyFaithfulRecreation(
        replacement_chart_path, write_res.subchart_paths,
        split_res.sum_subchart_leaves + split_res.skeleton_leaves,
        root_geometries);
    std::printf("Verification finished in %.2fs.\n", verify_timer.Seconds());
    std::printf("  Verified subcharts:       %d\n", vres.verified_shards);
    std::printf("  Subchart leaves:          %s\n", std::format("{:L}", vres.total_subchart_leaves).c_str());
    std::printf("  Skeleton leaves:          %s\n", std::format("{:L}", vres.total_skeleton_leaves).c_str());
    std::printf("  Total recreated leaves:   %s\n", std::format("{:L}", vres.total_recreated_leaves).c_str());
    std::printf("  Verification Verdict:     %s\n", vres.message.c_str());

    std::printf("\nSubchart Shard Breakdown:\n");
    std::printf("  %-4s  %-12s  %-12s  %-6s  %-12s  %-12s  %-10s  %-12s  %-6s\n",
                "#", "Hex ID", "Parent", "Depth", "Exp Leaves", "Got Leaves", "Delta", "Rows", "Status");
    std::printf("  --------------------------------------------------------------------------------------------\n");

    size_t total_shards = split_res.subcharts.size();
    for (size_t i = 0; i < total_shards; i++) {
      const auto &sc = split_res.subcharts[i];
      int64_t got_leaves = write_res.shard_leaves_written[i];
      bool is_mismatch = (got_leaves != sc.count);
      bool should_print = show_all || total_shards <= 128 || i < 20 || i >= total_shards - 10 || is_mismatch;
      if (should_print) {
        std::string hex_id = std::format("0x{:x}", sc.id);
        std::string parent_str = (sc.parent_id == -1) ? "root" : std::format("0x{:x}", sc.parent_id);
        std::string exp_str = std::format("{:L}", sc.count);
        std::string got_str = std::format("{:L}", got_leaves);
        int64_t diff = got_leaves - sc.count;
        std::string delta_str = (diff == 0) ? "0" : std::format("{:+d}", diff);
        std::string rows_str = std::format("{:L}", write_res.shard_rows_written[i]);
        const char *status_str = (!is_mismatch) ? "✓" : "✗";

        std::printf("  %-4zu  %-12s  %-12s  %-6d  %-12s  %-12s  %-10s  %-12s  %-6s\n",
                    i + 1, hex_id.c_str(), parent_str.c_str(), sc.depth,
                    exp_str.c_str(), got_str.c_str(), delta_str.c_str(), rows_str.c_str(), status_str);
      } else if (i == 20) {
        std::printf("  ... (intermediate subcharts omitted; pass --show_all to view all) ...\n");
      }
    }
    std::printf("================================================================================\n");

    return vres.ok ? 0 : 1;
  }

  // Pass 2: In-memory Shard Assignment and Verification Pass
  std::printf("\nStarting Pass 2: Shard assignment verification with Move-To-Front sets...\n");
  Timer pass2_timer;
  AssignmentResult assign_res = StreamAndAssignShards(chart_path, split_res, &status);
  status.Remove();

  if (!assign_res.error.empty()) {
    std::fprintf(stderr, "Error during shard assignment: %s\n", assign_res.error.c_str());
    return 1;
  }

  std::printf("\n");
  std::printf("================================================================================\n");
  std::printf("Pass 2: Shard Cleave Verification for: %s\n", chart_path.c_str());
  std::printf("================================================================================\n");
  std::printf("Passes needed to assign:    %d\n", assign_res.passes_needed);
  std::printf("Total rows processed:       %s\n", std::format("{:L}", assign_res.total_lines).c_str());
  std::printf("Duplicate rows dropped:     %s\n",
              std::format("{:L}", assign_res.duplicate_rows_dropped).c_str());
  std::printf("Unassigned rows:            %s\n", std::format("{:L}", assign_res.unassigned_rows).c_str());
  std::printf("Main skeleton splits:       %s\n", std::format("{:L}", assign_res.skeleton_splits).c_str());
  std::printf("Main skeleton leaves:       %s\n", std::format("{:L}", assign_res.skeleton_leaves).c_str());
  std::printf("Move-To-Front Total probes: %s\n", std::format("{:L}", assign_res.total_mtf_lookups).c_str());
  std::printf("MTF Position 0 Hit Rate:    %.2f%%\n", assign_res.pos0_hit_rate);
  std::printf("MTF Average Probe Depth:    %.3f\n", assign_res.avg_mtf_depth);
  std::printf("Verification Verdict:       %s\n",
              assign_res.is_exact_match ? "DISJOINT AND COMPLETE PARTITION CONFIRMED ✓"
                                        : "MISMATCH DETECTED ✗");
  std::printf("Assignment Pass Runtime:    %.2fs\n", pass2_timer.Seconds());
  std::printf("\n");

  std::printf("Shard Assignment Breakdown:\n");
  std::printf("  %-4s  %-12s  %-12s  %-6s  %-12s  %-12s  %-10s  %-12s  %-6s\n",
              "#", "Hex ID", "Parent", "Depth", "Exp Leaves", "Got Leaves", "Delta", "Splits", "Status");
  std::printf("  --------------------------------------------------------------------------------------------\n");

  size_t total_shards = assign_res.shards.size();
  for (size_t i = 0; i < total_shards; i++) {
    const auto &s = assign_res.shards[i];
    bool is_mismatch = (s.assigned_leaves != s.expected_leaves);
    bool should_print = show_all || total_shards <= 128 || i < 20 || i >= total_shards - 10 || is_mismatch;
    if (should_print) {
      std::string hex_id = std::format("0x{:x}", s.root_id);
      std::string parent_str = (s.parent_id == -1) ? "root" : std::format("0x{:x}", s.parent_id);
      std::string exp_str = std::format("{:L}", s.expected_leaves);
      std::string got_str = std::format("{:L}", s.assigned_leaves);
      int64_t diff = s.assigned_leaves - s.expected_leaves;
      std::string delta_str = (diff == 0) ? "0" : std::format("{:+d}", diff);
      std::string splits_str = std::format("{:L}", s.assigned_splits);
      const char *status_str = (!is_mismatch) ? "✓" : "✗";

      std::printf("  %-4zu  %-12s  %-12s  %-6d  %-12s  %-12s  %-10s  %-12s  %-6s\n",
                  i + 1, hex_id.c_str(), parent_str.c_str(), s.depth,
                  exp_str.c_str(), got_str.c_str(), delta_str.c_str(), splits_str.c_str(), status_str);
    } else if (i == 20) {
      std::printf("  ... (intermediate subcharts omitted; pass --show_all to view all) ...\n");
    }
  }
  std::printf("================================================================================\n");

  if (!output_roots_path.empty()) {
    std::ofstream out(output_roots_path);
    if (!out) {
      std::fprintf(stderr, "Error opening output file '%s': %s\n",
                   output_roots_path.c_str(), std::strerror(errno));
      return 1;
    }
    out << "# Subchart roots for " << chart_path << " (T=" << split_res.subcharts.size() << ")\n";
    out << "# hex_id dec_id parent_hex depth leaves splits\n";
    for (const auto &s : assign_res.shards) {
      out << std::format("{:x} {} {:x} {} {} {}\n",
                         s.root_id, s.root_id, (s.parent_id == -1 ? 0 : s.parent_id),
                         s.depth, s.assigned_leaves, s.assigned_splits);
    }
    std::printf("Wrote %zu subchart roots to '%s'.\n",
                assign_res.shards.size(), output_roots_path.c_str());
  }

  return assign_res.is_exact_match ? 0 : 1;
}
