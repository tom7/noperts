// split-chart.cc: Analyzes and computes a balanced split of a chart file
// into T subcharts using streaming and a two-phase rollup (coarse rollup
// followed by Huffman-style prioritized subtree merging).
//
// Designed to process multi-gigabyte chart files with low RAM usage.

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <fstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <variant>
#include <vector>

#include "chart229.h"
#include "periodically.h"
#include "split-chart.h"
#include "status-bar.h"
#include "timer.h"

static std::string FormatBytes(int64_t bytes) {
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

int main(int argc, char **argv) {
  int target_subcharts = 64;
  size_t max_nodes = 131072; // 128k
  std::string chart_path;
  std::string output_roots_path;
  bool show_all = false;

  for (int i = 1; i < argc; i++) {
    std::string_view arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      std::fprintf(stderr,
                   "Usage: %s [options] <chart.rows.log> [target_subcharts]\n\n"
                   "Computes a balanced split of a chart into T subcharts.\n\n"
                   "Options:\n"
                   "  -T, --target <N>     Target number of subcharts (default: 64)\n"
                   "  -N, --max_nodes <N>  Threshold for Huffman prioritized rollup (default: 131072)\n"
                   "  -o, --output <file>  Optional path to write list of chosen subchart root IDs\n"
                   "  --show_all           Print all subcharts in table (not just top/bottom)\n",
                   argv[0]);
      return 0;
    } else if ((arg == "-T" || arg == "--target") && i + 1 < argc) {
      target_subcharts = std::atoi(argv[++i]);
    } else if ((arg == "-N" || arg == "--max_nodes") && i + 1 < argc) {
      max_nodes = std::strtoull(argv[++i], nullptr, 10);
    } else if ((arg == "-o" || arg == "--output") && i + 1 < argc) {
      output_roots_path = argv[++i];
    } else if (arg == "--show_all") {
      show_all = true;
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

  FILE *in_file = std::fopen(chart_path.c_str(), "rb");
  if (!in_file) {
    std::fprintf(stderr, "Error opening '%s': %s\n", chart_path.c_str(), std::strerror(errno));
    return 1;
  }

  int64_t total_bytes = -1;
  if (fseeko(in_file, 0, SEEK_END) == 0) {
    total_bytes = ftello(in_file);
    fseeko(in_file, 0, SEEK_SET);
  }

  StatusBar status(1);
  Periodically progress_per(0.25);
  Timer timer;

  std::unordered_map<int64_t, InternalNode> node_map;
  int64_t total_lines = 0;
  int64_t total_leaf_rows = 0;
  int64_t total_split_rows = 0;
  int64_t parse_errors = 0;
  int64_t bytes_in = 0;

  static constexpr size_t CHUNK_SIZE = 1024 * 1024; // 1 MB
  std::vector<char> in_buf(CHUNK_SIZE);
  std::string remainder;

  auto HandleLine = [&](std::string_view line) -> bool {
    total_lines++;
    Chart229::Row row = Chart229::Parse(line);
    if (std::holds_alternative<Chart229::ParseError>(row)) {
      parse_errors++;
      return true;
    }

    std::visit([&](const auto &r) {
      using T = std::decay_t<decltype(r)>;
      if constexpr (std::is_same_v<T, Chart229::SplitRow> ||
                    std::is_same_v<T, Chart229::SplitOriginRow> ||
                    std::is_same_v<T, Chart229::SplitViewRow>) {
        total_split_rows++;
        auto &node = node_map[r.id];
        node.parent_id = r.parent_id;
        node.depth = r.depth;
        node.is_split_row = true;
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

    return true;
  };

  while (true) {
    size_t n = std::fread(in_buf.data(), 1, in_buf.size(), in_file);
    if (n == 0) {
      if (std::ferror(in_file)) {
        status.Print("Error reading input file: {}\n", std::strerror(errno));
        std::fclose(in_file);
        return 1;
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
        if (!remainder.empty() && remainder.back() == '\r') {
          remainder.pop_back();
        }
        HandleLine(remainder);
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
        if (!line.empty() && line.back() == '\r') {
          line.remove_suffix(1);
        }
        HandleLine(line);
        line_start = nl + 1;
      } else {
        remainder.assign(line_start, end - line_start);
        break;
      }
    }

    if (progress_per.ShouldRun()) {
      double elapsed = timer.Seconds();
      double mb_s = (bytes_in / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);

      if (total_bytes > 0) {
        status.Progress(
            bytes_in, total_bytes,
            "streaming chart... internal nodes: {:L} | leaves: {:L} | lines: {:L} | {:.1f} MB/s",
            node_map.size(), total_leaf_rows, total_lines, mb_s);
      } else {
        status.Status(
            "in: {} | internal nodes: {:L} | leaves: {:L} | lines: {:L} | {:.1f} MB/s",
            FormatBytes(bytes_in), node_map.size(), total_leaf_rows, total_lines, mb_s);
      }
    }
  }

  if (!remainder.empty()) {
    if (remainder.back() == '\r') remainder.pop_back();
    HandleLine(remainder);
    remainder.clear();
  }
  std::fclose(in_file);

  status.Print("Streaming complete in {:.2f}s: {:L} lines read ({}).\n"
               "  Internal split nodes: {:L}\n"
               "  Leaf certificate/prune rows: {:L}\n"
               "  Initial node map size: {:L}\n",
               timer.Seconds(), total_lines, FormatBytes(bytes_in),
               total_split_rows, total_leaf_rows, node_map.size());

  if (total_leaf_rows == 0) {
    status.Print("Error: chart contains no leaf rows to split.\n");
    return 1;
  }

  SplitResult result = ComputeBalancedSplit(
      std::move(node_map), total_leaf_rows, target_subcharts, max_nodes, &status);

  // Cleanly remove status bar before printing the final analysis report.
  status.Remove();

  int64_t total_accounted = result.sum_subchart_leaves + result.skeleton_leaves;

  std::printf("\n");
  std::printf("================================================================================\n");
  std::printf("Split Analysis for: %s\n", chart_path.c_str());
  std::printf("================================================================================\n");
  std::printf("Target subcharts (T):       %d\n", target_subcharts);
  std::printf("Actual subcharts:           %zu\n", result.subcharts.size());
  std::printf("Total input lines:          %s\n", std::format("{:L}", total_lines).c_str());
  std::printf("Total leaf certificates:    %s\n", std::format("{:L}", total_leaf_rows).c_str());
  std::printf("Leaves in subcharts:        %s (%.2f%%)\n",
              std::format("{:L}", result.sum_subchart_leaves).c_str(),
              100.0 * result.sum_subchart_leaves / total_leaf_rows);
  std::printf("Leaves in main skeleton:    %s (%.2f%%)\n",
              std::format("{:L}", result.skeleton_leaves).c_str(),
              100.0 * result.skeleton_leaves / total_leaf_rows);
  std::printf("Main skeleton splits:       %s\n",
              std::format("{:L}", result.skeleton_splits).c_str());
  std::printf("Verification check:         %s (sum: %s)\n",
              total_accounted == total_leaf_rows ? "EXACT MATCH ✓" : "MISMATCH ✗",
              std::format("{:L}", total_accounted).c_str());
  if (result.coarse_waves > 0) {
    std::printf("Phase 1 coarse waves:       %d\n", result.coarse_waves);
  }
  std::printf("Phase 2 Huffman merges:     %s\n",
              std::format("{:L}", result.huffman_steps).c_str());
  if (parse_errors > 0) {
    std::printf("Parse errors encountered:   %s\n", std::format("{:L}", parse_errors).c_str());
  }
  std::printf("\n");
  std::printf("Subchart Size Balance:\n");
  std::printf("  Minimum size:             %s leaves (%.2f%% of total)\n",
              std::format("{:L}", result.stats.min_count).c_str(),
              100.0 * result.stats.min_count / total_leaf_rows);
  std::printf("  Maximum size:             %s leaves (%.2f%% of total)\n",
              std::format("{:L}", result.stats.max_count).c_str(),
              100.0 * result.stats.max_count / total_leaf_rows);
  std::printf("  Mean size:                %s leaves\n",
              std::format("{:.1f}", result.stats.mean_count).c_str());
  std::printf("  Median size:              %s leaves\n",
              std::format("{:.1f}", result.stats.median_count).c_str());
  std::printf("  Std Deviation:            %s (CV: %.1f%%)\n",
              std::format("{:.1f}", result.stats.std_dev).c_str(), result.stats.cv);
  std::printf("  Max / Min Ratio:          %.2fx\n", result.stats.ratio);
  std::printf("\n");
  std::printf("Depth Distribution:\n");
  std::printf("  Min Depth:                %d\n", result.stats.min_depth);
  std::printf("  Max Depth:                %d\n", result.stats.max_depth);
  std::printf("  Avg Depth:                %.2f\n", result.stats.avg_depth);
  std::printf("\n");

  size_t print_count = result.subcharts.size();
  bool truncated = false;
  if (!show_all && print_count > 60) {
    print_count = 30;
    truncated = true;
  }

  std::printf("Proposed Subchart Roots:\n");
  std::printf("  %-4s  %-12s  %-12s  %-12s  %-6s  %-12s  %-8s\n",
              "#", "Hex ID", "Dec ID", "Parent", "Depth", "Leaves", "Share");
  std::printf("  ----------------------------------------------------------------------\n");

  for (size_t i = 0; i < print_count; i++) {
    const auto &s = result.subcharts[i];
    double pct = 100.0 * s.count / total_leaf_rows;
    std::string hex_id = std::format("0x{:x}", s.id);
    std::string dec_id = std::format("{}", s.id);
    std::string parent_str = (s.parent_id == -1) ? "root" : std::format("0x{:x}", s.parent_id);
    std::string leaves_str = std::format("{:L}", s.count);

    std::printf("  %-4zu  %-12s  %-12s  %-12s  %-6d  %-12s  %6.2f%%\n",
                i + 1, hex_id.c_str(), dec_id.c_str(), parent_str.c_str(),
                s.depth, leaves_str.c_str(), pct);
  }

  if (truncated) {
    std::printf("  ... (%zu intermediate subcharts omitted; pass --show_all to view all) ...\n",
                result.subcharts.size() - 40);
    for (size_t i = result.subcharts.size() - 10; i < result.subcharts.size(); i++) {
      const auto &s = result.subcharts[i];
      double pct = 100.0 * s.count / total_leaf_rows;
      std::string hex_id = std::format("0x{:x}", s.id);
      std::string dec_id = std::format("{}", s.id);
      std::string parent_str = (s.parent_id == -1) ? "root" : std::format("0x{:x}", s.parent_id);
      std::string leaves_str = std::format("{:L}", s.count);

      std::printf("  %-4zu  %-12s  %-12s  %-12s  %-6d  %-12s  %6.2f%%\n",
                  i + 1, hex_id.c_str(), dec_id.c_str(), parent_str.c_str(),
                  s.depth, leaves_str.c_str(), pct);
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
    out << "# Subchart roots for " << chart_path << " (T=" << result.subcharts.size() << ")\n";
    out << "# hex_id dec_id parent_hex depth leaves pct\n";
    for (const auto &s : result.subcharts) {
      double pct = 100.0 * s.count / total_leaf_rows;
      out << std::format("{:x} {} {:x} {} {} {:.4f}\n",
                         s.id, s.id, (s.parent_id == -1 ? 0 : s.parent_id),
                         s.depth, s.count, pct);
    }
    std::printf("Wrote %zu subchart roots to '%s'.\n",
                result.subcharts.size(), output_roots_path.c_str());
  }

  return 0;
}
