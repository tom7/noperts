// flatten-charts.cc: Recursively absorbs small subcharts
// into parent chart/subchart files, tracking exact geometry.

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <string>
#include <vector>

#include "chart229.h"
#include "flatten-charts.h"
#include "lib229.h"

static void PrintUsage(const char *argv0) {
  std::cerr << "Usage: " << argv0 << " [options] [subchart_files...]\n"
            << "Options:\n"
            << "  --subcharts_dir <path> Directory containing .subchart files (default: /mnt/nopertdata or .)\n"
            << "  --threshold <N>        Row threshold for absorbing vs leaving split (default: 50000)\n"
            << "  --chart <N>            Chart index (0, 1, 2) when auto-discovering files (default: 0)\n"
            << "  --out <path>           Output path (only with a single input file; default: in-place)\n"
            << "  --dry_run              Analyze and report actions without writing changes or deleting files\n"
            << "  --keep_subcharts       Do not delete absorbed .subchart files\n"
            << "  -v, --verbose          Verbose logging\n"
            << "  -h, --help             Show this help message\n";
}

int main(int argc, char **argv) {
  flatten_charts::FlattenOptions options;
  if (!std::filesystem::exists("/mnt/nopertdata")) {
    options.subcharts_dir = ".";
  }

  int chart_num = 0;
  std::string single_out_path = "";
  std::vector<std::string> input_files;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--subcharts_dir" || arg == "--done_dir") {
      if (i + 1 < argc) {
        options.subcharts_dir = argv[++i];
      } else {
        std::cerr << "Error: " << arg << " requires an argument\n";
        return 1;
      }
    } else if (arg == "--threshold") {
      if (i + 1 < argc) {
        options.threshold = std::atoi(argv[++i]);
      } else {
        std::cerr << "Error: --threshold requires an argument\n";
        return 1;
      }
    } else if (arg == "--chart") {
      if (i + 1 < argc) {
        chart_num = std::atoi(argv[++i]);
      } else {
        std::cerr << "Error: --chart requires an argument\n";
        return 1;
      }
    } else if (arg == "--out") {
      if (i + 1 < argc) {
        single_out_path = argv[++i];
      } else {
        std::cerr << "Error: --out requires an argument\n";
        return 1;
      }
    } else if (arg == "--dry_run") {
      options.dry_run = true;
    } else if (arg == "--keep_subcharts" || arg == "--keep_done") {
      options.keep_subcharts = true;
    } else if (arg == "-v" || arg == "--verbose") {
      options.verbose = true;
    } else if (arg == "-h" || arg == "--help") {
      PrintUsage(argv[0]);
      return 0;
    } else if (arg.rfind("-", 0) == 0) {
      std::cerr << "Unknown option: " << arg << "\n";
      PrintUsage(argv[0]);
      return 1;
    } else {
      input_files.push_back(arg);
    }
  }

  if (input_files.empty()) {
    // Auto-discover subcharts for the specified chart in subcharts_dir
    std::string prefix = std::format("chart{}.", chart_num);
    for (const auto &entry : std::filesystem::directory_iterator(options.subcharts_dir)) {
      if (!entry.is_regular_file()) continue;
      std::string fname = entry.path().filename().string();
      if (fname.rfind(prefix, 0) == 0 &&
          fname.size() >= 9 && fname.substr(fname.size() - 9) == ".subchart") {
        input_files.push_back(entry.path().string());
      }
    }
    std::sort(input_files.begin(), input_files.end());
    if (input_files.empty()) {
      std::cerr << "No input files specified and no " << prefix << "*.subchart files found in "
                << options.subcharts_dir << "\n";
      return 1;
    }
    std::cout << "Auto-discovered " << input_files.size() << " subchart files for Chart "
              << chart_num << " in " << options.subcharts_dir << "\n";
  }

  if (!single_out_path.empty() && input_files.size() > 1) {
    std::cerr << "Error: --out can only be used with a single input file.\n";
    return 1;
  }

  std::cout << "Flattening " << input_files.size() << " files with threshold "
            << options.threshold << " (subcharts_dir: " << options.subcharts_dir << ")\n";
  if (options.dry_run) {
    std::cout << "*** DRY RUN MODE - No files will be modified or deleted ***\n";
  }

  auto start_time = std::chrono::steady_clock::now();
  flatten_charts::FlattenStats total_stats;

  for (size_t i = 0; i < input_files.size(); i++) {
    const std::string &in_file = input_files[i];
    std::string out_file = single_out_path.empty() ? in_file : single_out_path;

    flatten_charts::FlattenStats file_stats;
    bool ok = flatten_charts::FlattenChartFile(in_file, out_file, options, file_stats, chart_num);
    if (!ok) {
      std::cerr << "Error processing " << in_file << "\n";
    }

    total_stats.df_rows_found += file_stats.df_rows_found;
    total_stats.files_absorbed += file_stats.files_absorbed;
    total_stats.rows_absorbed += file_stats.rows_absorbed;
    total_stats.files_converted_to_subchart += file_stats.files_converted_to_subchart;
    total_stats.subcharts_removed += file_stats.subcharts_removed;
    total_stats.unresolved_df += file_stats.unresolved_df;
    total_stats.pending_df += file_stats.pending_df;
    total_stats.geometry_errors += file_stats.geometry_errors;

    if (file_stats.df_rows_found > 0 || options.verbose) {
      std::cout << "[" << (i + 1) << "/" << input_files.size() << "] "
                << std::filesystem::path(in_file).filename().string() << ": "
                << file_stats.df_rows_found << " df rows, "
                << file_stats.files_absorbed << " absorbed (" << file_stats.rows_absorbed << " rows), "
                << file_stats.pending_df << " pending, "
                << file_stats.geometry_errors << " errors.\n";
    }
  }

  auto end_time = std::chrono::steady_clock::now();
  double elapsed = std::chrono::duration<double>(end_time - start_time).count();

  std::cout << "\n=== Flattening Complete (" << elapsed << "s) ===\n"
            << "Files processed:                 " << input_files.size() << "\n"
            << "Difficult (df) rows found:       " << total_stats.df_rows_found << "\n"
            << "Subtrees absorbed (<= " << options.threshold << " rows):  "
            << total_stats.files_absorbed << "\n"
            << "Rows absorbed into parents:      " << total_stats.rows_absorbed << "\n"
            << "Absorbed .subchart files removed:" << total_stats.subcharts_removed << "\n"
            << "Pending unsolved df rows:        " << total_stats.pending_df << "\n"
            << "Geometry tracing errors:         " << total_stats.geometry_errors << "\n";

  return (total_stats.geometry_errors > 0) ? 1 : 0;
}
