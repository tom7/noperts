// compare-charts.cc: Compares two chart files by parsing them into C++ structs
// in RAM and verifying exact semantic equality row by row.
//
// Streams both files line by line to keep memory footprint minimal O(1),
// capable of verifying files of arbitrary size (e.g. 60 GB).
// Prioritizes simplicity and correctness.

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <string>
#include <string_view>
#include <variant>

#include "chart229.h"
#include "periodically.h"
#include "status-bar.h"
#include "timer.h"

static std::string DescribeRow(const Chart229::Row &r) {
  return std::visit([](const auto &x) -> std::string {
    using T = std::decay_t<decltype(x)>;
    if constexpr (std::is_same_v<T, Chart229::ParseError>) {
      return "ParseError: " + x.message;
    } else if constexpr (std::is_same_v<T, Chart229::EmptyRow>) {
      return "EmptyRow";
    } else if constexpr (std::is_same_v<T, Chart229::CommentRow>) {
      return "CommentRow(# " + x.text + ")";
    } else if constexpr (std::is_same_v<T, Chart229::CertRow>) {
      return std::format("CertRow(id={}, parent={}, depth={}, triple={}, margin={:.17g}, in=[{},{},{}])",
                         x.id, x.parent_id, x.depth, x.winning_triple, x.margin,
                         x.in0, x.in1, x.in2);
    } else if constexpr (std::is_same_v<T, Chart229::MixedCertRow>) {
      std::string s = std::format("MixedCertRow(id={}, parent={}, depth={}, margin={:.17g}, components=[",
                                  x.id, x.parent_id, x.depth, x.margin);
      for (size_t i = 0; i < x.components.size(); i++) {
        if (i > 0) s += ", ";
        s += std::format("{{triple={}, weight={:.17g}, in=[{},{},{}]}}",
                         x.components[i].winning_triple, x.components[i].weight,
                         x.components[i].in0, x.components[i].in1, x.components[i].in2);
      }
      s += "])";
      return s;
    } else if constexpr (std::is_same_v<T, Chart229::SplitRow>) {
      return std::format("SplitRow(id={}, parent={}, depth={}, children=[{},{}])",
                         x.id, x.parent_id, x.depth, x.child0, x.child1);
    } else if constexpr (std::is_same_v<T, Chart229::SplitOriginRow>) {
      return std::format("SplitOriginRow(id={}, parent={}, depth={}, children=[{},{}])",
                         x.id, x.parent_id, x.depth, x.child0, x.child1);
    } else if constexpr (std::is_same_v<T, Chart229::SplitViewRow>) {
      return std::format("SplitViewRow(id={}, parent={}, depth={}, children=[{},{},{},{}])",
                         x.id, x.parent_id, x.depth, x.child0, x.child1, x.child2, x.child3);
    } else if constexpr (std::is_same_v<T, Chart229::PruneRadiusRow>) {
      return std::format("PruneRadiusRow(id={}, parent={}, depth={})",
                         x.id, x.parent_id, x.depth);
    } else if constexpr (std::is_same_v<T, Chart229::PruneFundamentalRow>) {
      return std::format("PruneFundamentalRow(id={}, parent={}, depth={}, fund_dir={})",
                         x.id, x.parent_id, x.depth, x.fund_dir);
    } else if constexpr (std::is_same_v<T, Chart229::TubeRow>) {
      return std::format("TubeRow(id={}, parent={}, depth={}, tube_radius={:.17g})",
                         x.id, x.parent_id, x.depth, x.tube_radius);
    } else if constexpr (std::is_same_v<T, Chart229::DifficultRow>) {
      return std::format("DifficultRow(id={}, parent={}, depth={})",
                         x.id, x.parent_id, x.depth);
    } else {
      return "UnknownRow";
    }
  }, r);
}

int main(int argc, char **argv) {
  if (argc == 2 && (std::string_view(argv[1]) == "--help" || std::string_view(argv[1]) == "-h")) {
    std::fprintf(stderr,
                 "Usage: %s <chart1.rows.log> <chart2.rows.log>\n\n"
                 "Compares two chart files by streaming both line-by-line, parsing each line\n"
                 "into structured C++ row objects in RAM, and verifying exact semantic equality.\n",
                 argv[0]);
    return 0;
  }

  if (argc < 3) {
    std::fprintf(stderr, "Usage: %s <chart1.rows.log> <chart2.rows.log>\n", argv[0]);
    return 1;
  }

  std::string path1 = argv[1];
  std::string path2 = argv[2];

  FILE *f1 = std::fopen(path1.c_str(), "rb");
  if (!f1) {
    std::fprintf(stderr, "Error: cannot open File 1 '%s': %s\n", path1.c_str(), std::strerror(errno));
    return 1;
  }

  FILE *f2 = std::fopen(path2.c_str(), "rb");
  if (!f2) {
    std::fprintf(stderr, "Error: cannot open File 2 '%s': %s\n", path2.c_str(), std::strerror(errno));
    std::fclose(f1);
    return 1;
  }

  int64_t size1 = -1;
  if (fseeko(f1, 0, SEEK_END) == 0) {
    size1 = ftello(f1);
    fseeko(f1, 0, SEEK_SET);
  }

  StatusBar status(1);
  Periodically progress_per(0.25);
  Timer timer;

  char *line1 = nullptr;
  size_t cap1 = 0;
  ssize_t len1 = 0;

  char *line2 = nullptr;
  size_t cap2 = 0;
  ssize_t len2 = 0;

  int64_t line_num = 0;
  int64_t bytes_read1 = 0;

  auto CleanUp = [&]() {
    if (line1) std::free(line1);
    if (line2) std::free(line2);
    std::fclose(f1);
    std::fclose(f2);
  };

  while (true) {
    len1 = getline(&line1, &cap1, f1);
    len2 = getline(&line2, &cap2, f2);

    if (len1 < 0 && len2 < 0) {
      if (std::ferror(f1)) {
        status.Print("Error reading from File 1: {}\n", std::strerror(errno));
        CleanUp();
        return 1;
      }
      if (std::ferror(f2)) {
        status.Print("Error reading from File 2: {}\n", std::strerror(errno));
        CleanUp();
        return 1;
      }
      // Both cleanly reached EOF
      break;
    }

    line_num++;

    if (len1 < 0) {
      status.Print("ERROR: File 1 ('{}') ended prematurely at line {:L}, but File 2 ('{}') has more rows.\n",
                   path1, line_num, path2);
      CleanUp();
      return 1;
    }

    if (len2 < 0) {
      status.Print("ERROR: File 2 ('{}') ended prematurely at line {:L}, but File 1 ('{}') has more rows.\n",
                   path2, line_num, path1);
      CleanUp();
      return 1;
    }

    bytes_read1 += len1;

    std::string_view sv1(line1, len1);
    if (!sv1.empty() && sv1.back() == '\n') sv1.remove_suffix(1);
    if (!sv1.empty() && sv1.back() == '\r') sv1.remove_suffix(1);

    std::string_view sv2(line2, len2);
    if (!sv2.empty() && sv2.back() == '\n') sv2.remove_suffix(1);
    if (!sv2.empty() && sv2.back() == '\r') sv2.remove_suffix(1);

    Chart229::Row r1 = Chart229::Parse(sv1);
    Chart229::Row r2 = Chart229::Parse(sv2);

    if (std::holds_alternative<Chart229::ParseError>(r1)) {
      status.Print("ERROR: Parse error in File 1 ('{}') at line {:L}: {}\nLine content: '{}'\n",
                   path1, line_num, std::get<Chart229::ParseError>(r1).message, sv1);
      CleanUp();
      return 1;
    }

    if (std::holds_alternative<Chart229::ParseError>(r2)) {
      status.Print("ERROR: Parse error in File 2 ('{}') at line {:L}: {}\nLine content: '{}'\n",
                   path2, line_num, std::get<Chart229::ParseError>(r2).message, sv2);
      CleanUp();
      return 1;
    }

    if (r1 != r2) {
      status.Print("ERROR: Semantic row mismatch at line {:L}!\n"
                   "  File 1: {}\n"
                   "          Raw line: '{}'\n"
                   "  File 2: {}\n"
                   "          Raw line: '{}'\n",
                   line_num,
                   DescribeRow(r1), sv1,
                   DescribeRow(r2), sv2);
      CleanUp();
      return 1;
    }

    if (progress_per.ShouldRun()) {
      double elapsed = timer.Seconds();
      double mb_s = (bytes_read1 / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);
      if (size1 > 0) {
        status.Progress(bytes_read1, size1,
                        "verified: {:L} rows | {:.1f} MB/s",
                        line_num, mb_s);
      } else {
        status.Status("verified: {:L} rows | {:.1f} MB/s",
                      line_num, mb_s);
      }
    }
  }

  CleanUp();

  status.Abandon();

  double elapsed = timer.Seconds();
  double mb_s = (bytes_read1 / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);

  status.Print("Charts match! Verified {:L} rows in RAM across both files in {:.2f}s ({:.1f} MB/s).\n",
               line_num, elapsed, mb_s);

  return 0;
}
