// normalize-chart.cc: Normalizes chart row logs to the compact chart229 format.
//
// Streams input and output using 1 MB chunks and FILE* to support
// multi-gigabyte files (e.g. 60 GB) with low constant memory overhead.
// Shows live progress and size ratio using StatusBar and Periodically.

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "chart229.h"
#include "periodically.h"
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

struct RowCounts {
  int64_t cert = 0;
  int64_t mixed_cert = 0;
  int64_t split = 0;
  int64_t split_origin = 0;
  int64_t split_view = 0;
  int64_t prune_radius = 0;
  int64_t prune_fundamental = 0;
  int64_t tube = 0;
  int64_t difficult = 0;
  int64_t comments = 0;
  int64_t empty = 0;
};

int main(int argc, char **argv) {
  if (argc == 2 && (std::string_view(argv[1]) == "--help" || std::string_view(argv[1]) == "-h")) {
    std::fprintf(stderr,
                 "Usage: %s <input.rows.log> <output.rows.log>\n\n"
                 "Normalizes chart row records into the compact chart229 format.\n"
                 "Reads and writes in a streaming pipeline using 1 MB chunks.\n",
                 argv[0]);
    return 0;
  }

  if (argc < 3) {
    std::fprintf(stderr, "Usage: %s <input.rows.log> <output.rows.log>\n", argv[0]);
    return 1;
  }

  std::string in_path = argv[1];
  std::string out_path = argv[2];

  if (in_path == out_path) {
    std::fprintf(stderr, "Error: input and output filenames must be different.\n");
    return 1;
  }

  FILE *in_file = std::fopen(in_path.c_str(), "rb");
  if (!in_file) {
    std::fprintf(stderr, "Error: cannot open input file '%s': %s\n",
                 in_path.c_str(), std::strerror(errno));
    return 1;
  }

  int64_t total_bytes = -1;
  if (fseeko(in_file, 0, SEEK_END) == 0) {
    total_bytes = ftello(in_file);
    fseeko(in_file, 0, SEEK_SET);
  }

  FILE *out_file = std::fopen(out_path.c_str(), "wb");
  if (!out_file) {
    std::fprintf(stderr, "Error: cannot open output file '%s': %s\n",
                 out_path.c_str(), std::strerror(errno));
    std::fclose(in_file);
    return 1;
  }

  static constexpr size_t CHUNK_SIZE = 1024 * 1024; // 1 MB
  std::vector<char> in_buf(CHUNK_SIZE);
  std::string out_buf;
  out_buf.reserve(CHUNK_SIZE + 65536);
  std::string remainder;

  StatusBar status(1);
  Periodically progress_per(0.25);
  Timer timer;

  int64_t total_lines = 0;
  int64_t bytes_in = 0;
  int64_t bytes_out = 0;
  RowCounts counts;

  auto FlushOutput = [&](bool force) -> bool {
    if (out_buf.size() >= CHUNK_SIZE || (force && !out_buf.empty())) {
      size_t written = std::fwrite(out_buf.data(), 1, out_buf.size(), out_file);
      if (written != out_buf.size()) {
        status.Print("Error: failed to write to output file: {}\n", std::strerror(errno));
        return false;
      }
      bytes_out += written;
      out_buf.clear();
    }
    return true;
  };

  auto HandleLine = [&](std::string_view line) -> bool {
    total_lines++;
    Chart229::Row row = Chart229::Parse(line);
    if (std::holds_alternative<Chart229::ParseError>(row)) {
      const auto &err = std::get<Chart229::ParseError>(row);
      status.Print("Parse error on line {}: {}\nLine: '{}'\n",
                   total_lines, err.message, line);
      return false;
    }

    std::visit([&](const auto &r) {
      using T = std::decay_t<decltype(r)>;
      if constexpr (std::is_same_v<T, Chart229::CertRow>) counts.cert++;
      else if constexpr (std::is_same_v<T, Chart229::MixedCertRow>) counts.mixed_cert++;
      else if constexpr (std::is_same_v<T, Chart229::SplitRow>) counts.split++;
      else if constexpr (std::is_same_v<T, Chart229::SplitOriginRow>) counts.split_origin++;
      else if constexpr (std::is_same_v<T, Chart229::SplitViewRow>) counts.split_view++;
      else if constexpr (std::is_same_v<T, Chart229::PruneRadiusRow>) counts.prune_radius++;
      else if constexpr (std::is_same_v<T, Chart229::PruneFundamentalRow>) counts.prune_fundamental++;
      else if constexpr (std::is_same_v<T, Chart229::TubeRow>) counts.tube++;
      else if constexpr (std::is_same_v<T, Chart229::DifficultRow>) counts.difficult++;
      else if constexpr (std::is_same_v<T, Chart229::CommentRow>) counts.comments++;
      else if constexpr (std::is_same_v<T, Chart229::EmptyRow>) counts.empty++;
    }, row);

    std::string s = Chart229::Serialize(row);
    out_buf.append(s);
    out_buf.push_back('\n');

    return FlushOutput(/*force=*/false);
  };

  while (true) {
    size_t n = std::fread(in_buf.data(), 1, in_buf.size(), in_file);
    if (n == 0) {
      if (std::ferror(in_file)) {
        status.Print("Error reading input file: {}\n", std::strerror(errno));
        std::fclose(in_file);
        std::fclose(out_file);
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
        if (!HandleLine(remainder)) {
          std::fclose(in_file);
          std::fclose(out_file);
          return 1;
        }
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
        if (!HandleLine(line)) {
          std::fclose(in_file);
          std::fclose(out_file);
          return 1;
        }
        line_start = nl + 1;
      } else {
        remainder.assign(line_start, end - line_start);
        break;
      }
    }

    if (progress_per.ShouldRun()) {
      int64_t current_out = bytes_out + out_buf.size();
      double ratio = bytes_in > 0 ? (double)current_out / (double)bytes_in : 1.0;
      double elapsed = timer.Seconds();
      double mb_s = (bytes_in / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);

      if (total_bytes > 0) {
        status.Progress(
            bytes_in, total_bytes,
            "ratio: {:.3f} ({:.1f}%) | in: {} | out: {} | lines: {:L} | {:.1f} MB/s",
            ratio, ratio * 100.0,
            FormatBytes(bytes_in),
            FormatBytes(current_out),
            total_lines,
            mb_s);
      } else {
        status.Status(
            "in: {} | out: {} | ratio: {:.3f} ({:.1f}%) | lines: {:L} | {:.1f} MB/s",
            FormatBytes(bytes_in),
            FormatBytes(current_out),
            ratio, ratio * 100.0,
            total_lines,
            mb_s);
      }
    }
  }

  if (!remainder.empty()) {
    if (remainder.back() == '\r') remainder.pop_back();
    if (!HandleLine(remainder)) {
      std::fclose(in_file);
      std::fclose(out_file);
      return 1;
    }
    remainder.clear();
  }

  if (!FlushOutput(/*force=*/true)) {
    std::fclose(in_file);
    std::fclose(out_file);
    return 1;
  }

  std::fclose(in_file);
  std::fclose(out_file);

  status.Abandon();

  double elapsed = timer.Seconds();
  double ratio = bytes_in > 0 ? (double)bytes_out / (double)bytes_in : 1.0;
  double savings = bytes_in > 0 ? (1.0 - ratio) * 100.0 : 0.0;
  double mb_s = (bytes_in / (1024.0 * 1024.0)) / std::max(1e-6, elapsed);

  status.Print(
      "\nSuccessfully normalized '{}' -> '{}':\n"
      "  Input size:       {} ({:L} bytes)\n"
      "  Output size:      {} ({:L} bytes)\n"
      "  Ratio:            {:.4f} ({:.2f}% size reduction, {:.2f}% of original size)\n"
      "  Total lines:      {:L}\n"
      "  Breakdown:\n"
      "    CE (cert):           {:L}\n"
      "    MX (mixed cert):     {:L}\n"
      "    SP (box split):      {:L}\n"
      "    SO (origin split):   {:L}\n"
      "    SV (view split):     {:L}\n"
      "    PR (radius prune):   {:L}\n"
      "    PF (fund prune):     {:L}\n"
      "    TU (tube prune):     {:L}\n"
      "    DF (difficult):      {:L}\n"
      "    Comments:            {:L}\n"
      "    Empty lines:         {:L}\n"
      "  Time elapsed:     {:.2f}s ({:.1f} MB/s)\n",
      in_path, out_path,
      FormatBytes(bytes_in), bytes_in,
      FormatBytes(bytes_out), bytes_out,
      ratio, savings, ratio * 100.0,
      total_lines,
      counts.cert, counts.mixed_cert,
      counts.split, counts.split_origin, counts.split_view,
      counts.prune_radius, counts.prune_fundamental,
      counts.tube, counts.difficult,
      counts.comments, counts.empty,
      elapsed, mb_s);

  return 0;
}
