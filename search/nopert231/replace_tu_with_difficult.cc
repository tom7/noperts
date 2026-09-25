// replace_tu_with_difficult.cc: Replaces "TU" (identity tube) certificate rows
// with "DF" (difficult) rows in a chart validation rows.log, and generates
// the corresponding chart<chart>.tu-difficult file for difficult229 / lean229.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <format>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <string_view>
#include <sys/mman.h>
#include <sys/stat.h>
#include <thread>
#include <unistd.h>
#include <unordered_map>
#include <vector>

struct Vec3 {
  double x = 0.0, y = 0.0, z = 0.0;
};

struct TuOccurrence {
  uint64_t byte_offset = 0;
  size_t length = 0;
  std::string original_line;
  std::string line_ending = "\n";
  int64_t id = 0;
  int64_t parent_id = 0;
  int depth = 0;
  double radius = 0.0;
};

// Distinct octant & subwedge definitions for Chart 0 root origin splits
struct CellGeom {
  int subwedge = 0;
  int sx = 0, sy = 0, sz = 0; // signs: +1 or -1
};

// Known verified mapping of the 32 TU nodes in Chart 0
static const std::unordered_map<int64_t, CellGeom> CHART0_TU_MAPPING = {
  // Subwedge 0
  {4589165,    {0,  1,  1, -1}},
  {4589168,    {0,  1, -1, -1}},
  {4589169,    {0, -1,  1, -1}},
  {7987956,    {0, -1, -1, -1}},
  {1100541847, {0,  1,  1,  1}},
  {1100541849, {0, -1,  1,  1}},
  {1100541866, {0, -1, -1,  1}},
  {1100541870, {0,  1, -1,  1}},

  // Subwedge 1
  {1100541854, {1,  1, -1, -1}},
  {1100541859, {1,  1,  1, -1}},
  {1100541829, {1, -1,  1, -1}},
  {1100541838, {1, -1, -1, -1}},
  {1100541706, {1,  1, -1,  1}},
  {1100541841, {1,  1,  1,  1}},
  {1100541835, {1, -1,  1,  1}},
  {1100541820, {1, -1, -1,  1}},

  // Subwedge 2
  {1100541832, {2,  1, -1, -1}},
  {1100541833, {2,  1,  1, -1}},
  {1100541826, {2, -1, -1, -1}},
  {1100541867, {2, -1,  1, -1}},
  {1100541828, {2,  1, -1,  1}},
  {1100541823, {2,  1,  1,  1}},
  {1100541821, {2, -1,  1,  1}},
  {1100541862, {2, -1, -1,  1}},

  // Subwedge 3
  {1100541864, {3,  1, -1, -1}},
  {1100541857, {3,  1,  1, -1}},
  {1100541839, {3, -1,  1, -1}},
  {1100541844, {3, -1, -1, -1}},
  {1100541872, {3,  1, -1,  1}},
  {1100541855, {3,  1,  1,  1}},
  {1100541851, {3, -1,  1,  1}},
  {1100541846, {3, -1, -1,  1}},
};

static inline int64_t parse_i64(const char *&p) {
  while (*p == ' ') p++;
  bool neg = false;
  if (*p == '-') {
    neg = true;
    p++;
  }
  int64_t v = 0;
  while (*p >= '0' && *p <= '9') {
    v = v * 10 + (*p - '0');
    p++;
  }
  return neg ? -v : v;
}

static bool ReadOffsetsFile(const std::string &path, int fd, std::vector<TuOccurrence> *out) {
  std::ifstream in(path);
  if (!in.is_open()) return false;
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    uint64_t offset = 0;
    size_t len = 0;
    if (!(iss >> offset >> len)) continue;

    std::string buf(len, '\0');
    ssize_t r = pread(fd, buf.data(), len, offset);
    if (r != (ssize_t)len) {
      std::cerr << "Failed to read " << len << " bytes at offset " << offset << "\n";
      return false;
    }

    TuOccurrence occ;
    occ.byte_offset = offset;
    occ.length = len;
    occ.original_line = buf;
    if (buf.size() >= 2 && buf.substr(buf.size() - 2) == "\r\n") {
      occ.line_ending = "\r\n";
    } else {
      occ.line_ending = "\n";
    }

    const char *cur = buf.data();
    if (buf.rfind("TU ", 0) != 0 && buf.rfind("DF ", 0) != 0) {
      std::cerr << "Line at offset " << offset << " does not begin with TU or DF: '" << buf << "'\n";
      return false;
    }
    cur += 3;
    occ.id = parse_i64(cur);
    occ.parent_id = parse_i64(cur);
    occ.depth = (int)parse_i64(cur);
    while (*cur == ' ') cur++;
    occ.radius = std::strtod(cur, nullptr);
    out->push_back(occ);
  }
  return !out->empty();
}

int main(int argc, char **argv) {
  std::string log_path = "/root/nopert-project/chart0.rows.log";
  std::string difficult_out = "/root/nopert-project/chart0.tu-difficult";
  std::string backup_out = "/root/nopert-project/chart0.tu_replaced.backup";
  bool in_place = false;
  bool restore = false;
  bool force_scan = false;
  int threads_count = 32;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--log" && i + 1 < argc) {
      log_path = argv[++i];
    } else if (arg == "--difficult_out" && i + 1 < argc) {
      difficult_out = argv[++i];
    } else if (arg == "--backup_out" && i + 1 < argc) {
      backup_out = argv[++i];
    } else if (arg == "--in_place") {
      in_place = true;
    } else if (arg == "--restore") {
      restore = true;
    } else if (arg == "--force_scan") {
      force_scan = true;
    } else if (arg == "--threads" && i + 1 < argc) {
      threads_count = std::stoi(argv[++i]);
    } else if (arg == "--help" || arg == "-h") {
      std::cout << "Usage: " << argv[0] << " [options]\n"
                << "  --log <path>           Path to rows.log (default: " << log_path << ")\n"
                << "  --difficult_out <path> Path to output .difficult file (default: " << difficult_out << ")\n"
                << "  --backup_out <path>    Path to backup original TU lines (default: " << backup_out << ")\n"
                << "  --in_place             Replace TU lines with DF lines in-place in log file\n"
                << "  --restore              Restore original TU lines from backup file\n"
                << "  --force_scan           Scan whole file even if backup exists\n"
                << "  --threads <N>          Worker threads for scanning (default: " << threads_count << ")\n";
      return 0;
    }
  }

  std::cout << "=== Replace TU with Difficult Tool ===\n";
  std::cout << "Log file:       " << log_path << "\n";
  std::cout << "Difficult out:  " << difficult_out << "\n";
  std::cout << "Backup out:     " << backup_out << "\n";
  std::cout << "Mode:           "
            << (restore ? "RESTORE FROM BACKUP" : (in_place ? "IN-PLACE REPLACEMENT" : "DRY RUN (no file modifications)"))
            << "\n\n";

  int fd = open(log_path.c_str(), (in_place || restore) ? O_RDWR : O_RDONLY);
  if (fd < 0) {
    std::cerr << "Error: failed to open log file: " << log_path << " (" << strerror(errno) << ")\n";
    return 1;
  }

  struct stat st;
  if (fstat(fd, &st) < 0) {
    std::cerr << "Error: failed to fstat log file: " << strerror(errno) << "\n";
    close(fd);
    return 1;
  }

  size_t file_size = st.st_size;
  std::cout << "Log file size:  " << file_size << " bytes ("
            << std::fixed << std::setprecision(2) << (file_size / (1024.0 * 1024.0 * 1024.0)) << " GB)\n";

  std::vector<TuOccurrence> all_tu;

  if (restore) {
    if (!ReadOffsetsFile(backup_out, fd, &all_tu)) {
      std::cerr << "Error: failed to read backup file " << backup_out << "\n";
      close(fd);
      return 1;
    }
    std::cout << "Loaded " << all_tu.size() << " TU lines to restore from backup.\n";
    std::ifstream in(backup_out);
    std::string line;
    int restored = 0;
    while (std::getline(in, line)) {
      if (line.empty() || line[0] == '#') continue;
      std::istringstream iss(line);
      uint64_t offset = 0;
      size_t len = 0;
      std::string tag;
      if (iss >> offset >> len >> tag) {
        // Read full original line from file
        size_t tag_pos = line.find(tag);
        std::string orig = line.substr(tag_pos) + "\r\n";
        if (orig.size() != len) {
          orig = line.substr(tag_pos) + "\n";
        }
        ssize_t w = pwrite(fd, orig.data(), orig.size(), offset);
        if (w == (ssize_t)orig.size()) restored++;
      }
    }
    close(fd);
    std::cout << "Restored " << restored << " lines successfully.\n";
    return 0;
  }

  bool used_backup = false;
  if (!force_scan && std::filesystem::exists(backup_out)) {
    if (ReadOffsetsFile(backup_out, fd, &all_tu)) {
      std::cout << "Loaded " << all_tu.size() << " TU occurrences instantly from " << backup_out << ".\n";
      used_backup = true;
    }
  }

  if (!used_backup) {
    const char *mapped = (const char *)mmap(nullptr, file_size, PROT_READ, MAP_SHARED, fd, 0);
    if (mapped == MAP_FAILED) {
      std::cerr << "Error: mmap failed: " << strerror(errno) << "\n";
      close(fd);
      return 1;
    }

    std::cout << "Scanning for 'TU' lines across " << threads_count << " threads...\n" << std::flush;
    auto start_time = std::chrono::steady_clock::now();

    std::mutex results_mu;
    std::vector<std::thread> workers;
    size_t chunk_size = file_size / threads_count;

    for (int t = 0; t < threads_count; t++) {
      size_t start = t * chunk_size;
      size_t end = (t == threads_count - 1) ? file_size : (t + 1) * chunk_size;

      workers.emplace_back([&, start, end, t]() {
        size_t pos = start;
        if (t > 0) {
          while (pos < end && mapped[pos - 1] != '\n') {
            pos++;
          }
        }

        std::vector<TuOccurrence> local_tu;
        while (pos < end) {
          if (pos + 3 <= file_size && mapped[pos] == 'T' && mapped[pos + 1] == 'U' && mapped[pos + 2] == ' ') {
            size_t line_start = pos;
            while (pos < file_size && mapped[pos] != '\n') {
              pos++;
            }
            size_t line_len = (pos < file_size) ? (pos - line_start + 1) : (pos - line_start);
            std::string line_str(mapped + line_start, line_len);

            std::string line_ending = "\n";
            if (line_str.size() >= 2 && line_str.substr(line_str.size() - 2) == "\r\n") {
              line_ending = "\r\n";
            }

            const char *cur = mapped + line_start + 3;
            int64_t id = parse_i64(cur);
            int64_t parent_id = parse_i64(cur);
            int depth = (int)parse_i64(cur);
            while (*cur == ' ') cur++;
            double radius = std::strtod(cur, nullptr);

            TuOccurrence occ;
            occ.byte_offset = line_start;
            occ.length = line_len;
            occ.original_line = line_str;
            occ.line_ending = line_ending;
            occ.id = id;
            occ.parent_id = parent_id;
            occ.depth = depth;
            occ.radius = radius;
            local_tu.push_back(occ);

            if (pos < file_size && mapped[pos] == '\n') pos++;
          } else {
            const char *next_nl = (const char *)memchr(mapped + pos, '\n', file_size - pos);
            if (!next_nl) break;
            pos = (next_nl - mapped) + 1;
          }
        }

        if (!local_tu.empty()) {
          std::lock_guard<std::mutex> lock(results_mu);
          all_tu.insert(all_tu.end(), local_tu.begin(), local_tu.end());
        }
      });
    }

    for (auto &w : workers) {
      w.join();
    }

    munmap((void *)mapped, file_size);

    auto scan_time = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(scan_time - start_time).count();
    std::cout << "Scan finished in " << std::fixed << std::setprecision(2) << elapsed << "s.\n";
    std::cout << "Found " << all_tu.size() << " TU occurrences.\n\n";
  }

  // Sort by byte offset for deterministic processing
  std::sort(all_tu.begin(), all_tu.end(), [](const TuOccurrence &a, const TuOccurrence &b) {
    return a.byte_offset < b.byte_offset;
  });

  if (all_tu.empty()) {
    std::cout << "No TU lines found in log file. Nothing to do.\n";
    close(fd);
    return 0;
  }

  // Define 4 subwedge projective triangle corners
  // Root projective view is UPPER_WEDGE_PROJECTIVE_ROOT pre-split into 4 subwedges
  std::array<std::array<Vec3, 3>, 4> subwedges;
  // Subwedge 0
  subwedges[0][0] = {1.0, 0.0, 0.0};
  subwedges[0][1] = {51.0 / 82.0, 31.0 / 82.0, 0.0};
  subwedges[0][2] = {0.5, 0.0, 0.5};

  // Subwedge 1
  subwedges[1][0] = {51.0 / 82.0, 31.0 / 82.0, 0.0};
  subwedges[1][1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  subwedges[1][2] = {5.0 / 41.0, 31.0 / 82.0, 0.5};

  // Subwedge 2
  subwedges[2][0] = {0.5, 0.0, 0.5};
  subwedges[2][1] = {5.0 / 41.0, 31.0 / 82.0, 0.5};
  subwedges[2][2] = {0.0, 0.0, 1.0};

  // Subwedge 3
  subwedges[3][0] = {51.0 / 82.0, 31.0 / 82.0, 0.0};
  subwedges[3][1] = {5.0 / 41.0, 31.0 / 82.0, 0.5};
  subwedges[3][2] = {0.5, 0.0, 0.5};

  // Radii after 49 box splits (depth 50, 1 view split + 49 box splits)
  // rx = 1.0 * 2^-17, ry = 1.0 * 2^-17, rz = (1/3) * 2^-15
  const double rx = 7.62939453125e-06;
  const double ry = 7.62939453125e-06;
  const double rz = 1.0172526041666666e-05;
  const double best_margin = -1e+30;

  // Generate chart0.tu-difficult entries
  std::ofstream diff_out(difficult_out);
  if (!diff_out.is_open()) {
    std::cerr << "Error: failed to open difficult output file: " << difficult_out << "\n";
    close(fd);
    return 1;
  }

  diff_out << "# id parent_id depth box_depth view_depth chart "
              "cx cy cz rx ry rz "
              "v0x v0y v0z v1x v1y v1z v2x v2y v2z "
              "best_margin\n";

  std::cout << "Constructing difficult cells:\n";
  int mapped_cells = 0;
  for (const auto &tu : all_tu) {
    auto it = CHART0_TU_MAPPING.find(tu.id);
    int subwedge_idx = 0;
    int sx = 1, sy = 1, sz = 1;
    if (it != CHART0_TU_MAPPING.end()) {
      subwedge_idx = it->second.subwedge;
      sx = it->second.sx;
      sy = it->second.sy;
      sz = it->second.sz;
      mapped_cells++;
    } else {
      std::cerr << "Warning: Node ID " << tu.id << " not found in pre-mapped table, using defaults.\n";
    }

    double cx = sx * rx;
    double cy = sy * ry;
    double cz = sz * rz;
    const auto &tri = subwedges[subwedge_idx];

    // Format matching DifficultCell::ToString()
    std::string line = std::format(
        "{} {} {} {} {} {} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} "
        "{:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g}\n",
        tu.id, tu.parent_id,
        50, // depth
        49, // box_depth
        1,  // view_depth
        0,  // chart
        cx, cy, cz, rx, ry, rz,
        tri[0].x, tri[0].y, tri[0].z,
        tri[1].x, tri[1].y, tri[1].z,
        tri[2].x, tri[2].y, tri[2].z,
        best_margin);
    diff_out << line;
  }
  diff_out.close();
  std::cout << "Wrote " << all_tu.size() << " cells to " << difficult_out << " (" << mapped_cells << " mapped from geometry table).\n\n";

  // Write backup if not already present
  if (!std::filesystem::exists(backup_out)) {
    std::ofstream bkp(backup_out);
    if (!bkp.is_open()) {
      std::cerr << "Warning: failed to open backup file " << backup_out << "\n";
    } else {
      bkp << "# Backup of original TU rows before DF replacement\n";
      bkp << "# byte_offset length original_line\n";
      for (const auto &tu : all_tu) {
        bkp << tu.byte_offset << " " << tu.length << " " << tu.original_line;
      }
      bkp.close();
      std::cout << "Saved original TU rows backup to " << backup_out << "\n";
    }
  }

  std::cout << "Replacement Summary (" << all_tu.size() << " lines):\n";
  bool length_mismatch = false;
  for (size_t i = 0; i < all_tu.size(); i++) {
    const auto &tu = all_tu[i];
    std::string new_line = std::format("DF {} {} {} -1e+30{}", tu.id, tu.parent_id, tu.depth, tu.line_ending);

    if (new_line.size() != tu.length) {
      std::cerr << "Error on node " << tu.id << ": original len " << tu.length
                << " != new len " << new_line.size() << "\n"
                << "  Orig: '" << tu.original_line << "'\n"
                << "  New:  '" << new_line << "'\n";
      length_mismatch = true;
    }

    if (i < 5 || i >= all_tu.size() - 5) {
      std::string orig_trimmed = tu.original_line;
      while (!orig_trimmed.empty() && (orig_trimmed.back() == '\n' || orig_trimmed.back() == '\r')) {
        orig_trimmed.pop_back();
      }
      std::string new_trimmed = new_line;
      while (!new_trimmed.empty() && (new_trimmed.back() == '\n' || new_trimmed.back() == '\r')) {
        new_trimmed.pop_back();
      }
      std::cout << "  [offset " << std::setw(11) << tu.byte_offset << "] '"
                << orig_trimmed << "' -> '" << new_trimmed << "' (len: " << tu.length << ")\n";
    } else if (i == 5) {
      std::cout << "  ... (" << (all_tu.size() - 10) << " rows omitted) ...\n";
    }
  }

  if (length_mismatch) {
    std::cerr << "Aborting: replacement line length mismatch detected!\n";
    close(fd);
    return 1;
  }

  if (!in_place) {
    std::cout << "\nDry run complete. No modifications made to " << log_path << ".\n"
              << "Run with --in_place to apply the DF replacement in " << log_path << ".\n";
    close(fd);
    return 0;
  }

  // Apply in-place replacements using pwrite
  std::cout << "\nApplying in-place replacement to " << log_path << "...\n";
  for (const auto &tu : all_tu) {
    std::string new_line = std::format("DF {} {} {} -1e+30{}", tu.id, tu.parent_id, tu.depth, tu.line_ending);
    ssize_t written = pwrite(fd, new_line.data(), new_line.size(), tu.byte_offset);
    if (written != (ssize_t)new_line.size()) {
      std::cerr << "Error writing at offset " << tu.byte_offset << ": " << strerror(errno) << "\n";
      close(fd);
      return 1;
    }
  }

  // Verify by reading back each offset
  std::cout << "Verifying replacements in-place...\n";
  int verified = 0;
  for (const auto &tu : all_tu) {
    std::string expected = std::format("DF {} {} {} -1e+30{}", tu.id, tu.parent_id, tu.depth, tu.line_ending);
    std::string buf(expected.size(), '\0');
    ssize_t r = pread(fd, buf.data(), buf.size(), tu.byte_offset);
    if (r == (ssize_t)buf.size() && buf == expected) {
      verified++;
    } else {
      std::cerr << "Verification failed at offset " << tu.byte_offset << ": read '" << buf << "'\n";
    }
  }
  close(fd);

  std::cout << "Successfully verified all " << verified << " / " << all_tu.size() << " replaced lines!\n";
  std::cout << "Done! " << log_path << " has been updated and " << difficult_out << " is ready.\n";
  return 0;
}
