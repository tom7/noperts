#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <atomic>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

#pragma pack(push, 1)
struct NodeEntry {
  uint32_t parent;
  uint8_t info; // bits 0-1: child_index (0..3), bit 2: split_type (0 = box, 1 = view)
};
#pragma pack(pop)

struct TuRecord {
  uint32_t id;
  uint32_t parent;
  int depth;
  double radius;
};

struct Vec3D {
  double x, y, z;
};

inline Vec3D operator+(const Vec3D &a, const Vec3D &b) { return {a.x + b.x, a.y + b.y, a.z + b.z}; }
inline Vec3D operator-(const Vec3D &a, const Vec3D &b) { return {a.x - b.x, a.y - b.y, a.z - b.z}; }
inline Vec3D operator*(const Vec3D &a, double s) { return {a.x * s, a.y * s, a.z * s}; }
inline Vec3D operator/(const Vec3D &a, double s) { return {a.x / s, a.y / s, a.z / s}; }
inline double dot(const Vec3D &a, const Vec3D &b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
inline double length(const Vec3D &a) { return std::sqrt(dot(a, a)); }
inline Vec3D normalize(const Vec3D &a) { double l = length(a); return (l > 0) ? a / l : a; }

struct CayleyBoxD {
  Vec3D center;
  Vec3D radii;

  int WidestAxis() const {
    int axis = 0;
    if (radii.y > radii.x) axis = 1;
    if (radii.z > ((axis == 1) ? radii.y : radii.x)) axis = 2;
    return axis;
  }

  std::pair<CayleyBoxD, CayleyBoxD> Split(int axis) const {
    CayleyBoxD left = *this;
    CayleyBoxD right = *this;
    if (axis == 0) {
      left.radii.x *= 0.5; right.radii.x *= 0.5;
      left.center.x -= left.radii.x; right.center.x += right.radii.x;
    } else if (axis == 1) {
      left.radii.y *= 0.5; right.radii.y *= 0.5;
      left.center.y -= left.radii.y; right.center.y += right.radii.y;
    } else {
      left.radii.z *= 0.5; right.radii.z *= 0.5;
      left.center.z -= left.radii.z; right.center.z += right.radii.z;
    }
    return {left, right};
  }
};

struct ProjectiveTriangleD {
  Vec3D corners[3];

  std::array<ProjectiveTriangleD, 4> Subdivide() const {
    Vec3D m01 = (corners[0] + corners[1]) * 0.5;
    Vec3D m12 = (corners[1] + corners[2]) * 0.5;
    Vec3D m20 = (corners[2] + corners[0]) * 0.5;
    return {{
      {corners[0], m01, m20},
      {m01, corners[1], m12},
      {m20, m12, corners[2]},
      {m01, m12, m20}
    }};
  }

  double AngularDiameter() const {
    Vec3D u0 = normalize(corners[0]);
    Vec3D u1 = normalize(corners[1]);
    Vec3D u2 = normalize(corners[2]);
    double d01 = length(u0 - u1);
    double d12 = length(u1 - u2);
    double d20 = length(u2 - u0);
    return std::max({d01, d12, d20});
  }

  Vec3D CentroidUnit() const {
    Vec3D c = (corners[0] + corners[1] + corners[2]) / 3.0;
    return normalize(c);
  }
};

static inline uint32_t parse_u32(const char *&p) {
  while (*p == ' ' || *p == '\t') p++;
  uint32_t val = 0;
  while (*p >= '0' && *p <= '9') {
    val = val * 10 + (*p - '0');
    p++;
  }
  return val;
}

static inline int parse_i32(const char *&p) {
  while (*p == ' ' || *p == '\t') p++;
  int sign = 1;
  if (*p == '-') { sign = -1; p++; }
  int val = 0;
  while (*p >= '0' && *p <= '9') {
    val = val * 10 + (*p - '0');
    p++;
  }
  return val * sign;
}

int main(int argc, char **argv) {
  std::string input_path = "/root/nopert-project/chart0.rows.log";
  std::string output_path = "/root/nopert-project/chart0_tu_intervals.txt";
  int num_threads = 32;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--input" && i + 1 < argc) input_path = argv[++i];
    else if (arg == "--output" && i + 1 < argc) output_path = argv[++i];
    else if (arg == "--threads" && i + 1 < argc) num_threads = std::atoi(argv[++i]);
  }

  std::cout << "=== Extracting Identity Tube (TU) Intervals from Chart 0 ===\n";
  std::cout << "Input file:  " << input_path << "\n";
  std::cout << "Output file: " << output_path << "\n";
  std::cout << "Threads:     " << num_threads << "\n";

  const size_t MAX_NODES = 1150000000ULL;
  std::cout << "Allocating " << (MAX_NODES * sizeof(NodeEntry) / (1024 * 1024))
            << " MB for node graph...\n" << std::flush;

  NodeEntry *nodes = (NodeEntry *)mmap(nullptr, MAX_NODES * sizeof(NodeEntry),
                                       PROT_READ | PROT_WRITE,
                                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (nodes == MAP_FAILED) {
    perror("mmap nodes failed");
    return 1;
  }

  int fd = open(input_path.c_str(), O_RDONLY);
  if (fd < 0) {
    perror("Failed to open input file");
    return 1;
  }

  struct stat st;
  if (fstat(fd, &st) != 0) {
    perror("fstat failed");
    return 1;
  }
  size_t file_size = st.st_size;
  std::cout << "File size:   " << (file_size / (1024 * 1024)) << " MB ("
            << (file_size / (1024 * 1024 * 1024)) << " GB)\n" << std::flush;

  const char *file_data = (const char *)mmap(nullptr, file_size, PROT_READ, MAP_SHARED, fd, 0);
  if (file_data == MAP_FAILED) {
    perror("mmap input file failed");
    return 1;
  }
  madvise((void *)file_data, file_size, MADV_WILLNEED);

  std::vector<std::vector<TuRecord>> thread_tu(num_threads);
  std::atomic<uint32_t> global_max_id{0};
  std::atomic<size_t> global_lines_processed{0};

  auto start_time = std::chrono::steady_clock::now();
  std::cout << "Scanning rows log file with " << num_threads << " threads...\n" << std::flush;

  std::vector<std::thread> workers;
  for (int t = 0; t < num_threads; t++) {
    workers.emplace_back([&, t]() {
      size_t chunk_start = (file_size * t) / num_threads;
      size_t chunk_end = (file_size * (t + 1)) / num_threads;

      // Align chunk_start to newline
      if (t > 0) {
        while (chunk_start < chunk_end && file_data[chunk_start - 1] != '\n') {
          chunk_start++;
        }
      }
      // Align chunk_end to newline
      if (t < num_threads - 1) {
        while (chunk_end < file_size && file_data[chunk_end - 1] != '\n') {
          chunk_end++;
        }
      }

      const char *p = file_data + chunk_start;
      const char *end = file_data + chunk_end;
      auto &local_tu = thread_tu[t];
      local_tu.reserve(4096);

      uint32_t local_max_id = 0;
      size_t local_lines = 0;

      while (p < end) {
        const char *nl = (const char *)memchr(p, '\n', end - p);
        if (!nl) nl = end;

        local_lines++;
        char c0 = p[0];
        if (c0 == 'S') {
          char c1 = p[1];
          if ((c1 == 'O' || c1 == 'P') && p[2] == ' ') {
            const char *cur = p + 3;
            uint32_t id = parse_u32(cur);
            parse_i32(cur); // parent (can be -1 for root)
            parse_i32(cur); // depth
            uint32_t ch0 = parse_u32(cur);
            uint32_t ch1 = parse_u32(cur);

            if (ch0 < MAX_NODES) {
              nodes[ch0].parent = id;
              nodes[ch0].info = 0 | (0 << 2);
            }
            if (ch1 < MAX_NODES) {
              nodes[ch1].parent = id;
              nodes[ch1].info = 1 | (0 << 2);
            }
            if (ch1 > local_max_id) local_max_id = ch1;
          } else if (c1 == 'V' && p[2] == ' ') {
            const char *cur = p + 3;
            uint32_t id = parse_u32(cur);
            parse_i32(cur); // parent (can be -1 for root)
            parse_i32(cur); // depth
            uint32_t ch0 = parse_u32(cur);
            uint32_t ch1 = parse_u32(cur);
            uint32_t ch2 = parse_u32(cur);
            uint32_t ch3 = parse_u32(cur);

            if (ch0 < MAX_NODES) { nodes[ch0].parent = id; nodes[ch0].info = 0 | (1 << 2); }
            if (ch1 < MAX_NODES) { nodes[ch1].parent = id; nodes[ch1].info = 1 | (1 << 2); }
            if (ch2 < MAX_NODES) { nodes[ch2].parent = id; nodes[ch2].info = 2 | (1 << 2); }
            if (ch3 < MAX_NODES) { nodes[ch3].parent = id; nodes[ch3].info = 3 | (1 << 2); }
            if (ch3 > local_max_id) local_max_id = ch3;
          }
        } else if (c0 == 'T' && p[1] == 'U' && p[2] == ' ') {
          const char *cur = p + 3;
          uint32_t id = parse_u32(cur);
          uint32_t parent = parse_u32(cur);
          int depth = parse_i32(cur);
          while (*cur == ' ' || *cur == '\t') cur++;
          double radius = std::strtod(cur, nullptr);

          local_tu.push_back({id, parent, depth, radius});
          if (id > local_max_id) local_max_id = id;
        }

        p = (nl < end) ? nl + 1 : end;
      }

      global_lines_processed.fetch_add(local_lines, std::memory_order_relaxed);
      uint32_t cur_max = global_max_id.load(std::memory_order_relaxed);
      while (local_max_id > cur_max &&
             !global_max_id.compare_exchange_weak(cur_max, local_max_id, std::memory_order_relaxed)) {}
    });
  }

  for (auto &w : workers) w.join();

  munmap((void *)file_data, file_size);
  close(fd);

  std::vector<TuRecord> tu_records;
  for (auto &lt : thread_tu) {
    tu_records.insert(tu_records.end(), lt.begin(), lt.end());
  }

  // Sort TU records by node ID
  std::sort(tu_records.begin(), tu_records.end(), [](const TuRecord &a, const TuRecord &b) {
    return a.id < b.id;
  });

  auto parse_time = std::chrono::steady_clock::now();
  double elapsed = std::chrono::duration<double>(parse_time - start_time).count();
  std::cout << "\nScanning complete!\n";
  std::cout << "Total lines:        " << global_lines_processed.load() << "\n";
  std::cout << "Total TU rows:      " << tu_records.size() << "\n";
  std::cout << "Max node ID:        " << global_max_id.load() << "\n";
  std::cout << "Time elapsed:       " << std::fixed << std::setprecision(2) << elapsed << "s\n\n";

  // Reconstruct 5D intervals
  CayleyBoxD root_box;
  root_box.center = {0.0, 0.0, 0.0};
  root_box.radii = {1.0, 1.0, 1.0 / 3.0};

  ProjectiveTriangleD wedge_root;
  wedge_root.corners[0] = {1.0, 0.0, 0.0};
  wedge_root.corners[1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  wedge_root.corners[2] = {0.0, 0.0, 1.0};
  auto sub_wedges = wedge_root.Subdivide();

  std::cout << "Reconstructing 5D search space intervals for " << tu_records.size()
            << " TU leaves...\n" << std::flush;

  std::ofstream out(output_path);
  if (!out.is_open()) {
    std::cerr << "Failed to open output file " << output_path << "\n";
    return 1;
  }

  out << "# TU Certificates in Chart 0\n";
  out << "# Total count: " << tu_records.size() << "\n";
  out << "# Format:\n";
  out << "# 1:id 2:parent 3:depth 4:requested_radius "
      << "5:cx 6:cy 7:cz 8:rx 9:ry 10:rz "
      << "11:xmin 12:xmax 13:ymin 14:ymax 15:zmin 16:zmax 17:cayley_max_norm "
      << "18:subwedge 19:view_path 20:view_depth "
      << "21:v0x 22:v0y 23:v0z 24:v1x 25:v1y 26:v1z 27:v2x 28:v2y 29:v2z "
      << "30:cent_x 31:cent_y 32:cent_z 33:angular_diam\n";
  out << std::setprecision(17);

  size_t valid_reconstructed = 0;
  for (const auto &tu : tu_records) {
    std::vector<std::pair<int, int>> path;
    uint32_t curr = tu.id;
    bool path_ok = true;

    while (curr != 0) {
      if (curr >= MAX_NODES) { path_ok = false; break; }
      uint32_t p = nodes[curr].parent;
      uint8_t info = nodes[curr].info;
      int child_idx = info & 3;
      int split_type = (info >> 2) & 1;
      path.push_back({split_type, child_idx});
      curr = p;
    }

    if (!path_ok || path.empty()) {
      std::cerr << "Warning: Could not trace path for TU node " << tu.id << "\n";
      continue;
    }

    std::reverse(path.begin(), path.end());

    if (path[0].first != 1) {
      std::cerr << "Warning: First split for TU node " << tu.id << " is not view split\n";
      continue;
    }

    int subwedge = path[0].second;
    ProjectiveTriangleD tri = sub_wedges[subwedge];
    CayleyBoxD box = root_box;
    std::string view_path = "";
    int view_depth = 0;

    for (size_t s = 1; s < path.size(); s++) {
      int split_type = path[s].first;
      int child_idx = path[s].second;
      if (split_type == 0) {
        int widest = box.WidestAxis();
        auto [b0, b1] = box.Split(widest);
        box = (child_idx == 0) ? b0 : b1;
      } else {
        auto sub = tri.Subdivide();
        tri = sub[child_idx];
        view_path += std::to_string(child_idx);
        view_depth++;
      }
    }

    double mx = std::abs(box.center.x) + box.radii.x;
    double my = std::abs(box.center.y) + box.radii.y;
    double mz = std::abs(box.center.z) + box.radii.z;
    double cayley_max_norm = 2.0 * std::sqrt(mx * mx + my * my + mz * mz);

    Vec3D cent = tri.CentroidUnit();
    double diam = tri.AngularDiameter();

    out << tu.id << " "
        << tu.parent << " "
        << tu.depth << " "
        << tu.radius << " "
        << box.center.x << " " << box.center.y << " " << box.center.z << " "
        << box.radii.x << " " << box.radii.y << " " << box.radii.z << " "
        << (box.center.x - box.radii.x) << " " << (box.center.x + box.radii.x) << " "
        << (box.center.y - box.radii.y) << " " << (box.center.y + box.radii.y) << " "
        << (box.center.z - box.radii.z) << " " << (box.center.z + box.radii.z) << " "
        << cayley_max_norm << " "
        << subwedge << " "
        << (view_path.empty() ? "-" : view_path) << " "
        << view_depth << " "
        << tri.corners[0].x << " " << tri.corners[0].y << " " << tri.corners[0].z << " "
        << tri.corners[1].x << " " << tri.corners[1].y << " " << tri.corners[1].z << " "
        << tri.corners[2].x << " " << tri.corners[2].y << " " << tri.corners[2].z << " "
        << cent.x << " " << cent.y << " " << cent.z << " "
        << diam << "\n";

    valid_reconstructed++;
  }

  out.close();
  munmap(nodes, MAX_NODES * sizeof(NodeEntry));

  std::cout << "Successfully exported " << valid_reconstructed << " TU intervals to "
            << output_path << "!\n";
  return 0;
}
