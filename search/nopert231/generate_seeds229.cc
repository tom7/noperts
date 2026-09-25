#include <cstdio>
#include <cmath>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <iomanip>
#include "yocto-math.h"
#include "ruperts-util.h"
#include "geom/hull-2d.h"
#include "lib229.h"
#include "solutions.h"
#include "base/logging.h"
#include "arcfour.h"

struct CellInfo {
  uint64_t id;
  int chart;
  vec3 c;
  vec3 r;
  vec3 v0, v1, v2;
  std::string source;
};

struct SeedCandidate {
  quat4 q_outer;
  vec3 w_inner;
  vec2 t_inner;
  double clearance;
  std::string source;
  uint64_t cell_id;
};

static std::vector<CellInfo> LoadCells(const std::string &path, const std::string &source) {
  std::vector<CellInfo> cells;
  std::ifstream f(path);
  if (!f.is_open()) {
    std::printf("Warning: could not open %s\n", path.c_str());
    return cells;
  }
  std::string line;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    CellInfo cell;
    uint64_t parent_id;
    int depth, box_depth, view_depth;
    double best_margin;
    if (iss >> cell.id >> parent_id >> depth >> box_depth >> view_depth
            >> cell.chart >> cell.c.x >> cell.c.y >> cell.c.z
            >> cell.r.x >> cell.r.y >> cell.r.z
            >> cell.v0.x >> cell.v0.y >> cell.v0.z
            >> cell.v1.x >> cell.v1.y >> cell.v1.z
            >> cell.v2.x >> cell.v2.y >> cell.v2.z
            >> best_margin) {
      cell.source = source;
      cells.push_back(cell);
    }
  }
  std::printf("Loaded %zu cells from %s (%s)\n", cells.size(), path.c_str(), source.c_str());
  return cells;
}

static inline quat4 RotationVectorToQuat(const vec3 &w) {
  const double theta = yocto::length(w);
  if (theta < 1e-12) {
    return quat4{0.0, 0.0, 0.0, 1.0};
  }
  const vec3 axis = w / theta;
  const double s = sin(0.5 * theta);
  const double c = cos(0.5 * theta);
  return yocto::normalize(quat4{axis.x * s, axis.y * s, axis.z * s, c});
}

static void ProjectVertices(const frame3 &f,
                            const std::vector<vec3> &verts,
                            std::vector<vec2> &out_pts) {
  out_pts.resize(verts.size());
  for (size_t i = 0; i < verts.size(); i++) {
    const vec3 &v = verts[i];
    out_pts[i] = vec2{
      f.x.x * v.x + f.y.x * v.y + f.z.x * v.z,
      f.x.y * v.x + f.y.y * v.y + f.z.y * v.z
    };
  }
}

int main() {
  Polyhedron target = GetPolyhedron229();
  auto opoly = PolyhedronFromVertices(target.vertices, "nopert_229");
  if (opoly.has_value()) target = std::move(opoly.value());
  std::printf("Polyhedron: %s with %zu vertices\n", target.name.c_str(), target.vertices.size());

  std::vector<CellInfo> all_cells;
  auto c_diff = LoadCells("chart0.difficult", "canyon");
  all_cells.insert(all_cells.end(), c_diff.begin(), c_diff.end());

  auto c_tu = LoadCells("/root/nopert-project/chart0.tu-difficult", "tu-difficult");
  all_cells.insert(all_cells.end(), c_tu.begin(), c_tu.end());

  std::printf("Total cells to sample from: %zu (canyon: %zu, tu-difficult: %zu)\n",
              all_cells.size(), c_diff.size(), c_tu.size());


  ArcFour rc("generate_seeds229");
  std::vector<SeedCandidate> candidates;
  candidates.reserve(100000);

  std::vector<vec2> outer_verts(target.vertices.size());
  std::vector<vec2> inner_verts(target.vertices.size());

  auto EvaluatePoint = [&](const vec3 &w_cayley, const vec3 &v_view,
                           const std::string &source, uint64_t cell_id) {
    vec3 norm_v = yocto::normalize(v_view);
    vec3 right;
    if (std::abs(norm_v.z) < 0.9) {
      right = yocto::normalize(yocto::cross(norm_v, vec3{0, 0, 1}));
    } else {
      right = yocto::normalize(yocto::cross(norm_v, vec3{1, 0, 0}));
    }
    vec3 up = yocto::normalize(yocto::cross(right, norm_v));
    frame3 f;
    f.x = vec3{right.x, up.x, -norm_v.x};
    f.y = vec3{right.y, up.y, -norm_v.y};
    f.z = vec3{right.z, up.z, -norm_v.z};
    f.o = vec3{0, 0, 0};
    auto [q_outer, _] = UnpackFrame(f);

    double w_len = yocto::length(w_cayley);
    vec3 w_inner = {0, 0, 0};
    if (w_len > 1e-15) {
      double theta = 2.0 * std::atan(w_len);
      vec3 axis_world = w_cayley / w_len;
      vec3 axis_cam = {
        yocto::dot(axis_world, right),
        yocto::dot(axis_world, up),
        yocto::dot(axis_world, -norm_v)
      };
      w_inner = axis_cam * theta;
    }

    frame3 fo = yocto::rotation_frame(q_outer);
    ProjectVertices(fo, target.vertices, outer_verts);
    std::vector<int> ho = Hull2D::QuickHull(outer_verts);
    if (ho.size() < 3) return;
    auto eo = GetHullEdges(outer_verts, ho);

    quat4 d_qi = RotationVectorToQuat(w_inner);
    quat4 qi = yocto::normalize(d_qi * q_outer);
    frame3 fi = yocto::rotation_frame(qi);
    ProjectVertices(fi, target.vertices, inner_verts);

    Clearance2D cl = MaximizeClearance2D(eo, inner_verts);
    candidates.push_back(SeedCandidate{
      .q_outer = q_outer,
      .w_inner = w_inner,
      .t_inner = cl.translation,
      .clearance = cl.clearance,
      .source = source,
      .cell_id = cell_id
    });
  };

  for (const auto &cell : all_cells) {
    // 1. Box center + triangle centroid
    vec3 v_cent = (cell.v0 + cell.v1 + cell.v2) / 3.0;
    EvaluatePoint(cell.c, v_cent, cell.source, cell.id);

    // 2. Cayley corners x triangle vertices
    for (double dx : {-cell.r.x, cell.r.x}) {
      for (double dy : {-cell.r.y, cell.r.y}) {
        for (double dz : {-cell.r.z, cell.r.z}) {
          vec3 w_corner = cell.c + vec3{dx, dy, dz};
          EvaluatePoint(w_corner, cell.v0, cell.source, cell.id);
          EvaluatePoint(w_corner, cell.v1, cell.source, cell.id);
          EvaluatePoint(w_corner, cell.v2, cell.source, cell.id);
          EvaluatePoint(w_corner, v_cent, cell.source, cell.id);
        }
      }
    }

    // 3. Dense sampling for canyon and tu-difficult cells
    int extra_samples = (cell.source == "canyon") ? 5000 : 2000;


    // Origin sampling if cell contains origin
    bool contains_origin = (cell.c.x - cell.r.x <= 0 && cell.c.x + cell.r.x >= 0 &&
                            cell.c.y - cell.r.y <= 0 && cell.c.y + cell.r.y >= 0 &&
                            cell.c.z - cell.r.z <= 0 && cell.c.z + cell.r.z >= 0);
    if (contains_origin) {
      EvaluatePoint(vec3{0, 0, 0}, v_cent, cell.source + "_origin", cell.id);
      EvaluatePoint(vec3{0, 0, 0}, cell.v0, cell.source + "_origin", cell.id);
      EvaluatePoint(vec3{0, 0, 0}, cell.v1, cell.source + "_origin", cell.id);
      EvaluatePoint(vec3{0, 0, 0}, cell.v2, cell.source + "_origin", cell.id);

      // Tube radius boundary samples
      for (double tube_r : {1e-7, 1e-6, 1e-5, 1e-4}) {
        for (int step = 0; step < 16; step++) {
          double u1 = RandDouble(&rc);
          double u2 = RandDouble(&rc);
          double z = 1.0 - 2.0 * u1;
          double r_xy = std::sqrt(std::max(0.0, 1.0 - z * z));
          double phi = 2.0 * M_PI * u2;
          vec3 w_sphere = tube_r * vec3{r_xy * cos(phi), r_xy * sin(phi), z};
          EvaluatePoint(w_sphere, v_cent, cell.source + "_tuber", cell.id);
        }
      }
    }

    // Canyon critical ray sampling
    if (cell.source == "canyon") {
      vec3 ray_dir = yocto::normalize(vec3{1.0, -1.0, -2.0});
      for (double ray_r = 1e-6; ray_r <= 1e-3; ray_r *= 1.5) {
        vec3 w_ray = ray_r * ray_dir;
        EvaluatePoint(w_ray, v_cent, cell.source + "_ray", cell.id);
        EvaluatePoint(w_ray, cell.v0, cell.source + "_ray", cell.id);
        EvaluatePoint(w_ray, cell.v1, cell.source + "_ray", cell.id);
        EvaluatePoint(w_ray, cell.v2, cell.source + "_ray", cell.id);
      }
    }

    // Random interior samples
    for (int s = 0; s < extra_samples; s++) {
      double rx = (RandDouble(&rc) * 2.0 - 1.0) * cell.r.x;
      double ry = (RandDouble(&rc) * 2.0 - 1.0) * cell.r.y;
      double rz = (RandDouble(&rc) * 2.0 - 1.0) * cell.r.z;
      vec3 w_samp = cell.c + vec3{rx, ry, rz};

      // Random barycentric inside view triangle
      double u1 = RandDouble(&rc);
      double u2 = RandDouble(&rc);
      if (u1 + u2 > 1.0) {
        u1 = 1.0 - u1;
        u2 = 1.0 - u2;
      }
      double u0 = 1.0 - u1 - u2;
      vec3 v_samp = u0 * cell.v0 + u1 * cell.v1 + u2 * cell.v2;

      EvaluatePoint(w_samp, v_samp, cell.source, cell.id);
    }
  }

  std::printf("Generated and evaluated %zu candidates.\n", candidates.size());

  // Sort descending by clearance (highest clearance / closest to 0 first!)
  std::sort(candidates.begin(), candidates.end(),
            [](const SeedCandidate &a, const SeedCandidate &b) {
              return a.clearance > b.clearance;
            });

  std::printf("Top 10 highest clearances found:\n");
  for (int i = 0; i < std::min<int>(10, candidates.size()); i++) {
    const auto &c = candidates[i];
    std::printf("  [%d] clearance = %+.17g | cell #%lu (%s) | |w| = %.6g\n",
                i, c.clearance, c.cell_id, c.source.c_str(), yocto::length(c.w_inner));
  }

  // Deduplicate points that are extremely close in (q_outer, w_inner)
  std::vector<SeedCandidate> unique_seeds;
  unique_seeds.reserve(4096);

  for (const auto &cand : candidates) {
    vec4 v_cand = {cand.q_outer.x, cand.q_outer.y, cand.q_outer.z, cand.q_outer.w};
    bool is_dup = false;
    for (const auto &kept : unique_seeds) {
      vec4 v_kept = {kept.q_outer.x, kept.q_outer.y, kept.q_outer.z, kept.q_outer.w};
      double dq = std::min(yocto::length(v_cand - v_kept),
                           yocto::length(v_cand + v_kept));
      double dw = yocto::length(cand.w_inner - kept.w_inner);
      if (dq < 5e-5 && dw < 5e-5) {
        is_dup = true;
        break;
      }
    }

    if (!is_dup) {
      unique_seeds.push_back(cand);
      if (unique_seeds.size() == 4096) break;
    }
  }

  std::printf("Selected %zu unique risky seed points (target: 4096).\n", unique_seeds.size());

  // Breakdown of sources in unique_seeds
  int count_canyon = 0, count_tu = 0;
  for (const auto &s : unique_seeds) {
    if (s.source.find("canyon") != std::string::npos) count_canyon++;
    else count_tu++;
  }
  std::printf("Source breakdown: canyon: %d, tu-difficult: %d\n", count_canyon, count_tu);
  std::printf("Clearance range in seeds: [%.17g, %.17g]\n",
              unique_seeds.back().clearance, unique_seeds.front().clearance);


  // Write out to seed-points229.txt
  std::ofstream out("seed-points229.txt");
  CHECK(out.is_open());
  out << std::setprecision(17);
  for (const auto &s : unique_seeds) {
    out << s.q_outer.x << " " << s.q_outer.y << " " << s.q_outer.z << " " << s.q_outer.w << " "
        << s.w_inner.x << " " << s.w_inner.y << " " << s.w_inner.z << " "
        << s.t_inner.x << " " << s.t_inner.y << "\n";
  }
  out.close();
  std::printf("Successfully wrote 4096 seeds to seed-points229.txt!\n");

  return 0;
}
