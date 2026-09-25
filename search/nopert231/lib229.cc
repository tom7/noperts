#include "lib229.h"

#include <CL/cl.h>
#include <CL/cl_platform.h>
#include <algorithm>
#include <array>
#include <atomic>
#include <cctype>
#include <charconv>
#include <cmath>
#include <condition_variable>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <format>
#include <fstream>
#include <functional>
#include <iterator>
#include <list>
#include <memory>
#include <mutex>
#include <numbers>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>

#include "ansi.h"
#include "atomic-util.h"
#include "base/print.h"
#include "geom/hull-2d.h"
#include "geom/polyhedra.h"
#include "nopert229.h"
#include "opencl/clutil.h"
#include "periodically.h"
#include "ruperts-util.h"
#include "solutions.h"
#include "status-bar.h"
#include "threadutil.h"
#include "timer.h"
#include "tubetree229.h"
#include "util.h"
#include "yocto-math.h"

DECLARE_COUNTERS(evaluated_count, certified_count, pruned_count, split_count,
                 ctr_built_triangles, ctr_loops, ctr_cpu, ctr_esc_certified);
DECLARE_COUNTERS(difficult_count);

static CL *cl = nullptr;
static std::atomic<bool> sigint_received{false};

static void SigHandler(int) {
  sigint_received.store(true);
}

void InstallSignalHandlers() {
  std::signal(SIGINT, SigHandler);
  std::signal(SIGTERM, SigHandler);
}

bool SigIntReceived() {
  return sigint_received.load();
}

void SetSigInt() {
  sigint_received.store(true);
}

std::vector<DifficultCell> ReadDifficultFile(const std::string &path) {
  std::vector<DifficultCell> cells;
  std::ifstream in(path);
  if (!in.is_open()) return cells;
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    DifficultCell cell;
    if (iss >> cell.id >> cell.parent_id >> cell.depth >> cell.box_depth
            >> cell.view_depth >> cell.chart
            >> cell.c.x >> cell.c.y >> cell.c.z
            >> cell.r.x >> cell.r.y >> cell.r.z
            >> cell.v[0].x >> cell.v[0].y >> cell.v[0].z
            >> cell.v[1].x >> cell.v[1].y >> cell.v[1].z
            >> cell.v[2].x >> cell.v[2].y >> cell.v[2].z
            >> cell.best_margin) {
      cells.push_back(cell);
    }
  }
  return cells;
}

bool WriteDifficultFile(const std::string &path,
                        const std::vector<DifficultCell> &cells) {
  std::string tmp_path = path + ".tmp";
  std::ofstream out(tmp_path);
  if (!out.is_open())
    return false;
  out << "# id parent_id depth box_depth view_depth chart "
         "cx cy cz rx ry rz "
         "v0x v0y v0z v1x v1y v1z v2x v2y v2z "
         "best_margin\n";
  for (const auto &cell : cells) {
    out << cell.ToString();
  }
  out.close();
  std::error_code ec;
  std::filesystem::rename(tmp_path, path, ec);
  return !ec;
}

size_t g_max_triangle_cache_size = 20480;
static std::mutex g_triangle_cache_mutex;
static std::list<std::shared_ptr<const TrianglePool>> g_triangle_lru_list;
static std::unordered_map<uint64_t, std::list<std::shared_ptr<const TrianglePool>>::iterator>
g_triangle_cache;

double ComputeWeightedDefectUpper(const ProjectiveTriangle &tri,
                                  const std::vector<GpuContact> &contacts,
                                  int c0, int c1, int c2,
                                  const vec3 w_coeff[3]) {
  double total = 0.0;
  const double error = 1e-9;
  const int c_indices[3] = {c0, c1, c2};
  for (int i = 0; i < 3; i++) {
    int sel = contacts[c_indices[i]].vertex;
    vec3 edge = {contacts[c_indices[i]].edge[0],
                 contacts[c_indices[i]].edge[1],
                 contacts[c_indices[i]].edge[2]};
    double w_vals[3] = {
      yocto::dot(tri.corners[0], w_coeff[i]) + error,
      yocto::dot(tri.corners[1], w_coeff[i]) + error,
      yocto::dot(tri.corners[2], w_coeff[i]) + error
    };
    double upper = 0.0;
    for (int k = 0; k < NUM_VERTICES; k++) {
      if (k == sel) continue;
      vec3 delta = {
        VERTICES[k][0] - VERTICES[sel][0],
        VERTICES[k][1] - VERTICES[sel][1],
        VERTICES[k][2] - VERTICES[sel][2]
      };
      vec3 s_coeff = yocto::cross(edge, delta);
      double s_vals[3] = {
        yocto::dot(tri.corners[0], s_coeff) + error,
        yocto::dot(tri.corners[1], s_coeff) + error,
        yocto::dot(tri.corners[2], s_coeff) + error
      };
      for (int a = 0; a < 3; a++) {
        for (int b = 0; b < 3; b++) {
          double ctrl = 0.5 * (w_vals[a] * s_vals[b] + w_vals[b] * s_vals[a]);
          if (ctrl > upper) upper = ctrl;
        }
      }
    }
    total += upper;
  }
  return total;
}


std::shared_ptr<const TrianglePool> BuildTrianglePool(
    const ProjectiveTriangle &tri, int cone_samples, uint64_t id) {
  ctr_built_triangles++;
  auto pool = std::make_shared<TrianglePool>();
  pool->id = id;
  vec3 view = tri.Centroid();
  double len = yocto::length(view);
  if (len < 1e-12) return pool;
  vec3 uview = view / len;

  // Project vertices to 2D along view direction.
  int min_axis = 0;
  for (int a = 1; a < 3; a++) {
    if (std::abs(uview[a]) < std::abs(uview[min_axis])) min_axis = a;
  }
  vec3 axis = {0, 0, 0};
  axis[min_axis] = 1.0;
  vec3 right = yocto::normalize(yocto::cross(uview, axis));
  vec3 up = yocto::cross(uview, right);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int i = 0; i < NUM_VERTICES; i++) {
    vec3 v = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
    projected[i] = {yocto::dot(v, right), yocto::dot(v, up)};
  }

  std::vector<int> hull = Hull2D::GrahamScan(projected);
  int H = hull.size();
  if (H < 3) return pool;

  // Build silhouette edge contacts interpolating adjacent edges.
  std::vector<GpuContact> valid_contacts;
  for (int i = 0; i < H; i++) {
    int curr = hull[i];
    int next = hull[(i + 1) % H];
    int prev = hull[(i - 1 + H) % H];

    vec3 v_curr = {VERTICES[curr][0], VERTICES[curr][1], VERTICES[curr][2]};
    vec3 v_next = {VERTICES[next][0], VERTICES[next][1], VERTICES[next][2]};
    vec3 v_prev = {VERTICES[prev][0], VERTICES[prev][1], VERTICES[prev][2]};

    vec3 first = v_prev - v_curr;
    vec3 second = v_curr - v_next;

    for (int s = 0; s <= cone_samples + 1; s++) {
      double lam = (double)s / (cone_samples + 1.0);
      vec3 e = lam * first + (1.0 - lam) * second;

      double max_upper = 0.0;
      double min_upper = 1e30;
      for (int k = 0; k < NUM_VERTICES; k++) {
        if (k == curr) continue;
        vec3 delta = {VERTICES[k][0] - VERTICES[curr][0],
                      VERTICES[k][1] - VERTICES[curr][1],
                      VERTICES[k][2] - VERTICES[curr][2]};
        vec3 coeff = yocto::cross(e, delta);
        if (yocto::length(coeff) < 1e-12) continue;
        double upper = std::max({yocto::dot(tri.corners[0], coeff),
                                 yocto::dot(tri.corners[1], coeff),
                                 yocto::dot(tri.corners[2], coeff)});
        if (upper > max_upper) max_upper = upper;
        if (upper < min_upper) min_upper = upper;
      }
      if (min_upper >= 0.0) {
        // Not a valid silhouette support direction.
        continue;
      }

      // Check for duplicate contact direction already in valid_contacts
      vec3 e_norm = yocto::normalize(e);
      bool duplicate = false;
      for (const auto &ex : valid_contacts) {
        vec3 ex_norm = yocto::normalize(
            vec3{ex.edge[0], ex.edge[1], ex.edge[2]});
        if (yocto::dot(e_norm, ex_norm) > 1.0 - 1e-9) {
          duplicate = true;
          break;
        }
      }
      if (duplicate) continue;

      GpuContact c;
      c.vertex = curr;
      c.edge[0] = e.x; c.edge[1] = e.y; c.edge[2] = e.z;
      c.defect = std::max(0.0, max_upper);
      valid_contacts.push_back(c);
    }
  }

  // Add multi-vertex candidate contacts for non-hull vertices whose support defect
  // is small (<= 0.002). This equips the 5D search with multi-vertex contact bases
  // to cover deep singular corridors near the identity tube boundary.
  static constexpr int POLY_3D_EDGES[54][2] = {
    {0, 1}, {0, 4}, {0, 16}, {0, 17},
    {1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 17}, {1, 18},
    {2, 3}, {2, 5}, {2, 6}, {2, 7},
    {3, 7}, {3, 18}, {3, 19},
    {4, 5}, {4, 8}, {4, 12}, {4, 16},
    {5, 6}, {5, 8}, {5, 9},
    {6, 7}, {6, 9}, {6, 11},
    {7, 11}, {7, 15}, {7, 19},
    {8, 9}, {8, 12},
    {9, 10}, {9, 11}, {9, 12}, {9, 13},
    {10, 11}, {10, 13}, {10, 15},
    {11, 15},
    {12, 13}, {12, 16},
    {13, 14}, {13, 15}, {13, 16}, {13, 17},
    {14, 15}, {14, 17}, {14, 19},
    {15, 19},
    {16, 17},
    {17, 18}, {17, 19},
    {18, 19},
  };
  std::vector<int> adj[NUM_VERTICES];
  for (int e_idx = 0; e_idx < 54; e_idx++) {
    int u = POLY_3D_EDGES[e_idx][0];
    int w = POLY_3D_EDGES[e_idx][1];
    adj[u].push_back(w);
    adj[w].push_back(u);
  }
  std::unordered_set<int> hull_set(hull.begin(), hull.end());
  for (int v = 0; v < NUM_VERTICES; v++) {
    if (hull_set.count(v)) continue;
    int deg = adj[v].size();
    for (int i = 0; i < deg; i++) {
      for (int j = 0; j < deg; j++) {
        if (i == j) continue;
        int p = adj[v][i];
        int n = adj[v][j];
        vec3 v_v = {VERTICES[v][0], VERTICES[v][1], VERTICES[v][2]};
        vec3 v_p = {VERTICES[p][0], VERTICES[p][1], VERTICES[p][2]};
        vec3 v_n = {VERTICES[n][0], VERTICES[n][1], VERTICES[n][2]};
        vec3 first = v_p - v_v;
        vec3 second = v_v - v_n;
        for (int s = 0; s <= cone_samples + 1; s++) {
          double lam = (double)s / (cone_samples + 1.0);
          vec3 e = lam * first + (1.0 - lam) * second;
          double max_upper = 0.0;
          double min_upper = 1e30;
          for (int k = 0; k < NUM_VERTICES; k++) {
            if (k == v) continue;
            vec3 delta = {VERTICES[k][0] - VERTICES[v][0],
                          VERTICES[k][1] - VERTICES[v][1],
                          VERTICES[k][2] - VERTICES[v][2]};
            vec3 coeff = yocto::cross(e, delta);
            if (yocto::length(coeff) < 1e-12) continue;
            double upper = std::max({yocto::dot(tri.corners[0], coeff),
                                     yocto::dot(tri.corners[1], coeff),
                                     yocto::dot(tri.corners[2], coeff)});
            if (upper > max_upper) max_upper = upper;
            if (upper < min_upper) min_upper = upper;
          }
          if (min_upper >= 0.0) continue;
          if (max_upper > 0.002) continue;

          vec3 e_norm = yocto::normalize(e);
          bool duplicate = false;
          for (const auto &ex : valid_contacts) {
            vec3 ex_norm = yocto::normalize(
                vec3{ex.edge[0], ex.edge[1], ex.edge[2]});
            if (yocto::dot(e_norm, ex_norm) > 1.0 - 1e-9) {
              duplicate = true;
              break;
            }
          }
          if (duplicate) continue;
          if (valid_contacts.size() >= MAX_GPU_CONTACTS) break;

          GpuContact c;
          c.vertex = v;
          c.edge[0] = e.x; c.edge[1] = e.y; c.edge[2] = e.z;
          c.defect = std::max(0.0, max_upper);
          valid_contacts.push_back(c);
        }
      }
    }
  }

  pool->contacts = std::move(valid_contacts);
  int C = pool->contacts.size();
  CHECK_LE(C, MAX_GPU_CONTACTS)
      << "Triangle pool has " << C << " contacts, exceeding MAX_GPU_CONTACTS ("
      << MAX_GPU_CONTACTS << ")";

  pool->gpu_triples.reserve(C * (C - 1) * (C - 2) / 6);


  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        vec3 e0 = {
          pool->contacts[i].edge[0],
          pool->contacts[i].edge[1],
          pool->contacts[i].edge[2],
        };
        vec3 e1 = {
          pool->contacts[j].edge[0],
          pool->contacts[j].edge[1],
          pool->contacts[j].edge[2],
        };
        vec3 e2 = {
          pool->contacts[k].edge[0],
          pool->contacts[k].edge[1],
          pool->contacts[k].edge[2],
        };

        vec3 coeff0 = yocto::cross(e1, e2);
        vec3 coeff1 = yocto::cross(e2, e0);
        vec3 coeff2 = yocto::cross(e0, e1);

        double p0 = yocto::dot(view, coeff0);
        double p1 = yocto::dot(view, coeff1);
        double p2 = yocto::dot(view, coeff2);

        int ci = i, cj = j, ck = k;
        if (p0 < 0.0 && p1 < 0.0 && p2 < 0.0) {
          std::swap(cj, ck);
          std::swap(e1, e2);
          coeff0 = yocto::cross(e1, e2);
          coeff1 = yocto::cross(e2, e0);
          coeff2 = yocto::cross(e0, e1);
          p0 = yocto::dot(view, coeff0);
          p1 = yocto::dot(view, coeff1);
          p2 = yocto::dot(view, coeff2);
        }

        if (p0 <= 1e-9 || p1 <= 1e-9 || p2 <= 1e-9) continue;

        // Check corner non-negativity across triangle
        double w0_min = std::min({yocto::dot(tri.corners[0], coeff0),
                                  yocto::dot(tri.corners[1], coeff0),
                                  yocto::dot(tri.corners[2], coeff0)});
        double w1_min = std::min({yocto::dot(tri.corners[0], coeff1),
                                  yocto::dot(tri.corners[1], coeff1),
                                  yocto::dot(tri.corners[2], coeff1)});
        double w2_min = std::min({yocto::dot(tri.corners[0], coeff2),
                                  yocto::dot(tri.corners[1], coeff2),
                                  yocto::dot(tri.corners[2], coeff2)});
        // Ensure the view cone triangle corners are strictly interior to the
        // contact cone. We test against a small positive epsilon (1e-11) rather
        // than 0.0 because Lean subtracts supportError = 6/10^15 (accounting
        // for algebraic vs rational vertex differences) when computing
        // weightLower = min_c(w) - supportError >= 0. Testing against <= 1e-11
        // safely eliminates exact-boundary triples (which evaluate to 0.0 in
        // exact arithmetic or +-1e-15 float noise) and leaves ~1600x headroom
        // above supportError, guaranteeing weightLower > 0 in Lean.
        // Note: this epsilon applies only to the angular view weights, not the
        // physical clearance margins between the polyhedra.
        if (w0_min <= 1e-11 || w1_min <= 1e-11 || w2_min <= 1e-11) continue;

        GpuTriple gt;
        gt.c0 = (uint8_t)ci;
        gt.c1 = (uint8_t)cj;
        gt.c2 = (uint8_t)ck;
        std::memset(gt._pad, 0, sizeof(gt._pad));

        vec3 w_coeffs[3] = {coeff0, coeff1, coeff2};
        gt.weighted_defect_upper =
          ComputeWeightedDefectUpper(tri, pool->contacts, ci, cj, ck, w_coeffs);
        pool->gpu_triples.push_back(gt);
      }
    }
  }

  pool->gpu_triples.shrink_to_fit();
  return pool;
}


std::shared_ptr<const TrianglePool>
GetTrianglePool(const ProjectiveTriangle &tri, int cone_samples) {
  const uint64_t h =
      HashTriangle(tri) ^ (uint64_t(cone_samples) * 0x9e3779b97f4a7c15ULL);
  {
    MutexLock ml(&g_triangle_cache_mutex);
    auto it = g_triangle_cache.find(h);
    if (it != g_triangle_cache.end()) {
      g_triangle_lru_list.splice(g_triangle_lru_list.begin(),
                                 g_triangle_lru_list, it->second);
      return *(it->second);
    }
  }
  auto pool = BuildTrianglePool(tri, cone_samples, h);
  {
    MutexLock ml(&g_triangle_cache_mutex);
    auto it = g_triangle_cache.find(h);
    if (it != g_triangle_cache.end()) {
      g_triangle_lru_list.splice(g_triangle_lru_list.begin(),
                                 g_triangle_lru_list, it->second);
      return *(it->second);
    }
    if (g_triangle_cache.size() >= g_max_triangle_cache_size) {
      auto oldest = std::prev(g_triangle_lru_list.end());
      g_triangle_cache.erase((*oldest)->id);
      g_triangle_lru_list.pop_back();
    }
    g_triangle_lru_list.push_front(pool);
    g_triangle_cache[h] = g_triangle_lru_list.begin();
    return pool;
  }
}

#if defined(__AVX2__) && defined(__FMA__)
#include <immintrin.h>

// Stores exactly 3 doubles from the lower 3 lanes of a 4-wide __m256d vector.
static inline void Store3(double *dst, __m256d v) {
  _mm_storeu_pd(dst, _mm256_castpd256_pd128(v));
  _mm_store_sd(dst + 2, _mm256_extractf128_pd(v, 1));
}

double Bernstein27Min(const double C[10],
                     double lx, double ly, double lz,
                     double wx, double wy, double wz) {
  double a0 = (C[0] + C[1] * lx + C[2] * ly + C[3] * lz + C[4] * lx * lx +
               C[5] * lx * ly + C[6] * lx * lz + C[7] * ly * ly +
               C[8] * ly * lz + C[9] * lz * lz);
  double ax = wx * (C[1] + 2.0 * C[4] * lx + C[5] * ly + C[6] * lz);
  double ay = wy * (C[2] + C[5] * lx + 2.0 * C[7] * ly + C[8] * lz);
  double az = wz * (C[3] + C[6] * lx + C[8] * ly + 2.0 * C[9] * lz);
  double axx = C[4] * wx * wx, ayy = C[7] * wy * wy, azz = C[9] * wz * wz;
  double axy = C[5] * wx * wy, axz = C[6] * wx * wz, ayz = C[8] * wy * wz;

  const __m256d vk_mult = _mm256_set_pd(0.0, 2.0, 1.0, 0.0);
  const __m256d vk2_mask = _mm256_set_pd(0.0, 1.0, 0.0, 0.0);
  const __m256d v_azz_scaled = _mm256_mul_pd(vk2_mask, _mm256_set1_pd(azz));

  double half_az = 0.5 * az;
  __m256d v_min = _mm256_set1_pd(1e30);

  for (int bi = 0; bi <= 2; bi++) {
    double ti = 0.5 * bi * ax + (bi == 2 ? axx : 0.0);
    double bi_axz = bi * axz;
    double bi_axy = 0.25 * bi * axy;
    for (int bj = 0; bj <= 2; bj++) {
      double tj = ti + 0.5 * bj * ay + (bj == 2 ? ayy : 0.0) + bj * bi_axy;
      double T = a0 + tj;
      double K_slope = half_az + 0.25 * (bi_axz + bj * ayz);

      __m256d v_T = _mm256_set1_pd(T);
      __m256d v_slope = _mm256_set1_pd(K_slope);
      __m256d v_res = _mm256_fmadd_pd(vk_mult, v_slope, v_T);
      v_res = _mm256_add_pd(v_res, v_azz_scaled);

      v_min = _mm256_min_pd(v_min, v_res);
    }
  }

  __m128d low = _mm256_castpd256_pd128(v_min);
  __m128d high = _mm256_extractf128_pd(v_min, 1);
  __m128d min128 = _mm_min_pd(low, high);
  __m128d min_shuffle = _mm_shuffle_pd(min128, min128, 1);
  __m128d final_min = _mm_min_sd(min128, min_shuffle);
  return _mm_cvtsd_f64(final_min);
}

void ComputeBernstein27Controls(
    const double C[10],
    double lx, double ly, double lz,
    double wx, double wy, double wz,
    double out_controls[27]) {
  double a0 = C[0] + C[1]*lx + C[2]*ly + C[3]*lz +
              C[4]*lx*lx + C[5]*lx*ly + C[6]*lx*lz +
              C[7]*ly*ly + C[8]*ly*lz + C[9]*lz*lz;
  double ax = (C[1] + 2.0*C[4]*lx + C[5]*ly + C[6]*lz) * wx;
  double ay = (C[2] + C[5]*lx + 2.0*C[7]*ly + C[8]*lz) * wy;
  double az = (C[3] + C[6]*lx + C[8]*ly + 2.0*C[9]*lz) * wz;
  double axx = C[4] * wx * wx, ayy = C[7] * wy * wy, azz = C[9] * wz * wz;
  double axy = C[5] * wx * wy, axz = C[6] * wx * wz, ayz = C[8] * wy * wz;

  const __m256d vk_mult = _mm256_set_pd(0.0, 2.0, 1.0, 0.0);
  const __m256d vk2_mask = _mm256_set_pd(0.0, 1.0, 0.0, 0.0);
  const __m256d v_azz_scaled = _mm256_mul_pd(vk2_mask, _mm256_set1_pd(azz));

  double half_az = 0.5 * az;
  int idx = 0;
  for (int bi = 0; bi <= 2; bi++) {
    double ti = 0.5 * bi * ax + (bi == 2 ? axx : 0.0);
    double bi_axz = bi * axz;
    double bi_axy = 0.25 * bi * axy;
    for (int bj = 0; bj <= 2; bj++) {
      double tj = ti + 0.5 * bj * ay + (bj == 2 ? ayy : 0.0) + bj * bi_axy;
      double T = a0 + tj;
      double K_slope = half_az + 0.25 * (bi_axz + bj * ayz);

      __m256d v_T = _mm256_set1_pd(T);
      __m256d v_slope = _mm256_set1_pd(K_slope);
      __m256d v_res = _mm256_fmadd_pd(vk_mult, v_slope, v_T);
      v_res = _mm256_add_pd(v_res, v_azz_scaled);

      Store3(&out_controls[idx], v_res);
      idx += 3;
    }
  }
}
#else
// Scalar reference fallback
double Bernstein27Min(const double C[10],
                     double lx, double ly, double lz,
                     double wx, double wy, double wz) {
  double a0 = (C[0] + C[1] * lx + C[2] * ly + C[3] * lz + C[4] * lx * lx +
               C[5] * lx * ly + C[6] * lx * lz + C[7] * ly * ly +
               C[8] * ly * lz + C[9] * lz * lz);
  double ax = wx * (C[1] + 2.0 * C[4] * lx + C[5] * ly + C[6] * lz);
  double ay = wy * (C[2] + C[5] * lx + 2.0 * C[7] * ly + C[8] * lz);
  double az = wz * (C[3] + C[6] * lx + C[8] * ly + 2.0 * C[9] * lz);
  double axx = C[4] * wx * wx, ayy = C[7] * wy * wy, azz = C[9] * wz * wz;
  double axy = C[5] * wx * wy, axz = C[6] * wx * wz, ayz = C[8] * wy * wz;

  double min_b = 1e30;
  for (int bi = 0; bi <= 2; bi++) {
    double ti = 0.5 * bi * ax + (bi == 2 ? axx : 0.0);
    for (int bj = 0; bj <= 2; bj++) {
      double tj =
          ti + 0.5 * bj * ay + (bj == 2 ? ayy : 0.0) + 0.25 * bi * bj * axy;
      for (int bk = 0; bk <= 2; bk++) {
        double val = a0 + tj + 0.5 * bk * az + (bk == 2 ? azz : 0.0) +
                     0.25 * bk * (bi * axz + bj * ayz);
        if (val < min_b)
          min_b = val;
      }
    }
  }
  return min_b;
}

void ComputeBernstein27Controls(
    const double C[10],
    double lx, double ly, double lz,
    double wx, double wy, double wz,
    double out_controls[27]) {
  double a0 = C[0] + C[1]*lx + C[2]*ly + C[3]*lz +
              C[4]*lx*lx + C[5]*lx*ly + C[6]*lx*lz +
              C[7]*ly*ly + C[8]*ly*lz + C[9]*lz*lz;
  double ax = (C[1] + 2.0*C[4]*lx + C[5]*ly + C[6]*lz) * wx;
  double ay = (C[2] + C[5]*lx + 2.0*C[7]*ly + C[8]*lz) * wy;
  double az = (C[3] + C[6]*lx + C[8]*ly + 2.0*C[9]*lz) * wz;
  double axx = C[4] * wx * wx, ayy = C[7] * wy * wy, azz = C[9] * wz * wz;
  double axy = C[5] * wx * wy, axz = C[6] * wx * wz, ayz = C[8] * wy * wz;

  int idx = 0;
  for (int bi = 0; bi <= 2; bi++) {
    double ti = 0.5 * bi * ax + (bi == 2 ? axx : 0.0);
    for (int bj = 0; bj <= 2; bj++) {
      double tj = ti + 0.5 * bj * ay + (bj == 2 ? ayy : 0.0) + 0.25 * bi * bj * axy;
      for (int bk = 0; bk <= 2; bk++) {
        double val = a0 + tj + 0.5 * bk * az + (bk == 2 ? azz : 0.0) +
                     0.25 * bk * (bi * axz + bj * ayz);
        out_controls[idx++] = val;
      }
    }
  }
}
#endif

// In-register accumulation of the 10 quadratic displacement polynomial
// coefficients for contact (vin, vout) with normal vector u, scaled by chart
// signs s = (sx, sy, sz).
inline void AccumulateContactPoly(double C[10], double weight, vec3 u, vec3 vin,
                                  vec3 vout, vec3 s) {
  double sx = s.x, sy = s.y, sz = s.z;
  double ux = u.x, uy = u.y, uz = u.z;
  double vx = vin.x, vy = vin.y, vz = vin.z;
  double ox = vout.x, oy = vout.y, oz = vout.z;

  // Constant term (m = 0):
  C[0] += weight * (ux * (sx*vx - ox) + uy * (sy*vy - oy) + uz * (sz*vz - oz));

  // Linear terms:
  C[1] += weight * 2.0 * (-uy * sy * vz + uz * sz * vy);
  C[2] += weight * 2.0 * (ux * sx * vz - uz * sz * vx);
  C[3] += weight * 2.0 * (-ux * sx * vy + uy * sy * vx);

  // Quadratic pure terms:
  C[4] += weight * (ux * (sx*vx - ox) - uy * (sy*vy + oy) - uz * (sz*vz + oz));
  C[7] += weight * (-ux * (sx*vx + ox) + uy * (sy*vy - oy) - uz * (sz*vz + oz));
  C[9] += weight * (-ux * (sx*vx + ox) - uy * (sy*vy + oy) + uz * (sz*vz - oz));

  // Quadratic cross terms:
  C[5] += weight * 2.0 * (ux * sx * vy + uy * sy * vx);
  C[6] += weight * 2.0 * (ux * sx * vz + uz * sz * vx);
  C[8] += weight * 2.0 * (uy * sy * vz + uz * sz * vy);
}

// CPU evaluator matching Bernstein logic
static Periodically eval_cpu_failed_per = Periodically(10.0);
GpuResult EvaluateBoxCPU(
    const GpuBox &box,
    const std::vector<GpuContact> &contacts,
    const std::vector<GpuTriple> &triples,
    StatusBar *status) {
  ctr_cpu++;

  double x0 = box.cx, y0 = box.cy, z0 = box.cz;
  double num[3][3] = {
    {1.0 + x0*x0 - y0*y0 - z0*z0, 2.0*(x0*y0 - z0), 2.0*(x0*z0 + y0)},
    {2.0*(x0*y0 + z0), 1.0 - x0*x0 + y0*y0 - z0*z0, 2.0*(y0*z0 - x0)},
    {2.0*(x0*z0 - y0), 2.0*(y0*z0 + x0), 1.0 - x0*x0 - y0*y0 + z0*z0}
  };
  double denom0 = 1.0 + x0*x0 + y0*y0 + z0*z0;

  vec3 s = {
    (box.chart == 2 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 2) ? -1.0 : 1.0
  };

  vec3 view_center = {
    (box.tri[0][0] + box.tri[1][0] + box.tri[2][0]) / 3.0,
    (box.tri[0][1] + box.tri[1][1] + box.tri[2][1]) / 3.0,
    (box.tri[0][2] + box.tri[1][2] + box.tri[2][2]) / 3.0
  };

  double ex = std::max(std::abs(box.cx - box.rx), std::abs(box.cx + box.rx));
  double ey = std::max(std::abs(box.cy - box.ry), std::abs(box.cy + box.ry));
  double ez = std::max(std::abs(box.cz - box.rz), std::abs(box.cz + box.rz));
  double d_bound = 1.0 + ex*ex + ey*ey + ez*ez;

  double lx = box.cx - box.rx, ly = box.cy - box.ry, lz = box.cz - box.rz;
  double wx = 2.0 * box.rx, wy = 2.0 * box.ry, wz = 2.0 * box.rz;
  double disp_error = 300.0 * d_bound * TIGHT_VERTEX_ERROR;

  vec3 p[6];
  p[0] = {box.tri[0][0], box.tri[0][1], box.tri[0][2]};
  p[1] = {box.tri[1][0], box.tri[1][1], box.tri[1][2]};
  p[2] = {box.tri[2][0], box.tri[2][1], box.tri[2][2]};
  p[3] = (p[0] + p[1]) * 0.5;
  p[4] = (p[1] + p[2]) * 0.5;
  p[5] = (p[2] + p[0]) * 0.5;

  // Pre-rotate all 20 inner vertices at box center
  vec3 rot_vin[20];
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec3 vin = {VERTICES[k][0], VERTICES[k][1], VERTICES[k][2]};
    rot_vin[k] = {
      s.x * (num[0][0]*vin.x + num[0][1]*vin.y + num[0][2]*vin.z),
      s.y * (num[1][0]*vin.x + num[1][1]*vin.y + num[1][2]*vin.z),
      s.z * (num[2][0]*vin.x + num[2][1]*vin.y + num[2][2]*vin.z)
    };
  }

  // Precompute best inner vertex and unit center polynomial for each contact in
  // this pool
  int c_start = box.contact_offset;
  int c_count =
      (box.num_contacts > 0) ? box.num_contacts : (int)contacts.size();
  std::vector<int> best_in(c_count);
  std::vector<std::array<double, 10>> psi_center(c_count);
  for (int c = 0; c < c_count; c++) {
    const auto &gc = contacts[c_start + c];
    vec3 edge = {gc.edge[0], gc.edge[1], gc.edge[2]};
    vec3 out = {VERTICES[gc.vertex][0], VERTICES[gc.vertex][1],
                VERTICES[gc.vertex][2]};
    vec3 u = yocto::cross(view_center, edge);
    double best_val = -1e30;
    int best_k = 0;
    for (int k = 0; k < NUM_VERTICES; k++) {
      vec3 disp = rot_vin[k] - denom0 * out;
      double v = yocto::dot(u, disp);
      if (v > best_val) {
        best_val = v;
        best_k = k;
      }
    }
    best_in[c] = best_k;

    vec3 vin = {VERTICES[best_k][0], VERTICES[best_k][1], VERTICES[best_k][2]};
    double poly[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    AccumulateContactPoly(poly, 1.0, u, vin, out, s);
    for (int m = 0; m < 10; m++) {
      psi_center[c][m] = poly[m];
    }
  }

  GpuResult res;
  res.certified = 0;
  res.winning_triple = -1;
  res.inner[0] = 0;
  res.inner[1] = 0;
  res.inner[2] = 0;
  res.margin = -1e30;

  int passed_w_positive = 0;
  int passed_center = 0;
  double best_center_margin = -1e30;
  double best_defect = 0.0;
  double best_min_b = 0.0;

  for (int t = 0; t < box.num_triples; t++) {
    const auto &trip = triples[box.triple_offset + t];

    double defect_penalty = d_bound * trip.weighted_defect_upper;

    int loc_c0 = trip.c0;
    int loc_c1 = trip.c1;
    int loc_c2 = trip.c2;
    if (loc_c0 >= c_count || loc_c1 >= c_count || loc_c2 >= c_count) continue;

    // Stage 1: Fast filter at view_center (27 controls)
    const auto &c1 = contacts[c_start + loc_c1];
    const auto &c2 = contacts[c_start + loc_c2];
    vec3 edge1 = {c1.edge[0], c1.edge[1], c1.edge[2]};
    vec3 edge2 = {c2.edge[0], c2.edge[1], c2.edge[2]};

    vec3 w_coeff0 = yocto::cross(edge1, edge2);
    double w0 = yocto::dot(view_center, w_coeff0);
    if (w0 <= 1e-9) continue;

    const auto &c0 = contacts[c_start + loc_c0];
    vec3 edge0 = {c0.edge[0], c0.edge[1], c0.edge[2]};

    vec3 w_coeff1 = yocto::cross(edge2, edge0);
    double w1 = yocto::dot(view_center, w_coeff1);
    if (w1 <= 1e-9) continue;

    vec3 w_coeff2 = yocto::cross(edge0, edge1);
    double w2 = yocto::dot(view_center, w_coeff2);
    if (w2 <= 1e-9) continue;

    passed_w_positive++;

    double C_center[10];
    for (int m = 0; m < 10; m++) {
      C_center[m] = w0 * psi_center[loc_c0][m] +
                    w1 * psi_center[loc_c1][m] +
                    w2 * psi_center[loc_c2][m];
    }

    double min_b_center = Bernstein27Min(C_center, lx, ly, lz, wx, wy, wz);
    double cmargin = min_b_center - defect_penalty - disp_error;
    if (cmargin > best_center_margin) {
      best_center_margin = cmargin;
      best_defect = defect_penalty;
      best_min_b = min_b_center;
    }
    if (cmargin <= 0.0) {
      continue;
    }
    passed_center++;

    // Stage 2: Simplex Bernstein evaluation with progressive early exit
    // Only evaluated when center filter passes (~12% of triples).
    int in0 = best_in[loc_c0];
    int in1 = best_in[loc_c1];
    int in2 = best_in[loc_c2];

    vec3 vin0 = {VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]};
    vec3 vout0 = {VERTICES[c0.vertex][0], VERTICES[c0.vertex][1], VERTICES[c0.vertex][2]};

    vec3 vin1 = {VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]};
    vec3 vout1 = {VERTICES[c1.vertex][0], VERTICES[c1.vertex][1], VERTICES[c1.vertex][2]};

    vec3 vin2 = {VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]};
    vec3 vout2 = {VERTICES[c2.vertex][0], VERTICES[c2.vertex][1], VERTICES[c2.vertex][2]};

    // Stage 2: Simplex Bernstein evaluation with progressive early exit
    // Corner 0
    double C0[10] = {0};
    double w0_0 = yocto::dot(p[0], w_coeff0);
    double w1_0 = yocto::dot(p[0], w_coeff1);
    double w2_0 = yocto::dot(p[0], w_coeff2);
    AccumulateContactPoly(C0, w0_0, yocto::cross(p[0], edge0), vin0, vout0, s);
    AccumulateContactPoly(C0, w1_0, yocto::cross(p[0], edge1), vin1, vout1, s);
    AccumulateContactPoly(C0, w2_0, yocto::cross(p[0], edge2), vin2, vout2, s);
    double min_0 = Bernstein27Min(C0, lx, ly, lz, wx, wy, wz);
    if (min_0 - defect_penalty - disp_error <= 0.0) continue;

    // Corner 1
    double C1[10] = {0};
    double w0_1 = yocto::dot(p[1], w_coeff0);
    double w1_1 = yocto::dot(p[1], w_coeff1);
    double w2_1 = yocto::dot(p[1], w_coeff2);
    AccumulateContactPoly(C1, w0_1, yocto::cross(p[1], edge0), vin0, vout0, s);
    AccumulateContactPoly(C1, w1_1, yocto::cross(p[1], edge1), vin1, vout1, s);
    AccumulateContactPoly(C1, w2_1, yocto::cross(p[1], edge2), vin2, vout2, s);
    double min_1 = Bernstein27Min(C1, lx, ly, lz, wx, wy, wz);
    if (min_1 - defect_penalty - disp_error <= 0.0) continue;

    // Corner 2
    double C2[10] = {0};
    double w0_2 = yocto::dot(p[2], w_coeff0);
    double w1_2 = yocto::dot(p[2], w_coeff1);
    double w2_2 = yocto::dot(p[2], w_coeff2);
    AccumulateContactPoly(C2, w0_2, yocto::cross(p[2], edge0), vin0, vout0, s);
    AccumulateContactPoly(C2, w1_2, yocto::cross(p[2], edge1), vin1, vout1, s);
    AccumulateContactPoly(C2, w2_2, yocto::cross(p[2], edge2), vin2, vout2, s);
    double min_2 = Bernstein27Min(C2, lx, ly, lz, wx, wy, wz);
    if (min_2 - defect_penalty - disp_error <= 0.0) continue;

    // Midpoint p[3] (Edge 01)
    double M[10] = {0};
    double w0_3 = yocto::dot(p[3], w_coeff0);
    double w1_3 = yocto::dot(p[3], w_coeff1);
    double w2_3 = yocto::dot(p[3], w_coeff2);
    AccumulateContactPoly(M, w0_3, yocto::cross(p[3], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_3, yocto::cross(p[3], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_3, yocto::cross(p[3], edge2), vin2, vout2, s);
    double Q[10];
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C0[m] + C1[m]);
    double min_3 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_3 - defect_penalty - disp_error <= 0.0) continue;

    // Midpoint p[4] (Edge 12)
    for (int m = 0; m < 10; m++) M[m] = 0;
    double w0_4 = yocto::dot(p[4], w_coeff0);
    double w1_4 = yocto::dot(p[4], w_coeff1);
    double w2_4 = yocto::dot(p[4], w_coeff2);
    AccumulateContactPoly(M, w0_4, yocto::cross(p[4], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_4, yocto::cross(p[4], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_4, yocto::cross(p[4], edge2), vin2, vout2, s);
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C1[m] + C2[m]);
    double min_4 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_4 - defect_penalty - disp_error <= 0.0) continue;

    // Midpoint p[5] (Edge 20)
    for (int m = 0; m < 10; m++) M[m] = 0;
    double w0_5 = yocto::dot(p[5], w_coeff0);
    double w1_5 = yocto::dot(p[5], w_coeff1);
    double w2_5 = yocto::dot(p[5], w_coeff2);
    AccumulateContactPoly(M, w0_5, yocto::cross(p[5], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_5, yocto::cross(p[5], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_5, yocto::cross(p[5], edge2), vin2, vout2, s);
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C2[m] + C0[m]);
    double min_5 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_5 - defect_penalty - disp_error <= 0.0) continue;

    // All 6 simplex Bernstein bounds passed!
    double min_162 = std::min({min_0, min_1, min_2, min_3, min_4, min_5});
    res.certified = 1;
    res.winning_triple = t;
    res.inner[0] = in0;
    res.inner[1] = in1;
    res.inner[2] = in2;
    res.margin = min_162 - defect_penalty - disp_error;
    break;
  }

  if (!res.certified && box.rx < 1e-6) {
    eval_cpu_failed_per.RunIf([&]{
        if (status) {
          status->Print(
              AORANGE("‼") " EvalBoxCPU failed: passed_w={}, passed_center={}, "
              "best_cmargin={:.17g} (min_b={:.17g}, defect={:.17g}, disp={:.17g})\n",
              passed_w_positive, passed_center, best_center_margin, best_min_b, best_defect, disp_error);
        }
      });
  }

  return res;
}

// Evaluator using 2D linear programming to find the optimal translation t*
// and center inner contact vertices before polynomial accumulation.
// Strictly superior to EvaluateBoxCPU for tight cells while producing
// Lean-compliant certificates.
GpuResult EvaluateBoxCPULP(const GpuBox &box,
                           const std::vector<GpuContact> &contacts,
                           const std::vector<GpuTriple> &triples,
                           bool use_optimal_translation, StatusBar *status) {
  ctr_cpu++;

  double x0 = box.cx, y0 = box.cy, z0 = box.cz;
  double num[3][3] = {
    {1.0 + x0*x0 - y0*y0 - z0*z0, 2.0*(x0*y0 - z0), 2.0*(x0*z0 + y0)},
    {2.0*(x0*y0 + z0), 1.0 - x0*x0 + y0*y0 - z0*z0, 2.0*(y0*z0 - x0)},
    {2.0*(x0*z0 - y0), 2.0*(y0*z0 + x0), 1.0 - x0*x0 - y0*y0 + z0*z0}
  };
  double denom0 = 1.0 + x0*x0 + y0*y0 + z0*z0;

  vec3 s = {
    (box.chart == 2 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 2) ? -1.0 : 1.0
  };

  vec3 view_center = {
    (box.tri[0][0] + box.tri[1][0] + box.tri[2][0]) / 3.0,
    (box.tri[0][1] + box.tri[1][1] + box.tri[2][1]) / 3.0,
    (box.tri[0][2] + box.tri[1][2] + box.tri[2][2]) / 3.0
  };

  double ex = std::max(std::abs(box.cx - box.rx), std::abs(box.cx + box.rx));
  double ey = std::max(std::abs(box.cy - box.ry), std::abs(box.cy + box.ry));
  double ez = std::max(std::abs(box.cz - box.rz), std::abs(box.cz + box.rz));
  double d_bound = 1.0 + ex*ex + ey*ey + ez*ez;

  double lx = box.cx - box.rx, ly = box.cy - box.ry, lz = box.cz - box.rz;
  double wx = 2.0 * box.rx, wy = 2.0 * box.ry, wz = 2.0 * box.rz;
  double disp_error = 300.0 * d_bound * TIGHT_VERTEX_ERROR;

  vec3 p[6];
  p[0] = {box.tri[0][0], box.tri[0][1], box.tri[0][2]};
  p[1] = {box.tri[1][0], box.tri[1][1], box.tri[1][2]};
  p[2] = {box.tri[2][0], box.tri[2][1], box.tri[2][2]};
  p[3] = (p[0] + p[1]) * 0.5;
  p[4] = (p[1] + p[2]) * 0.5;
  p[5] = (p[2] + p[0]) * 0.5;

  // Pre-rotate all 20 inner vertices at box center
  vec3 rot_vin[NUM_VERTICES];
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec3 vin = {VERTICES[k][0], VERTICES[k][1], VERTICES[k][2]};
    rot_vin[k] = {
      s.x * (num[0][0]*vin.x + num[0][1]*vin.y + num[0][2]*vin.z),
      s.y * (num[1][0]*vin.x + num[1][1]*vin.y + num[1][2]*vin.z),
      s.z * (num[2][0]*vin.x + num[2][1]*vin.y + num[2][2]*vin.z)
    };
  }

  // 2D projection frame at view_center
  vec3 norm_v = yocto::normalize(view_center);
  vec3 right;
  if (std::abs(norm_v.z) < 0.9) {
    right = yocto::normalize(yocto::cross(norm_v, vec3{0, 0, 1}));
  } else {
    right = yocto::normalize(yocto::cross(norm_v, vec3{1, 0, 0}));
  }
  vec3 up = yocto::normalize(yocto::cross(right, norm_v));

  vec3 t_3d{0, 0, 0};
  if (use_optimal_translation) {
    std::vector<vec2> outer_verts(NUM_VERTICES);
    for (int i = 0; i < NUM_VERTICES; i++) {
      vec3 v = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
      outer_verts[i] = {yocto::dot(v, right), yocto::dot(v, up)};
    }
    std::vector<int> outer_hull = Hull2D::QuickHull(outer_verts);
    if (outer_hull.size() >= 3) {
      std::vector<PolygonEdge> outer_edges =
          GetHullEdges(outer_verts, outer_hull);
      std::vector<vec2> inner_verts(NUM_VERTICES);
      for (int i = 0; i < NUM_VERTICES; i++) {
        vec3 v_unnorm = rot_vin[i] * (1.0 / denom0);
        inner_verts[i] = {yocto::dot(v_unnorm, right),
                          yocto::dot(v_unnorm, up)};
      }
      Clearance2D opt_c = MaximizeClearance2D(outer_edges, inner_verts);
      if (opt_c.clearance < 0.0) {
        t_3d = opt_c.translation.x * right + opt_c.translation.y * up;
      }
    }
  }

  // Precompute best inner vertex and unit center polynomial for each contact in
  // this pool
  int c_start = box.contact_offset;
  int c_count =
      (box.num_contacts > 0) ? box.num_contacts : (int)contacts.size();
  std::vector<int> best_in(c_count);
  std::vector<std::array<double, 10>> psi_center(c_count);
  for (int c = 0; c < c_count; c++) {
    const auto &gc = contacts[c_start + c];
    vec3 edge = {gc.edge[0], gc.edge[1], gc.edge[2]};
    vec3 out = {VERTICES[gc.vertex][0], VERTICES[gc.vertex][1],
                VERTICES[gc.vertex][2]};
    vec3 u = yocto::cross(view_center, edge);
    double best_val = -1e30;
    int best_k = 0;
    for (int k = 0; k < NUM_VERTICES; k++) {
      vec3 disp = (rot_vin[k] + denom0 * t_3d) - denom0 * out;
      double v = yocto::dot(u, disp);
      if (v > best_val) {
        best_val = v;
        best_k = k;
      }
    }
    best_in[c] = best_k;

    vec3 vin = {VERTICES[best_k][0], VERTICES[best_k][1], VERTICES[best_k][2]};
    double poly[10] = {0.0};
    AccumulateContactPoly(poly, 1.0, u, vin, out, s);
    for (int m = 0; m < 10; m++) {
      psi_center[c][m] = poly[m];
    }
  }

  GpuResult res;
  res.certified = 0;
  res.winning_triple = -1;
  res.inner[0] = 0;
  res.inner[1] = 0;
  res.inner[2] = 0;
  res.margin = -1e30;

  for (int t = 0; t < box.num_triples; t++) {
    const auto &trip = triples[box.triple_offset + t];

    double defect_penalty = d_bound * trip.weighted_defect_upper;

    int loc_c0 = trip.c0;
    int loc_c1 = trip.c1;
    int loc_c2 = trip.c2;
    if (loc_c0 >= c_count || loc_c1 >= c_count || loc_c2 >= c_count) continue;

    // Stage 1: Fast filter at view_center (27 controls)
    const auto &c1 = contacts[c_start + loc_c1];
    const auto &c2 = contacts[c_start + loc_c2];
    vec3 edge1 = {c1.edge[0], c1.edge[1], c1.edge[2]};
    vec3 edge2 = {c2.edge[0], c2.edge[1], c2.edge[2]};

    vec3 w_coeff0 = yocto::cross(edge1, edge2);
    double w0 = yocto::dot(view_center, w_coeff0);
    if (w0 <= 1e-9) continue;

    const auto &c0 = contacts[c_start + loc_c0];
    vec3 edge0 = {c0.edge[0], c0.edge[1], c0.edge[2]};

    vec3 w_coeff1 = yocto::cross(edge2, edge0);
    double w1 = yocto::dot(view_center, w_coeff1);
    if (w1 <= 1e-9) continue;

    vec3 w_coeff2 = yocto::cross(edge0, edge1);
    double w2 = yocto::dot(view_center, w_coeff2);
    if (w2 <= 1e-9) continue;

    double C_center[10];
    for (int m = 0; m < 10; m++) {
      C_center[m] = w0 * psi_center[loc_c0][m] +
                    w1 * psi_center[loc_c1][m] +
                    w2 * psi_center[loc_c2][m];
    }

    double min_b_center = Bernstein27Min(C_center, lx, ly, lz, wx, wy, wz);
    double cmargin = min_b_center - defect_penalty - disp_error;
    if (cmargin <= 0.0) continue;

    // Stage 2: Simplex Bernstein evaluation across 6 points
    int in0 = best_in[loc_c0];
    int in1 = best_in[loc_c1];
    int in2 = best_in[loc_c2];
    vec3 vin0 = {VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]};
    vec3 vin1 = {VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]};
    vec3 vin2 = {VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]};
    vec3 out0 = {VERTICES[c0.vertex][0], VERTICES[c0.vertex][1], VERTICES[c0.vertex][2]};
    vec3 out1 = {VERTICES[c1.vertex][0], VERTICES[c1.vertex][1], VERTICES[c1.vertex][2]};
    vec3 out2 = {VERTICES[c2.vertex][0], VERTICES[c2.vertex][1], VERTICES[c2.vertex][2]};

    double min_162 = 1e30;
    bool all_nodes_certified = true;

    for (int i = 0; i < 6; i++) {
      vec3 pi = p[i];
      double w0_i = yocto::dot(pi, w_coeff0);
      double w1_i = yocto::dot(pi, w_coeff1);
      double w2_i = yocto::dot(pi, w_coeff2);

      vec3 u0_i = yocto::cross(pi, edge0);
      vec3 u1_i = yocto::cross(pi, edge1);
      vec3 u2_i = yocto::cross(pi, edge2);

      double C_node[10] = {0.0};
      AccumulateContactPoly(C_node, w0_i, u0_i, vin0, out0, s);
      AccumulateContactPoly(C_node, w1_i, u1_i, vin1, out1, s);
      AccumulateContactPoly(C_node, w2_i, u2_i, vin2, out2, s);

      double min_b = Bernstein27Min(C_node, lx, ly, lz, wx, wy, wz);
      if (min_b < min_162) min_162 = min_b;

      if (min_b - defect_penalty - disp_error <= 0.0) {
        all_nodes_certified = false;
        break;
      }
    }

    if (!all_nodes_certified) continue;

    res.certified = 1;
    res.winning_triple = t;
    res.inner[0] = in0;
    res.inner[1] = in1;
    res.inner[2] = in2;
    res.margin = min_162 - defect_penalty - disp_error;
    break;
  }

  return res;
}

Polyhedron GetPolyhedron229() {
  Polyhedron poly;
  poly.name = "nopert_229";
  poly.vertices.reserve(NUM_VERTICES);
  for (int i = 0; i < NUM_VERTICES; i++) {
    poly.vertices.push_back(vec3{
        VERTICES[i][0],
        VERTICES[i][1],
        VERTICES[i][2],
      });
  }
  return poly;
}


// Euclidean projection of x onto the probability simplex sum(out) = 1, out >= 0
void ProjectToSimplex(int K, const double x[], double out[]) {
  double u[4];
  for (int i = 0; i < K; i++) u[i] = x[i];
  std::sort(u, u + K, std::greater<double>());
  double cssv[4];
  cssv[0] = u[0];
  for (int i = 1; i < K; i++) cssv[i] = cssv[i - 1] + u[i];
  int rho = 0;
  for (int i = 0; i < K; i++) {
    if (u[i] + (1.0 - cssv[i]) / (i + 1) > 0.0) {
      rho = i;
    }
  }
  double theta = (1.0 - cssv[rho]) / (rho + 1);
  for (int i = 0; i < K; i++) {
    out[i] = std::max(0.0, x[i] + theta);
  }
}

// Evaluates the worst margin across 162 controls given mixture weights alpha
double EvalMixtureMargin(int K, const double *const margins[],
                         const double alpha[],
                         int *out_worst_idx) {
  double min_val = 1e30;
  int worst_idx = 0;
  if (K == 1) {
    const double *m0 = margins[0];
    for (int j = 0; j < 162; j++) {
      if (m0[j] < min_val) {
        min_val = m0[j];
        worst_idx = j;
      }
    }
  } else if (K == 2) {
    double a0 = alpha[0], a1 = alpha[1];
    const double *m0 = margins[0], *m1 = margins[1];
    for (int j = 0; j < 162; j++) {
      double sum = a0 * m0[j] + a1 * m1[j];
      if (sum < min_val) {
        min_val = sum;
        worst_idx = j;
      }
    }
  } else if (K == 3) {
    double a0 = alpha[0], a1 = alpha[1], a2 = alpha[2];
    const double *m0 = margins[0], *m1 = margins[1], *m2 = margins[2];
    for (int j = 0; j < 162; j++) {
      double sum = a0 * m0[j] + a1 * m1[j] + a2 * m2[j];
      if (sum < min_val) {
        min_val = sum;
        worst_idx = j;
      }
    }
  } else if (K == 4) {
    double a0 = alpha[0], a1 = alpha[1], a2 = alpha[2], a3 = alpha[3];
    const double *m0 = margins[0], *m1 = margins[1], *m2 = margins[2],
                 *m3 = margins[3];
    for (int j = 0; j < 162; j++) {
      double sum = a0 * m0[j] + a1 * m1[j] + a2 * m2[j] + a3 * m3[j];
      if (sum < min_val) {
        min_val = sum;
        worst_idx = j;
      }
    }
  } else {
    for (int j = 0; j < 162; j++) {
      double sum = 0.0;
      for (int k = 0; k < K; k++)
        sum += alpha[k] * margins[k][j];
      if (sum < min_val) {
        min_val = sum;
        worst_idx = j;
      }
    }
  }
  if (out_worst_idx)
    *out_worst_idx = worst_idx;
  return min_val;
}

// Solves max_{alpha in Delta_K} min_{j=0..161} sum_{k=0}^{K-1} alpha_k
// margins[k][j] for K in {1, 2, 3, 4}.
double SolveOptimalWeights(int K, const double *const margins[],
                           double out_alpha[4], bool polish,
                           const double *warm_alpha,
                           double target_margin) {

  if (K == 1) {
    out_alpha[0] = 1.0;
    return EvalMixtureMargin(1, margins, out_alpha);
  }

  if (K == 2) {
    // 1. Exact 1D Chebyshev Centering for K = 2.
    // For each control point j in 0..161, we require:
    //   w * margins[0][j] + (1 - w) * margins[1][j] >= target_margin
    //   w * (margins[0][j] - margins[1][j]) >= target_margin - margins[1][j]
    double w_min = 0.0, w_max = 1.0;
    bool feasible = true;
    for (int j = 0; j < 162; j++) {
      double d = margins[0][j] - margins[1][j];
      double b = target_margin - margins[1][j];
      if (d > 0.0) {
        double bound = b / d;
        if (bound > w_min) w_min = bound;
      } else if (d < 0.0) {
        double bound = b / d;
        if (bound < w_max) w_max = bound;
      } else {
        if (margins[1][j] < target_margin) {
          feasible = false;
          break;
        }
      }
    }

    if (feasible && w_min <= w_max) {
      // The Chebyshev center is the midpoint of the feasible interval,
      // maximizing distance to constraint boundaries.
      double best_w = (w_min + w_max) * 0.5;
      out_alpha[0] = best_w;
      out_alpha[1] = 1.0 - best_w;
      return EvalMixtureMargin(2, margins, out_alpha);
    }

    // 2. If target_margin is not achievable, run 1D golden section search to find
    // the global maximum of the concave margin function f(w) on [0, 1].
    double a = 0.0, b = 1.0;
    const double phi = (std::sqrt(5.0) - 1.0) * 0.5;
    double x1 = b - phi * (b - a);
    double x2 = a + phi * (b - a);
    double a1[2] = {x1, 1.0 - x1};
    double a2[2] = {x2, 1.0 - x2};
    double f1 = EvalMixtureMargin(2, margins, a1);
    double f2 = EvalMixtureMargin(2, margins, a2);

    int max_iter = polish ? 30 : 15;
    for (int iter = 0; iter < max_iter; iter++) {
      if (f1 < f2) {
        a = x1;
        x1 = x2;
        f1 = f2;
        x2 = a + phi * (b - a);
        a2[0] = x2; a2[1] = 1.0 - x2;
        f2 = EvalMixtureMargin(2, margins, a2);
      } else {
        b = x2;
        x2 = x1;
        f2 = f1;
        x1 = b - phi * (b - a);
        a1[0] = x1; a1[1] = 1.0 - x1;
        f1 = EvalMixtureMargin(2, margins, a1);
      }
    }
    double best_a0 = (a + b) * 0.5;
    out_alpha[0] = best_a0;
    out_alpha[1] = 1.0 - best_a0;
    return EvalMixtureMargin(2, margins, out_alpha);
  }

  // K = 3 or 4:
  double alpha[4];
  for (int k = 0; k < K; k++) alpha[k] = 1.0 / K;

  double best_alpha[4];
  std::memcpy(best_alpha, alpha, sizeof(double) * K);
  double best_val = EvalMixtureMargin(K, margins, alpha);

  if (warm_alpha) {
    double warm_val = EvalMixtureMargin(K, margins, warm_alpha);
    if (warm_val > best_val) {
      best_val = warm_val;
      std::memcpy(best_alpha, warm_alpha, sizeof(double) * K);
      std::memcpy(alpha, warm_alpha, sizeof(double) * K);
    }
  }

  // Projected Subgradient Ascent
  double eta = 0.05;
  int subgrad_iters = polish ? 60 : 25;
  for (int iter = 0; iter < subgrad_iters; iter++) {
    int worst_j = 0;
    double val = EvalMixtureMargin(K, margins, alpha, &worst_j);
    if (val > best_val) {
      best_val = val;
      std::memcpy(best_alpha, alpha, sizeof(double) * K);
    }
    double step = eta / std::sqrt(iter + 1.0);
    double next_x[4];
    for (int k = 0; k < K; k++) {
      next_x[k] = alpha[k] + step * margins[k][worst_j];
    }
    ProjectToSimplex(K, next_x, alpha);
  }

  if (!polish && best_val <= -0.005) {
    std::memcpy(out_alpha, best_alpha, sizeof(double) * K);
    return best_val;
  }

  // Nelder-Mead simplex search on barycentric coordinates.
  // Once target_margin is reached, run a fixed number of heuristic polish
  // iterations to push deeper into the interior.
  constexpr int kNelderMeadGoalPolishIters = 8;
  int post_goal_iters = 0;

  double p[5][4];
  double p_val[5];
  std::memcpy(p[0], best_alpha, sizeof(double) * K);
  p_val[0] = best_val;

  double perturb = 0.02;
  for (int i = 1; i <= K; i++) {
    double unnorm[4];
    for (int k = 0; k < K; k++) {
      unnorm[k] = best_alpha[k] + (k == (i - 1) ? perturb : -perturb / (K - 1));
    }
    ProjectToSimplex(K, unnorm, p[i]);
    p_val[i] = EvalMixtureMargin(K, margins, p[i]);
    if (p_val[i] > best_val) {
      best_val = p_val[i];
      std::memcpy(best_alpha, p[i], sizeof(double) * K);
    }
  }

  for (int iter = 0; iter < 40; iter++) {
    if (best_val >= target_margin) {
      post_goal_iters++;
      if (post_goal_iters > kNelderMeadGoalPolishIters) break;
    }

    for (int i = 0; i <= K; i++) {
      for (int j = i + 1; j <= K; j++) {
        if (p_val[j] > p_val[i]) {
          std::swap(p_val[i], p_val[j]);
          for (int k = 0; k < K; k++) std::swap(p[i][k], p[j][k]);
        }
      }
    }
    if (p_val[0] > best_val) {
      best_val = p_val[0];
      std::memcpy(best_alpha, p[0], sizeof(double) * K);
    }

    double c[4] = {0};
    for (int i = 0; i < K; i++) {
      for (int k = 0; k < K; k++) c[k] += p[i][k];
    }
    for (int k = 0; k < K; k++) c[k] /= K;

    double xr[4], xr_proj[4];
    for (int k = 0; k < K; k++) xr[k] = c[k] + 1.0 * (c[k] - p[K][k]);
    ProjectToSimplex(K, xr, xr_proj);
    double vr = EvalMixtureMargin(K, margins, xr_proj);

    if (vr > p_val[0]) {
      double xe[4], xe_proj[4];
      for (int k = 0; k < K; k++) xe[k] = c[k] + 2.0 * (xr_proj[k] - c[k]);
      ProjectToSimplex(K, xe, xe_proj);
      double ve = EvalMixtureMargin(K, margins, xe_proj);
      if (ve > vr) {
        std::memcpy(p[K], xe_proj, sizeof(double) * K);
        p_val[K] = ve;
      } else {
        std::memcpy(p[K], xr_proj, sizeof(double) * K);
        p_val[K] = vr;
      }
    } else if (vr > p_val[K - 1]) {
      std::memcpy(p[K], xr_proj, sizeof(double) * K);
      p_val[K] = vr;
    } else {
      double xc[4], xc_proj[4];
      for (int k = 0; k < K; k++) xc[k] = c[k] + 0.5 * (p[K][k] - c[k]);
      ProjectToSimplex(K, xc, xc_proj);
      double vc = EvalMixtureMargin(K, margins, xc_proj);
      if (vc > p_val[K]) {
        std::memcpy(p[K], xc_proj, sizeof(double) * K);
        p_val[K] = vc;
      } else {
        for (int i = 1; i <= K; i++) {
          for (int k = 0; k < K; k++) p[i][k] = p[0][k] + 0.5 * (p[i][k] - p[0][k]);
          ProjectToSimplex(K, p[i], p[i]);
          p_val[i] = EvalMixtureMargin(K, margins, p[i]);
        }
      }
    }
  }

  std::memcpy(out_alpha, best_alpha, sizeof(double) * K);
  return best_val;
}

void ComputeTripleMargins(
    int chart,
    const vec3 p[6],
    double lx, double ly, double lz,
    double wx_len, double wy_len, double wz_len,
    double d_bound,
    int triple_idx,
    const int inners[3],
    std::shared_ptr<const TrianglePool> pool,
    double out_margins[162]) {
  double sx = 1.0, sy = 1.0, sz = 1.0;
  if (chart == 1) { sy = -1.0; sz = -1.0; }
  else if (chart == 2) { sx = -1.0; sz = -1.0; }
  vec3 s = {sx, sy, sz};

  const auto &triple = pool->gpu_triples[triple_idx];
  int ci0 = triple.c0, ci1 = triple.c1, ci2 = triple.c2;

  vec3 edge0 = {pool->contacts[ci0].edge[0], pool->contacts[ci0].edge[1], pool->contacts[ci0].edge[2]};
  vec3 edge1 = {pool->contacts[ci1].edge[0], pool->contacts[ci1].edge[1], pool->contacts[ci1].edge[2]};
  vec3 edge2 = {pool->contacts[ci2].edge[0], pool->contacts[ci2].edge[1], pool->contacts[ci2].edge[2]};

  vec3 coeff0 = yocto::cross(edge1, edge2);
  vec3 coeff1 = yocto::cross(edge2, edge0);
  vec3 coeff2 = yocto::cross(edge0, edge1);

  double disp_error = 300.0 * d_bound * TIGHT_VERTEX_ERROR;
  double penalty = d_bound * triple.weighted_defect_upper + disp_error;

  int in0 = inners[0], in1 = inners[1], in2 = inners[2];
  vec3 vin0 = {VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]};
  vec3 vout0 = {VERTICES[pool->contacts[ci0].vertex][0],
               VERTICES[pool->contacts[ci0].vertex][1],
               VERTICES[pool->contacts[ci0].vertex][2]};
  vec3 vin1 = {VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]};
  vec3 vout1 = {VERTICES[pool->contacts[ci1].vertex][0],
               VERTICES[pool->contacts[ci1].vertex][1],
               VERTICES[pool->contacts[ci1].vertex][2]};
  vec3 vin2 = {VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]};
  vec3 vout2 = {VERTICES[pool->contacts[ci2].vertex][0],
               VERTICES[pool->contacts[ci2].vertex][1],
               VERTICES[pool->contacts[ci2].vertex][2]};

  double C_pts[6][10] = {};
  for (int node = 0; node < 6; node++) {
    double w0 = yocto::dot(p[node], coeff0);
    double w1 = yocto::dot(p[node], coeff1);
    double w2 = yocto::dot(p[node], coeff2);

    AccumulateContactPoly(C_pts[node], w0, yocto::cross(p[node], edge0), vin0, vout0, s);
    AccumulateContactPoly(C_pts[node], w1, yocto::cross(p[node], edge1), vin1, vout1, s);
    AccumulateContactPoly(C_pts[node], w2, yocto::cross(p[node], edge2), vin2, vout2, s);
  }

  double C_ctrl[6][10];
  // Corners (pt = 0, 1, 2)
  for (int pt = 0; pt < 3; pt++) {
    for (int c = 0; c < 10; c++) C_ctrl[pt][c] = C_pts[pt][c];
  }
  // Off-diagonal controls: B_ij = 2 * Q(m_ij) - 0.5 * (Q(v_i) + Q(v_j))
  // pt = 3 is midpoint(v0, v1)
  for (int c = 0; c < 10; c++) {
    C_ctrl[3][c] = 2.0 * C_pts[3][c] - 0.5 * (C_pts[0][c] + C_pts[1][c]);
  }
  // pt = 4 is midpoint(v1, v2)
  for (int c = 0; c < 10; c++) {
    C_ctrl[4][c] = 2.0 * C_pts[4][c] - 0.5 * (C_pts[1][c] + C_pts[2][c]);
  }
  // pt = 5 is midpoint(v2, v0)
  for (int c = 0; c < 10; c++) {
    C_ctrl[5][c] = 2.0 * C_pts[5][c] - 0.5 * (C_pts[2][c] + C_pts[0][c]);
  }

  for (int node = 0; node < 6; node++) {
    double b_ctrl[27];
    ComputeBernstein27Controls(C_ctrl[node], lx, ly, lz, wx_len, wy_len, wz_len, b_ctrl);
    for (int m = 0; m < 27; m++) {
      out_margins[node * 27 + m] = b_ctrl[m] - penalty;
    }
  }
}

struct EvaluatedCandidateTriple {
  int triple_idx = -1;
  int inner[3] = {0};
  double margins[162] = {0};
  double min_margin = -1e30;
  vec3 grad{0, 0, 0};
  double penalty = 0.0;
  double box_span = 0.0;
};

MixtureResult EvaluateBoxCPUMixture(
    int chart, const CayleyBox &box, const ProjectiveTriangle &tri,
    int cone_samples, int max_components,
    const FarkasCageCache *cache) {
  MixtureResult res;

  double sx = 1.0, sy = 1.0, sz = 1.0;
  if (chart == 1) { sy = -1.0; sz = -1.0; }
  else if (chart == 2) { sx = -1.0; sz = -1.0; }
  vec3 s = {sx, sy, sz};

  vec3 w = box.center;
  vec3 r = box.radii;

  double lx = w.x - r.x, wx_len = 2.0 * r.x;
  double ly = w.y - r.y, wy_len = 2.0 * r.y;
  double lz = w.z - r.z, wz_len = 2.0 * r.z;

  double ex = std::max(std::abs(box.center.x - box.radii.x), std::abs(box.center.x + box.radii.x));
  double ey = std::max(std::abs(box.center.y - box.radii.y), std::abs(box.center.y + box.radii.y));
  double ez = std::max(std::abs(box.center.z - box.radii.z), std::abs(box.center.z + box.radii.z));
  double d_bound = 1.0 + ex*ex + ey*ey + ez*ez;
  double disp_error = 300.0 * d_bound * TIGHT_VERTEX_ERROR;

  double box_r = std::max({r.x, r.y, r.z});
  double safe_margin = std::min(1e-6, 1e-4 * box_r);

  auto pool = GetTrianglePool(tri, cone_samples);
  if (!pool || pool->gpu_triples.empty()) {
    return res;
  }
  res.pool_id = pool->id;

  double x0 = box.center.x, y0 = box.center.y, z0 = box.center.z;
  double num[3][3] = {
    {1.0 + x0*x0 - y0*y0 - z0*z0, 2.0*(x0*y0 - z0), 2.0*(x0*z0 + y0)},
    {2.0*(x0*y0 + z0), 1.0 - x0*x0 + y0*y0 - z0*z0, 2.0*(y0*z0 - x0)},
    {2.0*(x0*z0 - y0), 2.0*(y0*z0 + x0), 1.0 - x0*x0 - y0*y0 + z0*z0}
  };
  double denom0 = 1.0 + x0*x0 + y0*y0 + z0*z0;

  vec3 rot_vin[NUM_VERTICES];
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec3 vin = {VERTICES[k][0], VERTICES[k][1], VERTICES[k][2]};
    rot_vin[k] = {
      s.x * (num[0][0]*vin.x + num[0][1]*vin.y + num[0][2]*vin.z),
      s.y * (num[1][0]*vin.x + num[1][1]*vin.y + num[1][2]*vin.z),
      s.z * (num[2][0]*vin.x + num[2][1]*vin.y + num[2][2]*vin.z)
    };
  }

  vec3 view_center = (tri.corners[0] + tri.corners[1] + tri.corners[2]) / 3.0;
  vec3 norm_v = yocto::normalize(view_center);
  vec3 right;
  if (std::abs(norm_v.z) < 0.9) {
    right = yocto::normalize(yocto::cross(norm_v, vec3{0, 0, 1}));
  } else {
    right = yocto::normalize(yocto::cross(norm_v, vec3{1, 0, 0}));
  }
  vec3 up = yocto::normalize(yocto::cross(right, norm_v));

  vec3 t_3d{0, 0, 0};
  {
    std::vector<vec2> outer_verts(NUM_VERTICES);
    for (int i = 0; i < NUM_VERTICES; i++) {
      vec3 v = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
      outer_verts[i] = {yocto::dot(v, right), yocto::dot(v, up)};
    }
    std::vector<int> outer_hull = Hull2D::QuickHull(outer_verts);
    if (outer_hull.size() >= 3) {
      std::vector<PolygonEdge> outer_edges = GetHullEdges(outer_verts, outer_hull);
      std::vector<vec2> inner_verts(NUM_VERTICES);
      for (int i = 0; i < NUM_VERTICES; i++) {
        vec3 v_unnorm = rot_vin[i] * (1.0 / denom0);
        inner_verts[i] = {yocto::dot(v_unnorm, right), yocto::dot(v_unnorm, up)};
      }
      Clearance2D opt_c = MaximizeClearance2D(outer_edges, inner_verts);
      if (opt_c.clearance < 0.0) {
        t_3d = opt_c.translation.x * right + opt_c.translation.y * up;
      }
    }
  }

  int C = pool->contacts.size();
  std::vector<int> chosen_inners(C);
  std::vector<double> contact_center_val(C);
  const double wc_x = box.center.x, wc_y = box.center.y, wc_z = box.center.z;
  for (int c = 0; c < C; c++) {
    const auto &gc = pool->contacts[c];
    vec3 edge = {gc.edge[0], gc.edge[1], gc.edge[2]};
    vec3 out = {VERTICES[gc.vertex][0], VERTICES[gc.vertex][1], VERTICES[gc.vertex][2]};
    vec3 u = yocto::cross(view_center, edge);
    double best_val = -1e30;
    int best_k = 0;
    for (int k = 0; k < NUM_VERTICES; k++) {
      vec3 disp = (rot_vin[k] + denom0 * t_3d) - denom0 * out;
      double v = yocto::dot(u, disp);
      if (v > best_val) {
        best_val = v;
        best_k = k;
      }
    }
    chosen_inners[c] = best_k;

    vec3 vin = {VERTICES[best_k][0], VERTICES[best_k][1], VERTICES[best_k][2]};
    double C_poly[10] = {0};
    AccumulateContactPoly(C_poly, 1.0, u, vin, out, s);
    contact_center_val[c] = C_poly[0] + C_poly[1]*wc_x + C_poly[2]*wc_y + C_poly[3]*wc_z +
                            C_poly[4]*wc_x*wc_x + C_poly[5]*wc_x*wc_y + C_poly[6]*wc_x*wc_z +
                            C_poly[7]*wc_y*wc_y + C_poly[8]*wc_y*wc_z + C_poly[9]*wc_z*wc_z;
  }

  vec3 p[6];
  p[0] = tri.corners[0];
  p[1] = tri.corners[1];
  p[2] = tri.corners[2];
  p[3] = 0.5 * (tri.corners[0] + tri.corners[1]);
  p[4] = 0.5 * (tri.corners[1] + tri.corners[2]);
  p[5] = 0.5 * (tri.corners[2] + tri.corners[0]);

  // Warm-Start: If cached Farkas cages exist for this triangle pool, test them
  // first!
  if (cache) {
    for (int ci = 0; ci < cache->count; ci++) {
      const auto &hint = cache->entries[ci];
      if (hint.pool_id != pool->id || hint.num_components < 1 ||
          hint.num_components > max_components) {
        continue;
      }
      bool hint_valid = true;
      double hint_margins[4][162];
      int K_hint = hint.num_components;
      int hint_ci[4][3];

      for (int h = 0; h < K_hint; h++) {
        int t = hint.triples[h];
        if (t < 0 || t >= (int)pool->gpu_triples.size()) {
          hint_valid = false;
          break;
        }
        const auto &trip = pool->gpu_triples[t];
        int ci0 = trip.c0, ci1 = trip.c1, ci2 = trip.c2;
        hint_ci[h][0] = ci0; hint_ci[h][1] = ci1; hint_ci[h][2] = ci2;

        vec3 edge0 = {pool->contacts[ci0].edge[0], pool->contacts[ci0].edge[1],
                      pool->contacts[ci0].edge[2]};
        vec3 edge1 = {pool->contacts[ci1].edge[0], pool->contacts[ci1].edge[1],
                      pool->contacts[ci1].edge[2]};
        vec3 edge2 = {pool->contacts[ci2].edge[0], pool->contacts[ci2].edge[1],
                      pool->contacts[ci2].edge[2]};

        vec3 coeff0 = yocto::cross(edge1, edge2);
        vec3 coeff1 = yocto::cross(edge2, edge0);
        vec3 coeff2 = yocto::cross(edge0, edge1);

        double w0_min = std::min({yocto::dot(tri.corners[0], coeff0),
                                  yocto::dot(tri.corners[1], coeff0),
                                  yocto::dot(tri.corners[2], coeff0)});
        double w1_min = std::min({yocto::dot(tri.corners[0], coeff1),
                                  yocto::dot(tri.corners[1], coeff1),
                                  yocto::dot(tri.corners[2], coeff1)});
        double w2_min = std::min({yocto::dot(tri.corners[0], coeff2),
                                  yocto::dot(tri.corners[1], coeff2),
                                  yocto::dot(tri.corners[2], coeff2)});

        if (w0_min <= 1e-11 || w1_min <= 1e-11 || w2_min <= 1e-11) {
          hint_valid = false;
          break;
        }

        double penalty = d_bound * trip.weighted_defect_upper + disp_error;

        int in0 = chosen_inners[ci0];
        int in1 = chosen_inners[ci1];
        int in2 = chosen_inners[ci2];

        vec3 vin0 = {VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]};
        vec3 vout0 = {VERTICES[pool->contacts[ci0].vertex][0],
                      VERTICES[pool->contacts[ci0].vertex][1],
                      VERTICES[pool->contacts[ci0].vertex][2]};
        vec3 vin1 = {VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]};
        vec3 vout1 = {VERTICES[pool->contacts[ci1].vertex][0],
                      VERTICES[pool->contacts[ci1].vertex][1],
                      VERTICES[pool->contacts[ci1].vertex][2]};
        vec3 vin2 = {VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]};
        vec3 vout2 = {VERTICES[pool->contacts[ci2].vertex][0],
                      VERTICES[pool->contacts[ci2].vertex][1],
                      VERTICES[pool->contacts[ci2].vertex][2]};

        for (int n = 0; n < 6; n++) {
          double w0 = yocto::dot(p[n], coeff0);
          double w1 = yocto::dot(p[n], coeff1);
          double w2 = yocto::dot(p[n], coeff2);

          double C_node[10] = {0};
          AccumulateContactPoly(C_node, w0, yocto::cross(p[n], edge0), vin0,
                                vout0, s);
          AccumulateContactPoly(C_node, w1, yocto::cross(p[n], edge1), vin1,
                                vout1, s);
          AccumulateContactPoly(C_node, w2, yocto::cross(p[n], edge2), vin2,
                                vout2, s);

          double b_ctrl[27];
          ComputeBernstein27Controls(C_node, lx, ly, lz, wx_len, wy_len, wz_len,
                                     b_ctrl);

          for (int m = 0; m < 27; m++) {
            hint_margins[h][n * 27 + m] = b_ctrl[m] - penalty;
          }
        }
      }

      if (hint_valid) {
        if (K_hint == 1) {
          double min_m = 1e30;
          for (int j = 0; j < 162; j++) {
            if (hint_margins[0][j] < min_m) min_m = hint_margins[0][j];
          }
          if (min_m > 0.0) {
            res.certified = true;
            res.strategy_used = 3; // warm-start Farkas cage
            res.num_components = 1;
            res.triples[0] = hint.triples[0];
            res.chosen_ranks[0] = 0;
            res.max_rank_looked = 0;
            res.pool_tested = 1;
            res.inners[0][0] = chosen_inners[hint_ci[0][0]];
            res.inners[0][1] = chosen_inners[hint_ci[0][1]];
            res.inners[0][2] = chosen_inners[hint_ci[0][2]];
            res.weights[0] = 1.0;
            res.margin = min_m;
            res.num_candidates = 1;
            return res;
          }
        } else {
          const double *hint_ptrs[4];
          for (int h = 0; h < K_hint; h++) hint_ptrs[h] = hint_margins[h];
          double hint_alpha[4] = {0};
          double hint_margin = SolveOptimalWeights(K_hint, hint_ptrs, hint_alpha,
                                                   /*polish=*/true, /*warm_alpha=*/nullptr,
                                                   safe_margin);
          if (hint_margin > 0.0) {
            res.certified = true;
            res.strategy_used = 3; // warm-start Farkas cage
            res.num_components = K_hint;
            for (int h = 0; h < K_hint; h++) {
              res.triples[h] = hint.triples[h];
              res.chosen_ranks[h] = 0;
              res.inners[h][0] = chosen_inners[hint_ci[h][0]];
              res.inners[h][1] = chosen_inners[hint_ci[h][1]];
              res.inners[h][2] = chosen_inners[hint_ci[h][2]];
              res.weights[h] = hint_alpha[h];
            }
            res.max_rank_looked = 0;
            res.pool_tested = K_hint;
            res.margin = hint_margin;
            res.num_candidates = K_hint;
            return res;
          }
        }
      }
    }
  }

  std::vector<EvaluatedCandidateTriple> evaluated;
  evaluated.reserve(pool->gpu_triples.size());

  int full_evals = 0;
  int max_full_evals = (max_components == 1) ? 64 : 256;
  for (size_t t = 0; t < pool->gpu_triples.size(); t++) {
    const auto &trip = pool->gpu_triples[t];
    int ci0 = trip.c0, ci1 = trip.c1, ci2 = trip.c2;

    vec3 edge0 = {pool->contacts[ci0].edge[0], pool->contacts[ci0].edge[1],
                  pool->contacts[ci0].edge[2]};
    vec3 edge1 = {pool->contacts[ci1].edge[0], pool->contacts[ci1].edge[1],
                  pool->contacts[ci1].edge[2]};
    vec3 edge2 = {pool->contacts[ci2].edge[0], pool->contacts[ci2].edge[1],
                  pool->contacts[ci2].edge[2]};

    vec3 coeff0 = yocto::cross(edge1, edge2);
    vec3 coeff1 = yocto::cross(edge2, edge0);
    vec3 coeff2 = yocto::cross(edge0, edge1);

    double w0_min = std::min({yocto::dot(tri.corners[0], coeff0),
                              yocto::dot(tri.corners[1], coeff0),
                              yocto::dot(tri.corners[2], coeff0)});
    double w1_min = std::min({yocto::dot(tri.corners[0], coeff1),
                              yocto::dot(tri.corners[1], coeff1),
                              yocto::dot(tri.corners[2], coeff1)});
    double w2_min = std::min({yocto::dot(tri.corners[0], coeff2),
                              yocto::dot(tri.corners[1], coeff2),
                              yocto::dot(tri.corners[2], coeff2)});

    if (w0_min <= 1e-11 || w1_min <= 1e-11 || w2_min <= 1e-11) continue;

    double penalty = d_bound * trip.weighted_defect_upper + disp_error;

    bool is_hint_triple = false;
    if (cache) {
      for (int ci = 0; ci < cache->count && !is_hint_triple; ci++) {
        if (cache->entries[ci].pool_id == pool->id) {
          for (int h = 0; h < cache->entries[ci].num_components; h++) {
            if (cache->entries[ci].triples[h] == (int)t) {
              is_hint_triple = true;
              break;
            }
          }
        }
      }
    }

    // Fast center-pose screen: if the polynomial minus penalty at the center of
    // the box and view triangle is hopelessly negative, skip full 162 Bernstein
    // control computations. Exempt hint triples from nearby successes so
    // opposing gradient triples are retained.
    if (!is_hint_triple) {
      double w0_c = yocto::dot(view_center, coeff0);
      double w1_c = yocto::dot(view_center, coeff1);
      double w2_c = yocto::dot(view_center, coeff2);
      double center_poly = w0_c * contact_center_val[ci0] +
                           w1_c * contact_center_val[ci1] +
                           w2_c * contact_center_val[ci2];
      if (center_poly - penalty < -0.005)
        continue;
    }

    int in0 = chosen_inners[ci0];
    int in1 = chosen_inners[ci1];
    int in2 = chosen_inners[ci2];

    vec3 vin0 = {VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]};
    vec3 vout0 = {VERTICES[pool->contacts[ci0].vertex][0],
                  VERTICES[pool->contacts[ci0].vertex][1],
                  VERTICES[pool->contacts[ci0].vertex][2]};

    vec3 vin1 = {VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]};
    vec3 vout1 = {VERTICES[pool->contacts[ci1].vertex][0],
                  VERTICES[pool->contacts[ci1].vertex][1],
                  VERTICES[pool->contacts[ci1].vertex][2]};

    vec3 vin2 = {VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]};
    vec3 vout2 = {VERTICES[pool->contacts[ci2].vertex][0],
                  VERTICES[pool->contacts[ci2].vertex][1],
                  VERTICES[pool->contacts[ci2].vertex][2]};

    EvaluatedCandidateTriple et;
    et.triple_idx = (int)t;
    et.inner[0] = in0; et.inner[1] = in1; et.inner[2] = in2;

    full_evals++;


    double min_m = 1e30;
    bool early_rejected = false;

    for (int node = 0; node < 6; node++) {
      double w0 = yocto::dot(p[node], coeff0);
      double w1 = yocto::dot(p[node], coeff1);
      double w2 = yocto::dot(p[node], coeff2);

      double C_node[10] = {0};
      AccumulateContactPoly(C_node, w0, yocto::cross(p[node], edge0), vin0,
                            vout0, s);
      AccumulateContactPoly(C_node, w1, yocto::cross(p[node], edge1), vin1,
                            vout1, s);
      AccumulateContactPoly(C_node, w2, yocto::cross(p[node], edge2), vin2,
                            vout2, s);

      double b_ctrl[27];
      ComputeBernstein27Controls(C_node, lx, ly, lz, wx_len, wy_len, wz_len,
                                 b_ctrl);

      if (node == 0) {
        et.grad = {C_node[1], C_node[2], C_node[3]};
        double min_b = b_ctrl[0], max_b = b_ctrl[0];
        for (int m = 1; m < 27; m++) {
          if (b_ctrl[m] < min_b) min_b = b_ctrl[m];
          if (b_ctrl[m] > max_b) max_b = b_ctrl[m];
        }
        et.box_span = max_b - min_b;
        et.penalty = penalty;
      }

      for (int m = 0; m < 27; m++) {
        double m_val = b_ctrl[m] - penalty;
        et.margins[node * 27 + m] = m_val;
        if (m_val < min_m) min_m = m_val;
        if (!is_hint_triple && m_val < -0.05) {
          early_rejected = true;
          break;
        }
      }
      if (early_rejected) break;
    }

    if (early_rejected) continue;

    et.min_margin = min_m;

    if (min_m > 0.0) {
      res.certified = true;
      res.strategy_used = 0;
      res.num_components = 1;
      res.triples[0] = (int)t;
      res.chosen_ranks[0] = 0;
      res.max_rank_looked = 0;
      res.pool_tested = 1;
      res.inners[0][0] = in0; res.inners[0][1] = in1; res.inners[0][2] = in2;
      res.weights[0] = 1.0;
      res.margin = min_m;
      res.view_penalty = penalty;
      res.box_span = et.box_span;
      res.num_candidates = 1;
      return res;
    }

    if (et.min_margin > -0.05 || is_hint_triple) {
      evaluated.push_back(et);
      if (evaluated.size() >= 256) break;
    }
    if (full_evals >= max_full_evals) break;
  }


  res.num_candidates = (int)evaluated.size();
  if (evaluated.empty()) return res;

  std::sort(
      evaluated.begin(), evaluated.end(),
      [](const auto &a, const auto &b) { return a.min_margin > b.min_margin; });

  // Strategy 1: Corner + Center Best Subset
  int best_c0 = 0, best_c1 = 0, best_c2 = 0;
  double max_c0 = -1e30, max_c1 = -1e30, max_c2 = -1e30;
  int pool_size = std::min(64, (int)evaluated.size());
  for (int i = 0; i < pool_size; i++) {
    double min0 = 1e30, min1 = 1e30, min2 = 1e30;
    for (int m = 0; m < 27; m++) {
      min0 = std::min(min0, evaluated[i].margins[0 * 27 + m]);
      min1 = std::min(min1, evaluated[i].margins[1 * 27 + m]);
      min2 = std::min(min2, evaluated[i].margins[2 * 27 + m]);
    }
    if (min0 > max_c0) { max_c0 = min0; best_c0 = i; }
    if (min1 > max_c1) { max_c1 = min1; best_c1 = i; }
    if (min2 > max_c2) { max_c2 = min2; best_c2 = i; }
  }

  std::vector<int> corner_set = {0};
  if (std::find(corner_set.begin(), corner_set.end(), best_c0) ==
      corner_set.end())
    corner_set.push_back(best_c0);
  if (std::find(corner_set.begin(), corner_set.end(), best_c1) ==
      corner_set.end())
    corner_set.push_back(best_c1);
  if (std::find(corner_set.begin(), corner_set.end(), best_c2) ==
      corner_set.end())
    corner_set.push_back(best_c2);

  int K_corner = corner_set.size();
  const double *corner_margins[4];
  for (int k = 0; k < K_corner; k++)
    corner_margins[k] = evaluated[corner_set[k]].margins;
  double corner_alpha[4] = {0};
  double corner_margin =
      SolveOptimalWeights(K_corner, corner_margins, corner_alpha, /*polish=*/true,
                          /*warm_alpha=*/nullptr, safe_margin);

  if (corner_margin > 0.0) {
    res.certified = true;
    res.strategy_used = 1;
    res.num_components = K_corner;
    int max_r = 0;
    for (int k = 0; k < K_corner; k++) {
      int idx = corner_set[k];
      res.chosen_ranks[k] = idx;
      max_r = std::max(max_r, idx);
      res.triples[k] = evaluated[idx].triple_idx;
      res.inners[k][0] = evaluated[idx].inner[0];
      res.inners[k][1] = evaluated[idx].inner[1];
      res.inners[k][2] = evaluated[idx].inner[2];
      res.weights[k] = corner_alpha[k];
    }
    double p_sum = 0.0, span_sum = 0.0;
    for (int k = 0; k < K_corner; k++) {
      p_sum += corner_alpha[k] * evaluated[corner_set[k]].penalty;
      span_sum += corner_alpha[k] * evaluated[corner_set[k]].box_span;
    }
    res.view_penalty = p_sum;
    res.box_span = span_sum;
    res.max_rank_looked = max_r;
    res.pool_tested = pool_size;
    res.margin = corner_margin;
    return res;
  }

  // Strategy 2: Multi-Start Greedy Forward Selection with Targeted Column
  // Generation
  int num_starts = std::min(6, (int)evaluated.size());
  for (int start = 0; start < num_starts; start++) {
    std::vector<int> chosen = {start};
    double current_best_margin = evaluated[start].min_margin;
    double current_best_alpha[4] = {1.0, 0, 0, 0};

    for (int step = 2; step <= max_components; step++) {
      int K = chosen.size();
      const double *curr_margins[4];
      for (int k = 0; k < K; k++) curr_margins[k] = evaluated[chosen[k]].margins;

      std::vector<std::pair<double, int>> worst_controls;
      worst_controls.reserve(162);
      for (int j = 0; j < 162; j++) {
        double sum = 0.0;
        for (int k = 0; k < K; k++) sum += current_best_alpha[k] * curr_margins[k][j];
        worst_controls.push_back({sum, j});
      }
      std::sort(worst_controls.begin(), worst_controls.end());

      std::vector<int> cand_pool;
      cand_pool.reserve(384);
      std::vector<uint8_t> in_pool(evaluated.size(), 0);
      int base_pool = std::min(64, (int)evaluated.size());
      for (int i = 0; i < base_pool; i++) {
        cand_pool.push_back(i);
        in_pool[i] = 1;
      }

      int num_ctrls = std::min(16, (int)worst_controls.size());
      for (int w = 0; w < num_ctrls; w++) {
        int w_ctrl = worst_controls[w].second;
        struct CandScore {
          double score;
          int idx;
          bool operator>(const CandScore &other) const { return score > other.score; }
        };
        CandScore heap[20];
        int heap_sz = 0;
        int top_T = std::min(20, (int)evaluated.size());
        for (size_t c = 0; c < evaluated.size(); c++) {
          double s = evaluated[c].margins[w_ctrl];
          if (heap_sz < top_T) {
            heap[heap_sz] = {s, (int)c};
            heap_sz++;
            if (heap_sz == top_T) {
              std::make_heap(heap, heap + top_T, std::greater<CandScore>());
            }
          } else if (s > heap[0].score) {
            std::pop_heap(heap, heap + top_T, std::greater<CandScore>());
            heap[top_T - 1] = {s, (int)c};
            std::push_heap(heap, heap + top_T, std::greater<CandScore>());
          }
        }
        for (int t = 0; t < heap_sz; t++) {
          int c_idx = heap[t].idx;
          if (!in_pool[c_idx]) {
            in_pool[c_idx] = 1;
            cand_pool.push_back(c_idx);
          }
        }
      }

      // Opposing Support Vector search (Tom Idea Point 4):
      // The current mixture has residual rotation gradient R = sum alpha_k *
      // grad_k. To cancel rotation drift across the box, select candidates
      // whose gradient opposes R (i.e. maximizing dot(grad_c, -R)).
      vec3 residual_grad = {0, 0, 0};
      for (int k = 0; k < K; k++) {
        residual_grad += current_best_alpha[k] * evaluated[chosen[k]].grad;
      }
      double res_len = yocto::length(residual_grad);
      if (res_len > 1e-9) {
        struct OpposeScore {
          double score;
          int idx;
          bool operator>(const OpposeScore &other) const {
            return score > other.score;
          }
        };
        OpposeScore opp_heap[20];
        int opp_sz = 0;
        int top_opp = std::min(20, (int)evaluated.size());
        for (size_t c = 0; c < evaluated.size(); c++) {
          double s = yocto::dot(evaluated[c].grad, -residual_grad);
          if (opp_sz < top_opp) {
            opp_heap[opp_sz] = {s, (int)c};
            opp_sz++;
            if (opp_sz == top_opp)
              std::make_heap(opp_heap, opp_heap + top_opp,
                             std::greater<OpposeScore>());
          } else if (s > opp_heap[0].score) {
            std::pop_heap(opp_heap, opp_heap + top_opp,
                          std::greater<OpposeScore>());
            opp_heap[top_opp - 1] = {s, (int)c};
            std::push_heap(opp_heap, opp_heap + top_opp,
                           std::greater<OpposeScore>());
          }
        }
        for (int t = 0; t < opp_sz; t++) {
          int c_idx = opp_heap[t].idx;
          if (!in_pool[c_idx]) {
            in_pool[c_idx] = 1;
            cand_pool.push_back(c_idx);
          }
        }
      }

      int best_cand = -1;
      double best_step_margin = -1e30;
      double best_step_alpha[4] = {0};

      for (int c : cand_pool) {
        if (std::find(chosen.begin(), chosen.end(), c) != chosen.end()) continue;

        std::vector<int> test_set = chosen;
        test_set.push_back(c);
        int test_K = test_set.size();
        const double *test_margins[4];
        for (int k = 0; k < test_K; k++) test_margins[k] = evaluated[test_set[k]].margins;

        double warm[4] = {0};
        double eps = 0.15;
        for (int k = 0; k < test_K - 1; k++) warm[k] = (1.0 - eps) * current_best_alpha[k];
        warm[test_K - 1] = eps;

        double alpha[4] = {0};
        double m = SolveOptimalWeights(test_K, test_margins, alpha, /*polish=*/false, warm, safe_margin);
        if (m > best_step_margin) {
          best_step_margin = m;
          best_cand = c;
          std::memcpy(best_step_alpha, alpha, sizeof(double) * test_K);
          if (m >= safe_margin) {
            break;
          }
        }
      }

      if (best_cand >= 0 && best_step_margin > current_best_margin) {
        chosen.push_back(best_cand);
        current_best_margin = best_step_margin;
        std::memcpy(current_best_alpha, best_step_alpha, sizeof(double) * chosen.size());
        if (current_best_margin >= safe_margin) {
          break;
        }
      } else {
        break;
      }
    }

    if (current_best_margin > res.margin) {
      if (current_best_margin > 0.0) {
        // Polish the winning mixture to ensure optimal Chebyshev centering
        const double *chosen_ptrs[4];
        for (size_t k = 0; k < chosen.size(); k++) chosen_ptrs[k] = evaluated[chosen[k]].margins;
        current_best_margin = SolveOptimalWeights(chosen.size(), chosen_ptrs, current_best_alpha,
                                                  /*polish=*/true, current_best_alpha, safe_margin);
      }
      res.margin = current_best_margin;
      res.num_components = chosen.size();
      res.strategy_used = 2;
      int max_r = 0;
      for (size_t k = 0; k < chosen.size(); k++) {
        int idx = chosen[k];
        res.chosen_ranks[k] = idx;
        max_r = std::max(max_r, idx);
        res.triples[k] = evaluated[idx].triple_idx;
        res.inners[k][0] = evaluated[idx].inner[0];
        res.inners[k][1] = evaluated[idx].inner[1];
        res.inners[k][2] = evaluated[idx].inner[2];
        res.weights[k] = current_best_alpha[k];
      }
      res.max_rank_looked = max_r;
      res.pool_tested = (int)evaluated.size();
      if (current_best_margin > 0.0) {
        res.certified = true;
        double p_sum = 0.0, span_sum = 0.0;
        for (size_t k = 0; k < chosen.size(); k++) {
          p_sum += current_best_alpha[k] * evaluated[chosen[k]].penalty;
          span_sum += current_best_alpha[k] * evaluated[chosen[k]].box_span;
        }
        res.view_penalty = p_sum;
        res.box_span = span_sum;
        return res;
      }
    }
  }

  if (!evaluated.empty()) {
    if (res.num_components > 0 && res.weights[0] > 0.0) {
      double p_sum = 0.0, span_sum = 0.0;
      for (int k = 0; k < res.num_components; k++) {
        int r = res.chosen_ranks[k];
        if (r >= 0 && r < (int)evaluated.size()) {
          p_sum += res.weights[k] * evaluated[r].penalty;
          span_sum += res.weights[k] * evaluated[r].box_span;
        }
      }
      res.view_penalty = p_sum;
      res.box_span = span_sum;
    } else {
      res.view_penalty = evaluated[0].penalty;
      res.box_span = evaluated[0].box_span;
    }
  }

  return res;
}

bool ShouldSplitBox(
    int box_depth, int max_box_depth,
    int view_depth, int max_view_depth,
    double box_span, double view_penalty,
    double rot_diam, double view_diam,
    double split_kappa,
    int pre_vsplits,
    int root_view_depth,
    int box_splits_since_view) {
  if (box_depth >= max_box_depth && view_depth >= max_view_depth) {
    return true;
  }
  if (box_depth >= max_box_depth) {
    return false;
  }
  if (view_depth >= max_view_depth ||
      (pre_vsplits > 0 && view_depth >= root_view_depth + pre_vsplits)) {
    return true;
  }
  if (box_span > 0.0 && view_penalty > 0.0) {
    return (box_span >= view_penalty);
  }
  if (rot_diam >= split_kappa * view_diam) {
    return true;
  }
  if (box_splits_since_view >= 0) {
    return (box_splits_since_view < 2);
  }
  return false;
}

ViewQuadtree::ViewQuadtree() = default;
ViewQuadtree::~ViewQuadtree() = default;
ViewQuadtree::ViewQuadtree(ViewQuadtree &&) noexcept = default;
ViewQuadtree &ViewQuadtree::operator=(ViewQuadtree &&) noexcept = default;

ViewQuadtree::ViewQuadtree(const ViewQuadtree &other) : is_split(other.is_split) {
  if (is_split) {
    for (int i = 0; i < 4; i++) {
      if (other.children[i]) {
        children[i] = std::make_unique<ViewQuadtree>(*other.children[i]);
      }
    }
  }
}

ViewQuadtree &ViewQuadtree::operator=(const ViewQuadtree &other) {
  if (this == &other) return *this;
  is_split = other.is_split;
  for (int i = 0; i < 4; i++) {
    if (other.is_split && other.children[i]) {
      children[i] = std::make_unique<ViewQuadtree>(*other.children[i]);
    } else {
      children[i].reset();
    }
  }
  return *this;
}

ViewQuadtree ViewQuadtree::MakeUniform(int depth) {
  ViewQuadtree node;
  if (depth <= 0) {
    node.is_split = false;
  } else {
    node.is_split = true;
    for (int i = 0; i < 4; i++) {
      node.children[i] = std::make_unique<ViewQuadtree>(MakeUniform(depth - 1));
    }
  }
  return node;
}

std::string ViewQuadtree::ToString() const {
  if (!is_split) return ".";
  return std::format("S {} {} {} {}",
                     children[0] ? children[0]->ToString() : ".",
                     children[1] ? children[1]->ToString() : ".",
                     children[2] ? children[2]->ToString() : ".",
                     children[3] ? children[3]->ToString() : ".");
}

std::optional<ViewQuadtree> ViewQuadtree::FromString(std::string_view s) {
  size_t first = s.find_first_not_of(" \t\r\n");
  if (first == std::string_view::npos) return std::nullopt;
  size_t last = s.find_last_not_of(" \t\r\n");
  s = s.substr(first, last - first + 1);

  bool all_digits = true;
  for (char c : s) {
    if (!std::isdigit(static_cast<unsigned char>(c))) {
      all_digits = false;
      break;
    }
  }
  if (all_digits && !s.empty()) {
    int depth = 0;
    auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), depth);
    if (ec == std::errc()) {
      return MakeUniform(depth);
    }
  }

  std::vector<std::string_view> tokens;
  size_t i = 0;
  while (i < s.size()) {
    while (i < s.size() && (s[i] == ' ' || s[i] == '\t' || s[i] == '\r' || s[i] == '\n')) i++;
    if (i >= s.size()) break;
    size_t start = i;
    while (i < s.size() && s[i] != ' ' && s[i] != '\t' && s[i] != '\r' && s[i] != '\n') i++;
    tokens.push_back(s.substr(start, i - start));
  }

  size_t tok_idx = 0;
  std::function<std::optional<ViewQuadtree>()> Parse = [&]() -> std::optional<ViewQuadtree> {
    if (tok_idx >= tokens.size()) return std::nullopt;
    std::string_view tok = tokens[tok_idx++];
    if (tok == ".") {
      ViewQuadtree leaf;
      leaf.is_split = false;
      return leaf;
    } else if (tok == "S" || tok == "s") {
      ViewQuadtree node;
      node.is_split = true;
      for (int c = 0; c < 4; c++) {
        auto child = Parse();
        if (!child.has_value()) return std::nullopt;
        node.children[c] = std::make_unique<ViewQuadtree>(std::move(*child));
      }
      return node;
    }
    return std::nullopt;
  };

  auto root = Parse();
  if (!root.has_value() || tok_idx != tokens.size()) {
    return std::nullopt;
  }
  return root;
}

void ViewQuadtree::SplitPath(std::span<const int> path) {
  if (!is_split) {
    is_split = true;
    for (int i = 0; i < 4; i++) {
      children[i] = std::make_unique<ViewQuadtree>();
      children[i]->is_split = false;
    }
  }
  if (!path.empty()) {
    int c = path[0];
    if (c >= 0 && c < 4 && children[c]) {
      children[c]->SplitPath(path.subspan(1));
    }
  }
}

int ViewQuadtree::CountLeaves() const {
  if (!is_split) return 1;
  int count = 0;
  for (int i = 0; i < 4; i++) {
    count += children[i] ? children[i]->CountLeaves() : 1;
  }
  return count;
}

int ViewQuadtree::MaxDepth() const {
  if (!is_split) return 0;
  int d = 0;
  for (int i = 0; i < 4; i++) {
    if (children[i]) d = std::max(d, 1 + children[i]->MaxDepth());
  }
  return d;
}

std::vector<ViewQuadtree::LeafNode> ViewQuadtree::GetLeaves(
    const ProjectiveTriangle &root_tri) const {
  std::vector<ViewQuadtree::LeafNode> leaves;
  std::vector<int> cur_path;

  std::function<void(const ViewQuadtree &, const ProjectiveTriangle &)> Traverse =
      [&](const ViewQuadtree &node, const ProjectiveTriangle &tri) {
    if (!node.is_split) {
      leaves.push_back({cur_path, (int)cur_path.size(), tri});
      return;
    }
    auto sub = tri.Subdivide();
    for (int i = 0; i < 4; i++) {
      cur_path.push_back(i);
      if (node.children[i]) {
        Traverse(*node.children[i], sub[i]);
      } else {
        leaves.push_back({cur_path, (int)cur_path.size(), sub[i]});
      }
      cur_path.pop_back();
    }
  };

  Traverse(*this, root_tri);
  return leaves;
}

std::vector<int> FindTrianglePath(
    const ProjectiveTriangle &root_tri,
    const ProjectiveTriangle &sub_tri,
    int max_search_depth) {
  std::vector<int> path;
  vec3 target = sub_tri.Centroid();
  ProjectiveTriangle curr = root_tri;

  for (int d = 0; d < max_search_depth; d++) {
    double diff = yocto::length(curr.corners[0] - sub_tri.corners[0]) +
                  yocto::length(curr.corners[1] - sub_tri.corners[1]) +
                  yocto::length(curr.corners[2] - sub_tri.corners[2]);
    if (diff < 1e-8) break;

    auto sub = curr.Subdivide();
    int best_c = -1;
    double best_dist = 1e30;
    for (int c = 0; c < 4; c++) {
      if (sub[c].ContainsRay(target)) {
        best_c = c;
        break;
      }
      double dist = yocto::length(sub[c].Centroid() - target);
      if (dist < best_dist) {
        best_dist = dist;
        best_c = c;
      }
    }
    if (best_c >= 0) {
      path.push_back(best_c);
      curr = sub[best_c];
    } else {
      break;
    }
  }
  return path;
}

std::unordered_map<int64_t, ViewQuadtree> LoadQuadtreeSplitsFile(const std::string &path) {
  std::unordered_map<int64_t, ViewQuadtree> splits;
  std::ifstream f(path);
  if (!f.is_open()) return splits;
  std::string line;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    int64_t id;
    if (iss >> id) {
      std::string rest;
      std::getline(iss, rest);
      size_t first = rest.find_first_not_of(" \t");
      if (first != std::string::npos) {
        rest = rest.substr(first);
        size_t last = rest.find_last_not_of(" \t\r\n");
        if (last != std::string::npos) {
          rest = rest.substr(0, last + 1);
        }
        auto tree = ViewQuadtree::FromString(rest);
        if (tree.has_value()) {
          splits[id] = std::move(*tree);
        }
      }
    }
  }
  return splits;
}

bool SaveQuadtreeSplitsFile(const std::string &path, const std::unordered_map<int64_t, ViewQuadtree> &splits) {
  std::ofstream f(path);
  if (!f.is_open()) return false;
  f << "# id quadtree_or_vsplits\n";
  for (const auto &[id, tree] : splits) {
    f << id << " " << tree.ToString() << "\n";
  }
  return true;
}

std::unordered_map<int64_t, int> LoadSplitsFile(const std::string &path) {
  std::unordered_map<int64_t, int> splits;
  std::ifstream f(path);
  if (!f.is_open()) return splits;
  std::string line;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    int64_t id;
    int v;
    if (iss >> id >> v) {
      splits[id] = v;
    }
  }
  return splits;
}

bool SaveSplitsFile(const std::string &path, const std::unordered_map<int64_t, int> &splits) {
  std::ofstream f(path);
  if (!f.is_open()) return false;
  f << "# id vsplits\n";
  for (const auto &[id, v] : splits) {
    f << id << " " << v << "\n";
  }
  return true;
}

std::string MixtureSolveStats::FormatHistogramReport(int max_d, int max_bd, int max_vd) const {
  std::string out;

  // 1. Certified Leaves Depth Histogram
  if (certified_leaves > 0 && min_leaf_depth <= max_leaf_depth && max_leaf_depth < 160) {
    out += std::format("  " ACYAN("--- Certified Leaves Depth Histogram") " ({} leaves, depth {}..{}) ---\n",
                       FormatNum(certified_leaves), min_leaf_depth, max_leaf_depth);
    int start_bucket = (min_leaf_depth / 5) * 5;
    int end_bucket = (max_leaf_depth / 5) * 5;
    for (int b = start_bucket; b <= end_bucket; b += 5) {
      int64_t count = 0;
      for (int i = 0; i < 5; i++) {
        if (b + i < 160) count += leaf_depth_histogram[b + i];
      }
      if (count > 0) {
        double pct = 100.0 * (double)count / (double)certified_leaves;
        int bar_len = std::min(40, (int)std::round(pct / 2.5));
        std::string bar(bar_len, '#');
        out += std::format("    Depth {:>3}..{:<3}: {:>9} ({:>5.1f}%) |{}\n",
                           b, b + 4, FormatNum(count), pct, bar);
      }
    }
  }

  // 2. Unresolved Open Frontier (Stack / Queue) Diagnostics
  if (!solved && remaining_nodes > 0 && min_frontier_depth <= max_frontier_depth && max_frontier_depth < 160) {
    out += "\n";
    out += "  " AORANGE("================================================================================") "\n";
    out += std::format("  " ARED("⚠ UNRESOLVED SEARCH FRONTIER WARNING:") " {} open branch nodes on queue/stack\n",
                       FormatNum(remaining_nodes));
    out += "  " AYELLOW("REMINDER: These are UNVISITED BRANCH POINTS, NOT COMPLETED LEAVES!") "\n";
    int headroom = std::max(0, max_d - min_frontier_depth);
    out += std::format("  Shallowest open node: depth {} (headroom: {} levels to max_depth {})\n",
                       min_frontier_depth, headroom, max_d);
    if (headroom >= 20) {
      out += std::format("  " ARED("⚠ High expansion potential:") " a single node at depth {} can expand into\n"
                         "  millions of sub-nodes (up to 2^{} in worst case), or stall at a ceiling!\n",
                         min_frontier_depth, headroom);
    }
    out += "  " AORANGE("================================================================================") "\n";

    out += std::format("  " AORANGE("--- Open Frontier Depth Breakdown") " ({} nodes, depth {}..{}) ---\n",
                       FormatNum(remaining_nodes), min_frontier_depth, max_frontier_depth);
    int start_bucket = (min_frontier_depth / 5) * 5;
    int end_bucket = (max_frontier_depth / 5) * 5;
    for (int b = start_bucket; b <= end_bucket; b += 5) {
      int64_t count = 0;
      for (int i = 0; i < 5; i++) {
        if (b + i < 160) count += frontier_depth_histogram[b + i];
      }
      if (count > 0) {
        double pct = 100.0 * (double)count / (double)remaining_nodes;
        int h = std::max(0, max_d - (b + 4));
        int bar_len = std::min(40, (int)std::round(pct / 2.5));
        std::string bar(bar_len, '=');
        out += std::format("    Depth {:>3}..{:<3}: {:>9} ({:>5.1f}%) |{:<20} [headroom: ~{} lvls]\n",
                           b, b + 4, FormatNum(count), pct, bar, h);
      }
    }

    out += std::format("  --- Frontier Box Depth:  min={}, max={} (limit: max_box_depth={}) ---\n",
                       min_frontier_box_depth, max_frontier_box_depth, max_bd);
    out += std::format("  --- Frontier View Depth: min={}, max={} (limit: max_view_depth={}) ---\n",
                       min_frontier_view_depth, max_frontier_view_depth, max_vd);
  }

  return out;
}

MixtureSolveStats SolveCellMixture(
    const DifficultCell &cell,
    int max_depth,
    int max_box_depth,
    int max_view_depth,
    int max_nodes,
    int max_split_delta,
    int cone_samples,
    int max_components,
    double split_kappa,
    double tube_radius,
    double time_limit_sec,
    std::function<void(std::string_view)> row_callback,
    std::atomic<bool> *interrupted,
    int pre_vsplits,
    const ViewQuadtree *initial_quadtree,
    const tubetree229::TubeAtlas *tube_atlas,
    MixtureProgressCallback progress_callback) {
  MixtureSolveStats stats;
  Timer timer;
  bool all_leaves_certified = true;
  FarkasCageCache cage_cache;

  std::vector<SearchNode> stack;
  SearchNode root = cell.ToSearchNode();
  int64_t next_id = std::max<int64_t>(1000000000LL, cell.id * 1000LL);

  auto EmitRow = [&](std::string_view row) {
    stats.rows_written++;
    if (row_callback) row_callback(row);
  };

  ViewQuadtree base_tree;
  if (initial_quadtree != nullptr) {
    base_tree = *initial_quadtree;
  } else if (pre_vsplits > 0) {
    base_tree = ViewQuadtree::MakeUniform(pre_vsplits);
  }
  ViewQuadtree dynamic_tree = base_tree;

  auto FinishStats = [&](bool solved) {
    stats.solved = solved;
    stats.remaining_nodes = (int64_t)stack.size();
    stats.elapsed_seconds = timer.Seconds();
    if (!stats.solved) {
      for (const auto &n : stack) {
        auto path = FindTrianglePath(root.tri, n.tri);
        dynamic_tree.SplitPath(path);

        int d = std::clamp((int)n.depth, 0, 159);
        stats.frontier_depth_histogram[d]++;
        stats.min_frontier_depth = std::min(stats.min_frontier_depth, (int)n.depth);
        stats.max_frontier_depth = std::max(stats.max_frontier_depth, (int)n.depth);

        int bd = std::clamp((int)n.box_depth, 0, 99);
        stats.frontier_box_depth_histogram[bd]++;
        stats.min_frontier_box_depth = std::min(stats.min_frontier_box_depth, (int)n.box_depth);
        stats.max_frontier_box_depth = std::max(stats.max_frontier_box_depth, (int)n.box_depth);

        int vd = std::clamp((int)n.view_depth, 0, 29);
        stats.frontier_view_depth_histogram[vd]++;
        stats.min_frontier_view_depth = std::min(stats.min_frontier_view_depth, (int)n.view_depth);
        stats.max_frontier_view_depth = std::max(stats.max_frontier_view_depth, (int)n.view_depth);
      }
    }
    stats.learned_quadtree = std::move(dynamic_tree);
    return stats;
  };

  if (base_tree.is_split) {
    std::function<void(const SearchNode &, const ViewQuadtree &)> ExpandQuadtree =
        [&](const SearchNode &parent, const ViewQuadtree &qnode) {
      if (!qnode.is_split) {
        stack.push_back(parent);
        return;
      }
      auto sub_tris = parent.tri.Subdivide();
      int64_t c0_id = next_id++;
      int64_t c1_id = next_id++;
      int64_t c2_id = next_id++;
      int64_t c3_id = next_id++;
      EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                          parent.id, parent.parent_id, parent.depth,
                          c0_id, c1_id, c2_id, c3_id));
      int64_t c_ids[4] = {c0_id, c1_id, c2_id, c3_id};
      for (int t = 3; t >= 0; t--) {
        SearchNode c = parent;
        c.id = c_ids[t];
        c.parent_id = parent.id;
        c.depth++;
        c.view_depth++;
        c.tri = sub_tris[t];
        if (qnode.children[t]) {
          ExpandQuadtree(c, *qnode.children[t]);
        } else {
          stack.push_back(c);
        }
      }
    };
    ExpandQuadtree(root, base_tree);
  } else {
    stack.push_back(root);
  }

  while (!stack.empty()) {
    if (progress_callback && (stats.total_nodes % 1000 == 0)) {
      MixtureProgress prog;
      prog.elapsed_seconds = timer.Seconds();
      prog.total_nodes = stats.total_nodes;
      prog.certified_leaves = stats.certified_leaves;
      prog.k1_count = stats.k1_count;
      prog.mx_count = stats.corner_count + stats.greedy_count;
      prog.min_leaf_depth = stats.min_leaf_depth;
      prog.max_leaf_depth = stats.max_leaf_depth;
      prog.queue_nodes = (int64_t)stack.size();
      prog.worst_margin = stats.worst_margin;
      prog.nodes_per_sec = prog.elapsed_seconds > 0 ? (prog.total_nodes / prog.elapsed_seconds) : 0.0;
      progress_callback(prog);
    }

    if (SigIntReceived() || (interrupted && interrupted->load(std::memory_order_relaxed))) {
      return FinishStats(false);
    }
    if (time_limit_sec > 0.0 && timer.Seconds() >= time_limit_sec) {
      return FinishStats(false);
    }
    // Early exit: each node currently on the stack requires at least one evaluation
    // to certify or prune. If total_nodes + stack.size() > max_nodes, completing
    // the cell within the budget is mathematically impossible even if every remaining
    // stack node certifies immediately without further splitting.
    if (stats.total_nodes + (int64_t)stack.size() > max_nodes) {
      return FinishStats(false);
    }

    SearchNode node = stack.back();
    stack.pop_back();
    stats.total_nodes++;
    stats.max_view_depth_reached = std::max(stats.max_view_depth_reached, (int)node.view_depth);

    // 1. Pruning checks
    if (OutsideBall(node.box)) {
      stats.pruned_leaves++;
      EmitRow(std::format("PR {} {} {} RADIUS\n", node.id, node.parent_id, node.depth));
      continue;
    }

    FundamentalPruneResult fund = CheckFundamentalPrune(node.chart, node.box);
    if (fund.prune) {
      stats.pruned_leaves++;
      EmitRow(std::format("PR {} {} {} FUNDAMENTAL {}\n", node.id, node.parent_id, node.depth, fund.direction));
      continue;
    }

    double effective_tube_r = tube_radius;
    if (tube_atlas && tube_atlas->IsLoaded()) {
      double safe_r = tube_atlas->GetSafeRadiusForTriangle(node.tri.corners);
      effective_tube_r = std::max(safe_r, tube_radius);
    }

    if (effective_tube_r > 0.0 && InsideIdentityTube(node.chart, node.box, effective_tube_r)) {
      stats.pruned_leaves++;
      EmitRow(std::format("TU {} {} {} {:.17g}\n", node.id, node.parent_id, node.depth, effective_tube_r));
      continue;
    }

    if (node.chart == 0 && node.box.ContainsOrigin()) {
      if (tube_atlas && tube_atlas->IsLoaded() && effective_tube_r == 0.0 && node.view_depth < max_view_depth) {
        auto path = FindTrianglePath(root.tri, node.tri);
        dynamic_tree.SplitPath(path);

        auto sub_tris = node.tri.Subdivide();
        int64_t c_ids[4];
        for (int t = 0; t < 4; t++) c_ids[t] = next_id++;
        EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                            node.id, node.parent_id, node.depth,
                            c_ids[0], c_ids[1], c_ids[2], c_ids[3]));
        for (int t = 3; t >= 0; t--) {
          SearchNode c = node;
          c.id = c_ids[t];
          c.parent_id = node.id;
          c.depth++;
          c.view_depth++;
          c.tri = sub_tris[t];
          stack.push_back(c);
        }
        continue;
      }

      int widest = node.box.WidestAxis();
      auto [b0, b1] = node.box.Split(widest);
      SearchNode c0 = node; c0.id = next_id++; c0.parent_id = node.id; c0.depth++; c0.box_depth++; c0.box = b0;
      SearchNode c1 = node; c1.id = next_id++; c1.parent_id = node.id; c1.depth++; c1.box_depth++; c1.box = b1;
      EmitRow(std::format("SO {} {} {} {} {}\n", node.id, node.parent_id, node.depth, c0.id, c1.id));
      if (c0.box.ContainsOrigin()) {
        stack.push_back(c1);
        stack.push_back(c0);
      } else {
        stack.push_back(c0);
        stack.push_back(c1);
      }
      continue;
    }

    // 2. Mixture evaluation
    MixtureResult res = EvaluateBoxCPUMixture(node.chart, node.box, node.tri, cone_samples, max_components, &cage_cache);
    stats.count_evaluations++;
    stats.sum_candidate_pool_size += res.num_candidates;
    if (res.certified) {
      stats.certified_leaves++;
      stats.worst_margin = std::min(stats.worst_margin, res.margin);
      stats.min_leaf_depth = std::min(stats.min_leaf_depth, (int)node.depth);
      stats.max_leaf_depth = std::max(stats.max_leaf_depth, (int)node.depth);
      stats.leaf_depth_histogram[std::clamp((int)node.depth, 0, 159)]++;
      // TODO: Probably should include cone_samples here so that it's easier to interpret the triangle indices.
      if (res.strategy_used == 0) stats.k1_count++;
      else if (res.strategy_used == 1) stats.corner_count++;
      else if (res.strategy_used == 2) stats.greedy_count++;
      else if (res.strategy_used == 3) {
        stats.warm_count++;
        if (res.num_components == 1) stats.k1_count++;
        else stats.corner_count++;
      }

      // Update warm-start Farkas cage cache
      FarkasCageHint new_hint;
      new_hint.pool_id = res.pool_id;
      new_hint.num_components = res.num_components;
      for (int k = 0; k < res.num_components; k++) {
        new_hint.triples[k] = res.triples[k];
        new_hint.inners[k][0] = res.inners[k][0];
        new_hint.inners[k][1] = res.inners[k][1];
        new_hint.inners[k][2] = res.inners[k][2];
      }
      cage_cache.Insert(new_hint);

      int max_r = res.max_rank_looked;
      stats.max_candidate_rank = std::max(stats.max_candidate_rank, (int64_t)max_r);
      if (max_r == 0) stats.rank_histogram[0]++;
      else if (max_r <= 3) stats.rank_histogram[1]++;
      else if (max_r <= 7) stats.rank_histogram[2]++;
      else if (max_r <= 15) stats.rank_histogram[3]++;
      else if (max_r <= 31) stats.rank_histogram[4]++;
      else if (max_r <= 63) stats.rank_histogram[5]++;
      else if (max_r <= 127) stats.rank_histogram[6]++;
      else stats.rank_histogram[7]++;
      if (res.num_components == 1) {
        EmitRow(std::format("CE {} {} {} {} {:.17g} {} {} {}\n",
                            node.id, node.parent_id, node.depth,
                            res.triples[0], res.margin,
                            res.inners[0][0], res.inners[0][1], res.inners[0][2]));
      } else {
        std::string row = std::format("MX {} {} {} {} {:.17g}",
                                      node.id, node.parent_id, node.depth,
                                      res.num_components, res.margin);
        for (int k = 0; k < res.num_components; k++) {
          row += std::format(" {} {:.17g} {} {} {}",
                             res.triples[k], res.weights[k],
                             res.inners[k][0], res.inners[k][1], res.inners[k][2]);
        }
        row += "\n";
        EmitRow(row);
      }
      continue;
    }

    // 3. Depth limits
    if (node.depth >= cell.depth + max_split_delta ||
        node.depth >= max_depth ||
        (node.box_depth >= max_box_depth && node.view_depth >= max_view_depth)) {
      all_leaves_certified = false;
      stats.ceiling_hits++;
      stats.worst_margin = std::min(stats.worst_margin, res.margin);
      continue;
    }

    // 4. Analytical splitting decision:
    // Tradeoff governed by split_kappa:
    // - View Defect Error: penalty = d_bound * weighted_defect_upper + disp_error ~ O(view_diam).
    //   Subdividing the view triangle (SV) shrinks view defect, but has branching factor 4
    //   and invalidates the triangle candidate pool and FarkasCageCache, dropping throughput to ~30 nodes/s.
    // - Orientation Variation: Delta_box ~ 2 * ||grad F|| * r_box ~ O(rot_diam).
    //   Subdividing the Cayley box (SP) has branching factor 2, preserves the candidate pool,
    //   and achieves 60-65 nodes/s with 70%+ FarkasCageCache hit rates.
    // - When rot_diam >= split_kappa * view_diam, box orientation error dominates -> split box (SP).
    //   Otherwise, view defect error dominates -> split view (SV).
    //   (See ruperts/TOM_IDEAS_ANALYSIS.md for mathematical derivation).
    double rot_diam = 2.0 * node.box.radii[node.box.WidestAxis()];
    double view_diam = node.tri.AngularDiameter();
    bool split_box = ShouldSplitBox(
        node.box_depth, max_box_depth,
        node.view_depth, max_view_depth,
        res.box_span, res.view_penalty,
        rot_diam, view_diam,
        split_kappa, pre_vsplits, cell.view_depth);

    if (split_box) {
      int widest = node.box.WidestAxis();
      auto [b0, b1] = node.box.Split(widest);
      SearchNode c0 = node; c0.id = next_id++; c0.parent_id = node.id; c0.depth++; c0.box_depth++; c0.box = b0;
      SearchNode c1 = node; c1.id = next_id++; c1.parent_id = node.id; c1.depth++; c1.box_depth++; c1.box = b1;
      EmitRow(std::format("SP {} {} {} {} {}\n", node.id, node.parent_id, node.depth, c0.id, c1.id));
      stack.push_back(c1);
      stack.push_back(c0);
    } else {
      auto path = FindTrianglePath(root.tri, node.tri);
      dynamic_tree.SplitPath(path);

      auto sub_tris = node.tri.Subdivide();
      int64_t c_ids[4];
      for (int t = 0; t < 4; t++) c_ids[t] = next_id++;
      EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                          node.id, node.parent_id, node.depth,
                          c_ids[0], c_ids[1], c_ids[2], c_ids[3]));
      for (int t = 3; t >= 0; t--) {
        SearchNode c = node;
        c.id = c_ids[t];
        c.parent_id = node.id;
        c.depth++;
        c.view_depth++;
        c.tri = sub_tris[t];
        stack.push_back(c);
      }
    }
  }

  return FinishStats(all_leaves_certified && stack.empty());
}

MixtureSolveStats SolveCellMixtureParallel(
    const DifficultCell &cell,
    int num_threads,
    int max_depth,
    int max_box_depth,
    int max_view_depth,
    int max_nodes,
    int max_split_delta,
    int cone_samples,
    int max_components,
    double split_kappa,
    double tube_radius,
    double time_limit_sec,
    std::function<void(std::string_view)> row_callback,
    std::atomic<bool> *interrupted,
    const ViewQuadtree *initial_quadtree,
    const tubetree229::TubeAtlas *tube_atlas,
    MixtureProgressCallback progress_callback) {
  if (num_threads <= 1) {
    return SolveCellMixture(
        cell, max_depth, max_box_depth, max_view_depth,
        max_nodes, max_split_delta, cone_samples, max_components,
        split_kappa, tube_radius, time_limit_sec, row_callback,
        interrupted, 0, initial_quadtree, tube_atlas, progress_callback);
  }

  Timer timer;
  SearchNode root = cell.ToSearchNode();
  std::atomic<int64_t> next_id = std::max<int64_t>(1000000000LL, cell.id * 1000LL);

  ViewQuadtree base_tree;
  if (initial_quadtree) {
    base_tree = *initial_quadtree;
  }

  std::mutex row_mu;
  auto EmitRow = [&](std::string_view row) {
    if (row_callback) {
      std::lock_guard<std::mutex> lk(row_mu);
      row_callback(row);
    }
  };

  // 1. Expand root quadtree (or start with root)
  std::vector<SearchNode> initial_views;
  if (base_tree.is_split) {
    std::function<void(const SearchNode &, const ViewQuadtree &)> ExpandQuadtree =
        [&](const SearchNode &parent, const ViewQuadtree &qnode) {
      if (!qnode.is_split) {
        initial_views.push_back(parent);
        return;
      }
      auto sub_tris = parent.tri.Subdivide();
      int64_t c0_id = next_id.fetch_add(1);
      int64_t c1_id = next_id.fetch_add(1);
      int64_t c2_id = next_id.fetch_add(1);
      int64_t c3_id = next_id.fetch_add(1);
      EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                          parent.id, parent.parent_id, parent.depth,
                          c0_id, c1_id, c2_id, c3_id));
      int64_t c_ids[4] = {c0_id, c1_id, c2_id, c3_id};
      for (int t = 3; t >= 0; t--) {
        SearchNode c = parent;
        c.id = c_ids[t];
        c.parent_id = parent.id;
        c.depth++;
        c.view_depth++;
        c.tri = sub_tris[t];
        if (qnode.children[t]) {
          ExpandQuadtree(c, *qnode.children[t]);
        } else {
          initial_views.push_back(c);
        }
      }
    };
    ExpandQuadtree(root, base_tree);
  } else {
    initial_views.push_back(root);
  }

  // Two-tier queues:
  // view_queue: untouched root view cones (coarsest grain, independent triangles)
  // box_queue: stolen/shared Cayley sub-boxes (fine grain, within an active cone)
  std::mutex work_mu;
  std::condition_variable work_cv;
  std::vector<SearchNode> view_queue;
  for (auto it = initial_views.rbegin(); it != initial_views.rend(); ++it) {
    view_queue.push_back(*it);
  }
  std::vector<SearchNode> box_queue;

  std::mutex tree_mu;
  ViewQuadtree dynamic_tree = base_tree;

  std::atomic<int64_t> total_nodes_evaluated = 0;
  std::atomic<int64_t> certified_leaves = 0;
  std::atomic<int64_t> pruned_leaves = 0;
  std::atomic<int64_t> ceiling_hits = 0;
  std::atomic<int64_t> count_evaluations = 0;
  std::atomic<double> sum_candidate_pool_size = 0.0;
  std::atomic<int64_t> max_candidate_rank = 0;
  std::atomic<int64_t> k1_count = 0, corner_count = 0, greedy_count = 0, warm_count = 0;
  std::atomic<int64_t> rank_histogram[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  std::atomic<double> worst_margin = 1e30;
  std::atomic<int> max_view_depth_reached = (int)cell.view_depth;
  std::atomic<int> min_leaf_depth = 999999;
  std::atomic<int> max_leaf_depth = 0;
  int64_t global_leaf_depth_hist[160] = {0};
  int global_min_leaf_depth = 999999;
  int global_max_leaf_depth = 0;

  auto AtomicMin = [](std::atomic<int> &atom, int val) {
    int cur = atom.load(std::memory_order_relaxed);
    while (val < cur && !atom.compare_exchange_weak(cur, val, std::memory_order_relaxed)) {}
  };
  auto AtomicMax = [](std::atomic<int> &atom, int val) {
    int cur = atom.load(std::memory_order_relaxed);
    while (val > cur && !atom.compare_exchange_weak(cur, val, std::memory_order_relaxed)) {}
  };

  std::atomic<bool> terminate_search = false;
  std::atomic<bool> all_leaves_certified = true;
  std::atomic<int> active_workers = 0;

  std::mutex unres_mu;
  std::vector<SearchNode> unresolved_nodes;

  int actual_threads = std::max(1, num_threads);

  auto WorkerThread = [&]() {
    FarkasCageCache cage_cache;
    std::vector<SearchNode> local_stack;
    int64_t local_leaf_hist[160] = {0};
    int local_min_leaf_d = 999999, local_max_leaf_d = 0;

    while (true) {
      if (terminate_search.load(std::memory_order_relaxed) ||
          SigIntReceived() ||
          (interrupted && interrupted->load(std::memory_order_relaxed))) {
        terminate_search.store(true, std::memory_order_relaxed);
        work_cv.notify_all();
        break;
      }
      if (time_limit_sec > 0.0 && timer.Seconds() >= time_limit_sec) {
        terminate_search.store(true, std::memory_order_relaxed);
        work_cv.notify_all();
        break;
      }

      // Tier 1 & 2 work acquisition
      {
        std::unique_lock<std::mutex> lock(work_mu);
        while (view_queue.empty() && box_queue.empty() &&
               active_workers.load() > 0 && !terminate_search.load()) {
          work_cv.wait(lock);
        }

        if (terminate_search.load() ||
            (view_queue.empty() && box_queue.empty() && active_workers.load() == 0)) {
          work_cv.notify_all();
          break;
        }

        // Prefer untouched view cone first (Tier 1)
        if (!view_queue.empty()) {
          local_stack.push_back(view_queue.back());
          view_queue.pop_back();
        } else if (!box_queue.empty()) {
          // Steal coarse sub-boxes (Tier 2)
          int steal_count = std::min<int>(box_queue.size(), 2);
          for (int s = 0; s < steal_count; s++) {
            local_stack.push_back(box_queue.back());
            box_queue.pop_back();
          }
        }
        active_workers.fetch_add(1);
      }

      // Local DFS loop
      while (!local_stack.empty()) {
        if (terminate_search.load(std::memory_order_relaxed) ||
            SigIntReceived() ||
            (interrupted && interrupted->load(std::memory_order_relaxed))) {
          terminate_search.store(true, std::memory_order_relaxed);
          break;
        }
        if (time_limit_sec > 0.0 && timer.Seconds() >= time_limit_sec) {
          terminate_search.store(true, std::memory_order_relaxed);
          break;
        }

        int64_t n_eval = total_nodes_evaluated.fetch_add(1);
        if (n_eval > max_nodes) {
          terminate_search.store(true, std::memory_order_relaxed);
          break;
        }

        SearchNode node = local_stack.back();
        local_stack.pop_back();

        int vd = node.view_depth;
        int cur_mvd = max_view_depth_reached.load(std::memory_order_relaxed);
        while (vd > cur_mvd && !max_view_depth_reached.compare_exchange_weak(cur_mvd, vd)) {}

        // 1. Pruning checks
        if (OutsideBall(node.box)) {
          pruned_leaves.fetch_add(1);
          EmitRow(std::format("PR {} {} {} RADIUS\n", node.id, node.parent_id, node.depth));
          continue;
        }
        FundamentalPruneResult fund = CheckFundamentalPrune(node.chart, node.box);
        if (fund.prune) {
          pruned_leaves.fetch_add(1);
          EmitRow(std::format("PR {} {} {} FUNDAMENTAL {}\n", node.id, node.parent_id, node.depth, fund.direction));
          continue;
        }
        double effective_tube_r = tube_radius;
        if (tube_atlas && tube_atlas->IsLoaded()) {
          double safe_r = tube_atlas->GetSafeRadiusForTriangle(node.tri.corners);
          effective_tube_r = std::max(safe_r, tube_radius);
        }

        if (effective_tube_r > 0.0 && InsideIdentityTube(node.chart, node.box, effective_tube_r)) {
          pruned_leaves.fetch_add(1);
          EmitRow(std::format("TU {} {} {} {:.17g}\n", node.id, node.parent_id, node.depth, effective_tube_r));
          continue;
        }

        if (node.chart == 0 && node.box.ContainsOrigin()) {
          if (tube_atlas && tube_atlas->IsLoaded() && effective_tube_r == 0.0 && node.view_depth < max_view_depth) {
            auto sub_tris = node.tri.Subdivide();
            int64_t c_ids[4];
            for (int t = 0; t < 4; t++) c_ids[t] = next_id.fetch_add(1);
            EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                                node.id, node.parent_id, node.depth,
                                c_ids[0], c_ids[1], c_ids[2], c_ids[3]));
            for (int t = 3; t >= 0; t--) {
              SearchNode c = node;
              c.id = c_ids[t];
              c.parent_id = node.id;
              c.depth++;
              c.view_depth++;
              c.tri = sub_tris[t];
              local_stack.push_back(c);
            }
            continue;
          }

          int widest = node.box.WidestAxis();
          auto [b0, b1] = node.box.Split(widest);
          int64_t c0_id = next_id.fetch_add(1);
          int64_t c1_id = next_id.fetch_add(1);
          SearchNode c0 = node; c0.id = c0_id; c0.parent_id = node.id; c0.depth++; c0.box_depth++; c0.box = b0;
          SearchNode c1 = node; c1.id = c1_id; c1.parent_id = node.id; c1.depth++; c1.box_depth++; c1.box = b1;
          EmitRow(std::format("SO {} {} {} {} {}\n", node.id, node.parent_id, node.depth, c0.id, c1.id));
          if (c0.box.ContainsOrigin()) {
            local_stack.push_back(c1);
            local_stack.push_back(c0);
          } else {
            local_stack.push_back(c0);
            local_stack.push_back(c1);
          }
          continue;
        }

        // 2. Mixture evaluation
        MixtureResult res = EvaluateBoxCPUMixture(node.chart, node.box, node.tri, cone_samples, max_components, &cage_cache);
        count_evaluations.fetch_add(1);
        sum_candidate_pool_size.fetch_add(res.num_candidates);

        if (res.certified) {
          certified_leaves.fetch_add(1);
          double m = res.margin;
          double cur_wm = worst_margin.load(std::memory_order_relaxed);
          while (m < cur_wm && !worst_margin.compare_exchange_weak(cur_wm, m)) {}

          int d = std::clamp((int)node.depth, 0, 159);
          local_leaf_hist[d]++;
          local_min_leaf_d = std::min(local_min_leaf_d, (int)node.depth);
          local_max_leaf_d = std::max(local_max_leaf_d, (int)node.depth);
          AtomicMin(min_leaf_depth, (int)node.depth);
          AtomicMax(max_leaf_depth, (int)node.depth);

          if (res.strategy_used == 0) k1_count.fetch_add(1);
          else if (res.strategy_used == 1) corner_count.fetch_add(1);
          else if (res.strategy_used == 2) greedy_count.fetch_add(1);
          else if (res.strategy_used == 3) {
            warm_count.fetch_add(1);
            if (res.num_components == 1) k1_count.fetch_add(1);
            else corner_count.fetch_add(1);
          }

          int max_r = res.max_rank_looked;
          int64_t cur_mr = max_candidate_rank.load(std::memory_order_relaxed);
          while (max_r > cur_mr && !max_candidate_rank.compare_exchange_weak(cur_mr, max_r)) {}

          int bucket = 0;
          if (max_r == 0) bucket = 0;
          else if (max_r <= 3) bucket = 1;
          else if (max_r <= 7) bucket = 2;
          else if (max_r <= 15) bucket = 3;
          else if (max_r <= 31) bucket = 4;
          else if (max_r <= 63) bucket = 5;
          else if (max_r <= 127) bucket = 6;
          else bucket = 7;
          rank_histogram[bucket].fetch_add(1);

          FarkasCageHint new_hint;
          new_hint.pool_id = res.pool_id;
          new_hint.num_components = res.num_components;
          for (int k = 0; k < res.num_components; k++) {
            new_hint.triples[k] = res.triples[k];
            new_hint.inners[k][0] = res.inners[k][0];
            new_hint.inners[k][1] = res.inners[k][1];
            new_hint.inners[k][2] = res.inners[k][2];
          }
          cage_cache.Insert(new_hint);

          if (res.num_components == 1) {
            EmitRow(std::format("CE {} {} {} {} {:.17g} {} {} {}\n",
                                node.id, node.parent_id, node.depth,
                                res.triples[0], res.margin,
                                res.inners[0][0], res.inners[0][1], res.inners[0][2]));
          } else {
            std::string mx_row = std::format("MX {} {} {} {} {:.17g}",
                                             node.id, node.parent_id, node.depth,
                                             res.num_components, res.margin);
            for (int k = 0; k < res.num_components; k++) {
              mx_row += std::format(" {} {:.17g} {} {} {}",
                                    res.triples[k], res.weights[k],
                                    res.inners[k][0], res.inners[k][1], res.inners[k][2]);
            }
            mx_row += "\n";
            EmitRow(mx_row);
          }
          continue;
        }

        // 3. Splitting
        if (node.depth >= max_depth ||
            (node.box_depth >= max_box_depth && node.view_depth >= max_view_depth) ||
            (max_split_delta > 0 && (node.depth - cell.depth) >= max_split_delta)) {
          int ch = ceiling_hits.fetch_add(1);
          if (ch < 5) {
            fprintf(stderr, "Ceiling hit #%d: depth=%d bd=%d vd=%d center=(%.3e,%.3e,%.3e) rad=(%.3e,%.3e,%.3e) res.margin=%.3e penalty=%.3e span=%.3e\n",
                    ch, node.depth, node.box_depth, node.view_depth,
                    node.box.center.x, node.box.center.y, node.box.center.z,
                    node.box.radii.x, node.box.radii.y, node.box.radii.z,
                    res.margin, res.view_penalty, res.box_span);
          }
          all_leaves_certified.store(false, std::memory_order_relaxed);
          {
            std::lock_guard<std::mutex> lk(unres_mu);
            unresolved_nodes.push_back(node);
          }
          continue;
        }

        double rot_diam = 2.0 * node.box.radii[node.box.WidestAxis()];
        double view_diam = node.tri.AngularDiameter();
        bool split_box = ShouldSplitBox(
            node.box_depth, max_box_depth,
            node.view_depth, max_view_depth,
            res.box_span, res.view_penalty,
            rot_diam, view_diam,
            split_kappa, /*pre_vsplits=*/0, cell.view_depth);

        if (split_box) {
          int widest = node.box.WidestAxis();
          auto [b0, b1] = node.box.Split(widest);
          int64_t c0_id = next_id.fetch_add(1);
          int64_t c1_id = next_id.fetch_add(1);
          SearchNode c0 = node; c0.id = c0_id; c0.parent_id = node.id; c0.depth++; c0.box_depth++; c0.box = b0;
          SearchNode c1 = node; c1.id = c1_id; c1.parent_id = node.id; c1.depth++; c1.box_depth++; c1.box = b1;
          EmitRow(std::format("SP {} {} {} {} {}\n", node.id, node.parent_id, node.depth, c0.id, c1.id));
          local_stack.push_back(c1);
          local_stack.push_back(c0);
        } else {
          auto path = FindTrianglePath(root.tri, node.tri);
          {
            std::lock_guard<std::mutex> lk(tree_mu);
            dynamic_tree.SplitPath(path);
          }
          auto sub_tris = node.tri.Subdivide();
          int64_t c_ids[4];
          for (int t = 0; t < 4; t++) c_ids[t] = next_id.fetch_add(1);
          EmitRow(std::format("SV {} {} {} {} {} {} {}\n",
                              node.id, node.parent_id, node.depth,
                              c_ids[0], c_ids[1], c_ids[2], c_ids[3]));
          for (int t = 3; t >= 0; t--) {
            SearchNode c = node;
            c.id = c_ids[t];
            c.parent_id = node.id;
            c.depth++;
            c.view_depth++;
            c.tri = sub_tris[t];
            local_stack.push_back(c);
          }
        }

        // Tier 2 box donating: If we have excess work and other threads are idle,
        // donate coarse boxes from the base (front) of local_stack
        if (local_stack.size() >= 4) {
          std::unique_lock<std::mutex> lock(work_mu, std::try_to_lock);
          if (lock.owns_lock() && box_queue.empty()) {
            size_t donate = local_stack.size() / 2;
            for (size_t d = 0; d < donate; d++) {
              box_queue.push_back(local_stack.front());
              local_stack.erase(local_stack.begin());
            }
            work_cv.notify_one();
          }
        }
      } // end local_stack DFS loop

      {
        std::lock_guard<std::mutex> lk(unres_mu);
        for (const auto &n : local_stack) unresolved_nodes.push_back(n);
        local_stack.clear();
        for (int i = 0; i < 160; i++) {
          global_leaf_depth_hist[i] += local_leaf_hist[i];
        }
        global_min_leaf_depth = std::min(global_min_leaf_depth, local_min_leaf_d);
        global_max_leaf_depth = std::max(global_max_leaf_depth, local_max_leaf_d);
      }

      active_workers.fetch_sub(1);
      work_cv.notify_all();
    }
  };

  std::atomic<bool> monitor_stop = false;
  std::thread monitor_thread;
  if (progress_callback) {
    monitor_thread = std::thread([&]() {
      double last_report = timer.Seconds();
      while (!monitor_stop.load(std::memory_order_relaxed) &&
             !terminate_search.load(std::memory_order_relaxed)) {
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
        double now = timer.Seconds();
        if (now - last_report >= 2.0) {
          last_report = now;
          MixtureProgress prog;
          prog.elapsed_seconds = now;
          prog.total_nodes = total_nodes_evaluated.load(std::memory_order_relaxed);
          prog.certified_leaves = certified_leaves.load(std::memory_order_relaxed);
          prog.k1_count = k1_count.load(std::memory_order_relaxed);
          prog.mx_count = corner_count.load(std::memory_order_relaxed) + greedy_count.load(std::memory_order_relaxed);
          prog.min_leaf_depth = min_leaf_depth.load(std::memory_order_relaxed);
          prog.max_leaf_depth = max_leaf_depth.load(std::memory_order_relaxed);
          prog.worst_margin = worst_margin.load(std::memory_order_relaxed);
          prog.nodes_per_sec = prog.elapsed_seconds > 0 ? (prog.total_nodes / prog.elapsed_seconds) : 0.0;
          {
            std::unique_lock<std::mutex> lk(work_mu, std::try_to_lock);
            if (lk.owns_lock()) {
              prog.queue_nodes = (int64_t)(view_queue.size() + box_queue.size());
            }
          }
          progress_callback(prog);
        }
      }
    });
  }

  std::vector<std::thread> workers;
  workers.reserve(actual_threads);
  for (int t = 0; t < actual_threads; t++) {
    workers.emplace_back(WorkerThread);
  }
  for (auto &w : workers) {
    w.join();
  }

  monitor_stop = true;
  if (monitor_thread.joinable()) {
    monitor_thread.join();
  }

  // Gather any unvisited queue nodes into unresolved_nodes
  {
    std::lock_guard<std::mutex> lock(work_mu);
    for (const auto &n : view_queue) unresolved_nodes.push_back(n);
    for (const auto &n : box_queue) unresolved_nodes.push_back(n);
  }

  MixtureSolveStats stats;
  stats.total_nodes = total_nodes_evaluated.load();
  stats.certified_leaves = certified_leaves.load();
  stats.pruned_leaves = pruned_leaves.load();
  stats.ceiling_hits = ceiling_hits.load();
  stats.count_evaluations = count_evaluations.load();
  stats.sum_candidate_pool_size = sum_candidate_pool_size.load();
  stats.max_candidate_rank = max_candidate_rank.load();
  stats.k1_count = k1_count.load();
  stats.corner_count = corner_count.load();
  stats.greedy_count = greedy_count.load();
  stats.warm_count = warm_count.load();
  for (int b = 0; b < 8; b++) stats.rank_histogram[b] = rank_histogram[b].load();
  stats.worst_margin = worst_margin.load();
  stats.max_view_depth_reached = max_view_depth_reached.load();
  stats.remaining_nodes = (int64_t)unresolved_nodes.size();
  stats.elapsed_seconds = timer.Seconds();

  // Populate leaf depth statistics
  stats.min_leaf_depth = global_min_leaf_depth;
  stats.max_leaf_depth = global_max_leaf_depth;
  for (int i = 0; i < 160; i++) {
    stats.leaf_depth_histogram[i] = global_leaf_depth_hist[i];
  }

  // Populate unresolved search frontier statistics
  for (const auto &n : unresolved_nodes) {
    int d = std::clamp((int)n.depth, 0, 159);
    stats.frontier_depth_histogram[d]++;
    stats.min_frontier_depth = std::min(stats.min_frontier_depth, (int)n.depth);
    stats.max_frontier_depth = std::max(stats.max_frontier_depth, (int)n.depth);

    int bd = std::clamp((int)n.box_depth, 0, 99);
    stats.frontier_box_depth_histogram[bd]++;
    stats.min_frontier_box_depth = std::min(stats.min_frontier_box_depth, (int)n.box_depth);
    stats.max_frontier_box_depth = std::max(stats.max_frontier_box_depth, (int)n.box_depth);

    int vd = std::clamp((int)n.view_depth, 0, 29);
    stats.frontier_view_depth_histogram[vd]++;
    stats.min_frontier_view_depth = std::min(stats.min_frontier_view_depth, (int)n.view_depth);
    stats.max_frontier_view_depth = std::max(stats.max_frontier_view_depth, (int)n.view_depth);
  }

  stats.solved = all_leaves_certified.load() && unresolved_nodes.empty() && !terminate_search.load();

  if (!stats.solved) {
    for (const auto &n : unresolved_nodes) {
      auto path = FindTrianglePath(root.tri, n.tri);
      dynamic_tree.SplitPath(path);
    }
  }
  stats.learned_quadtree = std::move(dynamic_tree);
  return stats;
}

// Check whether a leaf SearchNode contains a valid Rupert passage.
// Converts the projective view and Cayley box into 3D frames, solves
// for the optimal 2D translation via MaximizeClearance2D, and
// formally verifies positive clearance using GetClearance.

std::optional<SolutionWitness> CheckSolutionWitness(
    const SearchNode &node) {
  static const Polyhedron poly = GetPolyhedron229();

  // Test multiple view directions within the leaf triangle
  // (centroid + 3 corners).
  std::vector<vec3> view_candidates = {
    node.tri.Centroid(),
    node.tri.corners[0],
    node.tri.corners[1],
    node.tri.corners[2]
  };

  // Chart sign reflections for Cayley coordinates
  double sx = 1.0, sy = 1.0, sz = 1.0;
  if (node.chart == 1) { sy = -1.0; sz = -1.0; }
  else if (node.chart == 2) { sx = -1.0; sz = -1.0; }

  vec3 center_w = {
    sx * node.box.center.x,
    sy * node.box.center.y,
    sz * node.box.center.z,
  };

  // Candidate Cayley rotation vectors to test (center + box corners)
  std::vector<vec3> rot_candidates = {center_w};
  double rx = node.box.radii.x, ry = node.box.radii.y, rz = node.box.radii.z;
  for (double dx : {-rx, rx}) {
    for (double dy : {-ry, ry}) {
      for (double dz : {-rz, rz}) {
        rot_candidates.push_back(center_w + vec3{dx, dy, dz});
      }
    }
  }

  for (const vec3 &raw_view : view_candidates) {
    vec3 view = yocto::normalize(raw_view);
    vec3 right;
    if (std::abs(view.z) < 0.9) {
      right = yocto::normalize(yocto::cross(view, vec3{0, 0, 1}));
    } else {
      right = yocto::normalize(yocto::cross(view, vec3{1, 0, 0}));
    }
    vec3 up = yocto::cross(view, right);

    frame3 outer_frame;
    outer_frame.x = vec3{right.x, up.x, view.x};
    outer_frame.y = vec3{right.y, up.y, view.y};
    outer_frame.z = vec3{right.z, up.z, view.z};
    outer_frame.o = vec3{0, 0, 0};

    std::vector<vec2> outer_verts(NUM_VERTICES);
    for (int i = 0; i < NUM_VERTICES; i++) {
      vec3 v = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
      outer_verts[i] = vec2{yocto::dot(right, v), yocto::dot(up, v)};
    }
    std::vector<int> outer_hull = Hull2D::QuickHull(outer_verts);
    if (outer_hull.size() < 3) continue;
    auto outer_edges = GetHullEdges(outer_verts, outer_hull);

    auto EvalClearance = [&](const vec3 &rot_w, Clearance2D *out_c2d,
                             frame3 *out_inner) -> double {
      double r2 = rot_w.x * rot_w.x + rot_w.y * rot_w.y + rot_w.z * rot_w.z;
      double denom = 1.0 + r2;
      double R[3][3] = {
        { (1.0 + rot_w.x*rot_w.x - rot_w.y*rot_w.y - rot_w.z*rot_w.z) / denom,
          2.0 * (rot_w.x*rot_w.y - rot_w.z) / denom,
          2.0 * (rot_w.x*rot_w.z + rot_w.y) / denom },
        { 2.0 * (rot_w.y*rot_w.x + rot_w.z) / denom,
          (1.0 - rot_w.x*rot_w.x + rot_w.y*rot_w.y - rot_w.z*rot_w.z) / denom,
          2.0 * (rot_w.y*rot_w.z - rot_w.x) / denom },
        { 2.0 * (rot_w.z*rot_w.x - rot_w.y) / denom,
          2.0 * (rot_w.z*rot_w.y + rot_w.x) / denom,
          (1.0 - rot_w.x*rot_w.x - rot_w.y*rot_w.y + rot_w.z*rot_w.z) / denom }
      };

      std::vector<vec2> inner_verts(20);
      for (int i = 0; i < 20; i++) {
        vec3 v = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
        vec3 rv = {
          R[0][0]*v.x + R[0][1]*v.y + R[0][2]*v.z,
          R[1][0]*v.x + R[1][1]*v.y + R[1][2]*v.z,
          R[2][0]*v.x + R[2][1]*v.y + R[2][2]*v.z
        };
        inner_verts[i] = vec2{yocto::dot(right, rv), yocto::dot(up, rv)};
      }

      Clearance2D c2d = MaximizeClearance2D(outer_edges, inner_verts);
      if (out_c2d)
        *out_c2d = c2d;
      if (out_inner) {
        out_inner->x = outer_frame.x * R[0][0] + outer_frame.y * R[1][0] +
                       outer_frame.z * R[2][0];
        out_inner->y = outer_frame.x * R[0][1] + outer_frame.y * R[1][1] +
                       outer_frame.z * R[2][1];
        out_inner->z = outer_frame.x * R[0][2] + outer_frame.y * R[1][2] +
                       outer_frame.z * R[2][2];
        out_inner->o = vec3{c2d.translation.x, c2d.translation.y, 0.0};
      }
      return c2d.clearance;
    };

    // First test candidates directly
    for (const vec3 &rot_w : rot_candidates) {
      Clearance2D c2d;
      frame3 inner_f;
      double c = EvalClearance(rot_w, &c2d, &inner_f);
      if (c > 0.0) {
        auto verified = GetClearance(poly, outer_frame, inner_f);
        if (verified && *verified > 0.0) {
          return SolutionWitness{outer_frame, inner_f, *verified};
        }
      }
    }

    // Fast 3D Nelder-Mead simplex inside the leaf box to locate
    // interior maximum.
    vec3 p[4] = {
      center_w,
      center_w + vec3{rx * 0.5, 0, 0},
      center_w + vec3{0, ry * 0.5, 0},
      center_w + vec3{0, 0, rz * 0.5}
    };
    double val[4];
    for (int i = 0; i < 4; i++) {
      Clearance2D c2d;
      frame3 inner_f;
      val[i] = EvalClearance(p[i], &c2d, &inner_f);
      if (val[i] > 0.0) {
        auto verified = GetClearance(poly, outer_frame, inner_f);
        if (verified && *verified > 0.0) {
          return SolutionWitness{outer_frame, inner_f, *verified};
        }
      }
    }

    for (int iter = 0; iter < 30; iter++) {
      for (int i = 0; i < 4; i++) {
        for (int j = i + 1; j < 4; j++) {
          if (val[j] > val[i]) {
            std::swap(val[i], val[j]);
            std::swap(p[i], p[j]);
          }
        }
      }
      if (val[0] > 0.0) {
        Clearance2D c2d;
        frame3 inner_f;
        EvalClearance(p[0], &c2d, &inner_f);
        auto verified = GetClearance(poly, outer_frame, inner_f);
        if (verified && *verified > 0.0) {
          return SolutionWitness{outer_frame, inner_f, *verified};
        }
      }

      vec3 x0 = (p[0] + p[1] + p[2]) * (1.0 / 3.0);
      vec3 xr = x0 + (x0 - p[3]);
      Clearance2D c2d_r;
      frame3 inner_r;
      double vr = EvalClearance(xr, &c2d_r, &inner_r);
      if (vr > 0.0) {
        auto verified = GetClearance(poly, outer_frame, inner_r);
        if (verified && *verified > 0.0)
          return SolutionWitness{outer_frame, inner_r, *verified};
      }

      if (vr > val[0]) {
        vec3 xe = x0 + (xr - x0) * 2.0;
        Clearance2D c2d_e;
        frame3 inner_e;
        double ve = EvalClearance(xe, &c2d_e, &inner_e);
        if (ve > 0.0) {
          auto verified = GetClearance(poly, outer_frame, inner_e);
          if (verified && *verified > 0.0)
            return SolutionWitness{outer_frame, inner_e, *verified};
        }
        if (ve > vr) { p[3] = xe; val[3] = ve; }
        else { p[3] = xr; val[3] = vr; }
      } else if (vr > val[2]) {
        p[3] = xr; val[3] = vr;
      } else {
        vec3 xc = x0 + (p[3] - x0) * 0.5;
        Clearance2D c2d_c;
        frame3 inner_c;
        double vc = EvalClearance(xc, &c2d_c, &inner_c);
        if (vc > 0.0) {
          auto verified = GetClearance(poly, outer_frame, inner_c);
          if (verified && *verified > 0.0)
            return SolutionWitness{outer_frame, inner_c, *verified};
        }
        if (vc > val[3]) { p[3] = xc; val[3] = vc; }
        else {
          for (int i = 1; i < 4; i++) {
            p[i] = p[0] + (p[i] - p[0]) * 0.5;
            val[i] = EvalClearance(p[i], nullptr, nullptr);
          }
        }
      }
    }
  }

  return std::nullopt;
}

SearchManager::SearchManager() : status(4) {
    cert_k_by_depth = std::make_unique<std::atomic<uint64_t>[]>(kMaxTrackDepth * kMaxTrackK);
    cert_k_by_box_depth = std::make_unique<std::atomic<uint64_t>[]>(kMaxTrackDepth * kMaxTrackK);
    cert_k_by_view_depth = std::make_unique<std::atomic<uint64_t>[]>(64 * kMaxTrackK);
    for (size_t i = 0; i < kMaxTrackDepth * kMaxTrackK; i++) {
      cert_k_by_depth[i].store(0, std::memory_order_relaxed);
      cert_k_by_box_depth[i].store(0, std::memory_order_relaxed);
    }
    for (size_t i = 0; i < 64 * kMaxTrackK; i++) {
      cert_k_by_view_depth[i].store(0, std::memory_order_relaxed);
    }
  }


void SearchManager::RecordCertification(const SearchNode &node) {
    certified_count++;
    int k = node.box_depth + 2 * node.view_depth;
    if (node.depth < kMaxTrackDepth) {
      cert_by_depth[node.depth].fetch_add(1, std::memory_order_relaxed);
      if (k < kMaxTrackK && cert_k_by_depth) {
        cert_k_by_depth[node.depth * kMaxTrackK + k].fetch_add(1, std::memory_order_relaxed);
      }
    }
    if (node.box_depth < kMaxTrackDepth) {
      cert_by_box_depth[node.box_depth].fetch_add(1, std::memory_order_relaxed);
      if (k < kMaxTrackK && cert_k_by_box_depth) {
        cert_k_by_box_depth[node.box_depth * kMaxTrackK + k].fetch_add(1, std::memory_order_relaxed);
      }
    }
    if (node.view_depth < 64) {
      cert_by_view_depth[node.view_depth].fetch_add(1, std::memory_order_relaxed);
      if (k < kMaxTrackK && cert_k_by_view_depth) {
        cert_k_by_view_depth[node.view_depth * kMaxTrackK + k].fetch_add(1, std::memory_order_relaxed);
      }
    }
  }


std::string SearchManager::FormatDepthHistogram() const {
    uint64_t total = 0;
    int max_d = 0;
    uint64_t b0 = 0, b1 = 0, b2 = 0, b3 = 0; // <40, 40-69, 70-89, 90+
    for (int d = 0; d < kMaxTrackDepth; d++) {
      uint64_t cnt = cert_by_depth[d].load(std::memory_order_relaxed);
      if (cnt > 0) {
        total += cnt;
        max_d = d;
        if (d < 40) b0 += cnt;
        else if (d < 70) b1 += cnt;
        else if (d < 90) b2 += cnt;
        else b3 += cnt;
      }
    }
    if (total == 0) return AGREY("Cert depths: none yet");
    double inv = 100.0 / total;
    return std::format(
        "Cert depths: <40: {:.1f}% " AGREY("|")
        " 40-69: {:.1f}% " AGREY("|")
        " 70-89: {:.1f}% " AGREY("|")
        " 90+: {} (max {})",
        b0 * inv, b1 * inv, b2 * inv, FormatNum(b3), max_d);
  }


void SearchManager::PrintDepthDistribution() {
    uint64_t total = 0;
    int max_d = 0;
    for (int d = 0; d < kMaxTrackDepth; d++) {
      uint64_t c = cert_by_depth[d].load(std::memory_order_relaxed);
      if (c > 0) {
        total += c;
        max_d = d;
      }
    }
    if (total == 0) return;

    double total_vol = 0.0;
    std::vector<double> vol_by_depth(max_d + 1, 0.0);
    for (int d = 0; d <= max_d; d++) {
      vol_by_depth[d] = EvalKVolume(cert_k_by_depth.get(), d);
      total_vol += vol_by_depth[d];
    }

    status.Print("\n" ABLUE("── Certified Depth Distribution (total: {}, 5D vol: {:.4f}%) ────────") "\n",
                 FormatNum(total), total_vol * 100.0);
    status.Print("  Depth range       Count     Count%   CumCount%         Vol%      CumVol%\n");
    uint64_t cum_count = 0;
    double cum_vol = 0.0;
    for (int start = 0; start <= max_d; start += 10) {
      int end = std::min(start + 9, max_d);
      uint64_t bucket_cnt = 0;
      double bucket_vol = 0.0;
      for (int d = start; d <= end; d++) {
        bucket_cnt += cert_by_depth[d].load(std::memory_order_relaxed);
        bucket_vol += vol_by_depth[d];
      }
      cum_count += bucket_cnt;
      cum_vol += bucket_vol;
      if (bucket_cnt > 0) {
        double count_pct = (100.0 * bucket_cnt) / total;
        double cum_count_pct = (100.0 * cum_count) / total;
        double vol_pct = bucket_vol * 100.0;
        double cum_vol_pct = cum_vol * 100.0;
        status.Print("  {:3d} .. {:3d}   {:11s}    {:6.2f}%    {:6.2f}%   {:10.4f}%   {:10.4f}%\n",
                     start, end, FormatNum(bucket_cnt), count_pct, cum_count_pct, vol_pct, cum_vol_pct);
      }
    }
    status.Print("  " AGREY("(Detailed discrete Depth, BoxDepth, and ViewDepth CDFs written to ")
                 "{}/depth_histogram.txt" AGREY(")") "\n", output_dir);
    status.Print(ABLUE("────────────────────────────────────────────────────────────────────────────") "\n\n");
  }


void SearchManager::WriteDepthHistogramFile(const std::string &filename) const {
    FILE *f = fopen(filename.c_str(), "w");
    if (!f) return;
    uint64_t total_nodes = 0;
    int max_d = 0;
    for (int d = 0; d < kMaxTrackDepth; d++) {
      uint64_t c = cert_by_depth[d].load(std::memory_order_relaxed);
      if (c > 0) {
        total_nodes += c;
        max_d = d;
      }
    }

    double total_vol = 0.0;
    std::vector<double> vol_by_depth(max_d + 1, 0.0);
    for (int d = 0; d <= max_d; d++) {
      vol_by_depth[d] = EvalKVolume(cert_k_by_depth.get(), d);
      total_vol += vol_by_depth[d];
    }

    auto FormatPct = [](double pct) -> std::string {
      if (pct == 0.0) return "       0.0000%";
      if (pct >= 1e-4) return std::format("{:13.6f}%", pct);
      return std::format("{:13.4e}%", pct);
    };

    std::fprintf(f, "# Rupert 229 Proof Search - Certification Depth CDF\n");
    std::fprintf(f, "Total certified nodes: %llu\n", (unsigned long long)total_nodes);
    std::fprintf(f, "Max certified depth: %d\n", max_d);
    std::fprintf(f, "Total 5D volume certified: %s\n\n", FormatPct(total_vol * 100.0).c_str());

    std::fprintf(f, "%-7s %12s %10s %11s %16s %16s\n",
                 "Depth", "Count", "Count%", "CumCount%", "5D_Vol%", "Cum_5D_Vol%");

    uint64_t cum_count = 0;
    double cum_vol = 0.0;
    for (int d = 0; d <= max_d; d++) {
      uint64_t c = cert_by_depth[d].load(std::memory_order_relaxed);
      cum_count += c;
      cum_vol += vol_by_depth[d];
      double count_pct = total_nodes > 0 ? (100.0 * c) / total_nodes : 0.0;
      double cum_count_pct = total_nodes > 0 ? (100.0 * cum_count) / total_nodes : 0.0;
      double vol_pct = vol_by_depth[d] * 100.0;
      double cum_vol_pct = cum_vol * 100.0;

      std::fprintf(f, "%5d   %12llu   %9.4f%%   %9.4f%%   %16s   %16s\n",
                   d, (unsigned long long)c, count_pct, cum_count_pct,
                   FormatPct(vol_pct).c_str(), FormatPct(cum_vol_pct).c_str());
    }

    // Box depth discrete CDF
    int max_box_d = 0;
    uint64_t total_box_nodes = 0;
    for (int d = 0; d < kMaxTrackDepth; d++) {
      uint64_t c = cert_by_box_depth[d].load(std::memory_order_relaxed);
      if (c > 0) {
        total_box_nodes += c;
        max_box_d = d;
      }
    }
    std::fprintf(f, "\n# Box Depth CDF\n");
    std::fprintf(f, "%-10s %12s %10s %11s %16s %16s\n",
                 "BoxDepth", "Count", "Count%", "CumCount%", "5D_Vol%", "Cum_5D_Vol%");
    uint64_t cum_box_count = 0;
    double cum_box_vol = 0.0;
    for (int d = 0; d <= max_box_d; d++) {
      uint64_t c = cert_by_box_depth[d].load(std::memory_order_relaxed);
      cum_box_count += c;
      double v = EvalKVolume(cert_k_by_box_depth.get(), d);
      cum_box_vol += v;
      double count_pct = total_box_nodes > 0 ? (100.0 * c) / total_box_nodes : 0.0;
      double cum_count_pct = total_box_nodes > 0 ? (100.0 * cum_box_count) / total_box_nodes : 0.0;
      std::fprintf(f, "%8d   %12llu   %9.4f%%   %9.4f%%   %16s   %16s\n",
                   d, (unsigned long long)c, count_pct, cum_count_pct,
                   FormatPct(v * 100.0).c_str(), FormatPct(cum_box_vol * 100.0).c_str());
    }

    // View depth discrete CDF
    int max_view_d = 0;
    uint64_t total_view_nodes = 0;
    for (int d = 0; d < 64; d++) {
      uint64_t c = cert_by_view_depth[d].load(std::memory_order_relaxed);
      if (c > 0) {
        total_view_nodes += c;
        max_view_d = d;
      }
    }
    std::fprintf(f, "\n# View Depth CDF\n");
    std::fprintf(f, "%-11s %12s %10s %11s %16s %16s\n",
                 "ViewDepth", "Count", "Count%", "CumCount%", "5D_Vol%", "Cum_5D_Vol%");
    uint64_t cum_view_count = 0;
    double cum_view_vol = 0.0;
    for (int d = 0; d <= max_view_d; d++) {
      uint64_t c = cert_by_view_depth[d].load(std::memory_order_relaxed);
      cum_view_count += c;
      double v = EvalKVolume(cert_k_by_view_depth.get(), d);
      cum_view_vol += v;
      double count_pct = total_view_nodes > 0 ? (100.0 * c) / total_view_nodes : 0.0;
      double cum_count_pct = total_view_nodes > 0 ? (100.0 * cum_view_count) / total_view_nodes : 0.0;
      std::fprintf(f, "%9d   %12llu   %9.4f%%   %9.4f%%   %16s   %16s\n",
                   d, (unsigned long long)c, count_pct, cum_count_pct,
                   FormatPct(v * 100.0).c_str(), FormatPct(cum_view_vol * 100.0).c_str());
    }

    fclose(f);
  }


std::string SearchManager::CLPreamble() {
    std::string s = std::format(
        "#pragma OPENCL EXTENSION cl_khr_fp64 : enable\n\n"
        "#define NUM_VERTICES {}\n\n"
        "#define MAX_CONTACTS {}\n\n"
        "#define TIGHT_VERTEX_ERROR {:.17g}\n\n"
        "__constant double VERTICES[NUM_VERTICES][3] = {{\n",
        NUM_VERTICES, MAX_GPU_CONTACTS, TIGHT_VERTEX_ERROR);
    for (int i = 0; i < NUM_VERTICES; i++) {
      s += std::format("  {{ {:.17g}, {:.17g}, {:.17g} }},\n",
                       VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]);
    }
    s += "};\n\n";
    return s;
  }


void SearchManager::InitOpenCL() {
    if (!use_gpu) return;
    cl = new CL(1);
    std::string kernel_src = CLPreamble() + Util::ReadFile("lean229.cl");
    Timer build_timer;
    auto [prg, k] = cl->BuildOneKernel(kernel_src, "EvaluateBoxes", 1);
    program = prg;
    kernel = k;
    status.Print(AGREEN("Built") " OpenCL kernel 'EvaluateBoxes' in {}\n",
                 ANSI::Time(build_timer.Seconds()));
  }


bool SearchManager::SaveCheckpoint(const std::string &path) {
    std::string tmp = path + ".tmp";
    FILE *f = fopen(tmp.c_str(), "wb");
    if (!f) return false;

    CheckpointHeader hdr;
    hdr.chart = chart;
    hdr.next_node_id = next_node_id;
    hdr.evaluated_count = evaluated_count.Read();
    hdr.certified_count = certified_count.Read();
    hdr.pruned_count = pruned_count.Read();
    hdr.split_count = split_count.Read();
    hdr.difficult_count = difficult_count.Read();
    hdr.stack_size = stack.size();

    if (fwrite(&hdr, sizeof(hdr), 1, f) != 1) {
      fclose(f);
      return false;
    }
    if (hdr.stack_size > 0) {
      if (fwrite(stack.data(), sizeof(SearchNode), hdr.stack_size, f) !=
          hdr.stack_size) {
        fclose(f);
        return false;
      }
    }
    fclose(f);

    std::string hist_path = path + ".hist";
    FILE *hf = fopen(hist_path.c_str(), "wb");
    if (hf) {
      uint64_t raw_depth[128], raw_box[128], raw_view[64];
      for (int i = 0; i < 128; i++)
        raw_depth[i] = cert_by_depth[i].load(std::memory_order_relaxed);
      for (int i = 0; i < 128; i++)
        raw_box[i] = cert_by_box_depth[i].load(std::memory_order_relaxed);
      for (int i = 0; i < 64; i++)
        raw_view[i] = cert_by_view_depth[i].load(std::memory_order_relaxed);
      fwrite(raw_depth, sizeof(uint64_t), 128, hf);
      fwrite(raw_box, sizeof(uint64_t), 128, hf);
      fwrite(raw_view, sizeof(uint64_t), 64, hf);

      std::vector<uint64_t> raw_k(320 * 256);
      for (int i = 0; i < 128 * 256; i++)
        raw_k[i] = cert_k_by_depth[i].load(std::memory_order_relaxed);
      for (int i = 0; i < 128 * 256; i++)
        raw_k[128 * 256 + i] =
            cert_k_by_box_depth[i].load(std::memory_order_relaxed);
      for (int i = 0; i < 64 * 256; i++)
        raw_k[256 * 256 + i] =
            cert_k_by_view_depth[i].load(std::memory_order_relaxed);
      fwrite(raw_k.data(), sizeof(uint64_t), 320 * 256, hf);
      fclose(hf);
    }
    WriteDepthHistogramFile(output_dir + "/depth_histogram.txt");

    std::error_code ec;
    return std::filesystem::rename(tmp, path, ec), !ec;
  }


bool SearchManager::LoadCheckpoint(const std::string &path) {
    FILE *f = fopen(path.c_str(), "rb");
    if (!f) return false;

    CheckpointHeader hdr;
    if (fread(&hdr, sizeof(hdr), 1, f) != 1) {
      status.Print("Failed to read checkpoint header from " AORANGE("{}") "\n",
                   path);
      fclose(f);
      return false;
    }
    if (hdr.magic != CheckpointHeader::kMagic) {
      status.Print("Checkpoint magic mismatch in " AORANGE("{}")
                   " (got 0x{:x}, expected 0x{:x})\n",
                   path, hdr.magic, CheckpointHeader::kMagic);
      fclose(f);
      return false;
    }
    if (hdr.version != CheckpointHeader::kVersion) {
      status.Print("Checkpoint version mismatch in " AORANGE("{}")
                   " (got {}, expected {})\n",
                   path, hdr.version, CheckpointHeader::kVersion);
      fclose(f);
      return false;
    }

    if (hdr.chart != chart) {
      status.Print("Checkpoint chart mismatch in " AORANGE("{}")
                   " (got chart {}, current chart {})\n",
                   path, hdr.chart, chart);
      fclose(f);
      return false;
    }

    next_node_id = hdr.next_node_id;
    evaluated_count.Reset(); evaluated_count += hdr.evaluated_count;
    certified_count.Reset(); certified_count += hdr.certified_count;
    pruned_count.Reset();    pruned_count += hdr.pruned_count;
    split_count.Reset();     split_count += hdr.split_count;
    difficult_count.Reset(); difficult_count += hdr.difficult_count;

    stack.resize(hdr.stack_size);
    if (hdr.stack_size > 0) {
      if (fread(stack.data(), sizeof(SearchNode), hdr.stack_size, f) !=
          hdr.stack_size) {
        status.Print("Checkpoint " AORANGE("{}")
                     " truncated while reading {} stack nodes\n",
                     path, hdr.stack_size);
        fclose(f);
        return false;
      }
    }
    fclose(f);

    std::string hist_path = path + ".hist";
    FILE *hf = fopen(hist_path.c_str(), "rb");
    if (hf) {
      uint64_t raw_depth[128], raw_box[128], raw_view[64];
      if (fread(raw_depth, sizeof(uint64_t), 128, hf) == 128 &&
          fread(raw_box, sizeof(uint64_t), 128, hf) == 128 &&
          fread(raw_view, sizeof(uint64_t), 64, hf) == 64) {
        for (int i = 0; i < 128; i++)
          cert_by_depth[i].store(raw_depth[i], std::memory_order_relaxed);
        for (int i = 0; i < 128; i++)
          cert_by_box_depth[i].store(raw_box[i], std::memory_order_relaxed);
        for (int i = 0; i < 64; i++)
          cert_by_view_depth[i].store(raw_view[i], std::memory_order_relaxed);

        std::vector<uint64_t> raw_k(320 * 256);
        if (fread(raw_k.data(), sizeof(uint64_t), 320 * 256, hf) == 320 * 256) {
          for (int i = 0; i < 128 * 256; i++)
            cert_k_by_depth[i].store(raw_k[i], std::memory_order_relaxed);
          for (int i = 0; i < 128 * 256; i++)
            cert_k_by_box_depth[i].store(raw_k[128 * 256 + i],
                                         std::memory_order_relaxed);
          for (int i = 0; i < 64 * 256; i++)
            cert_k_by_view_depth[i].store(raw_k[256 * 256 + i],
                                          std::memory_order_relaxed);
        }
      }
      fclose(hf);
    }

    return true;
  }

bool SearchManager::ContainsUncertifiedPriority(const SearchNode &node) const {
    if (!prioritize_related || active_priority.empty()) return false;
    for (const auto &p : active_priority) {
      if (p.chart == node.chart && node.box.Contains(p.w) &&
          node.tri.ContainsRay(p.view)) {
        return true;
      }
    }
    return false;
  }


std::vector<SearchManager::PriorityPoint> SearchManager::GetPriorityPoints(double max_dist) {
    std::vector<PriorityPoint> priority_points;
    // Known hard / pathological points from past runs.
    struct HardPoint {
      int chart;
      vec3 w;
      vec3 view;
      std::string_view label;
    };

    static constexpr HardPoint HARD_POINTS[] = {
        {.chart = 0,
         .w = {0.00096893310546875, -0.0012969970703125, -0.002044677734375},
         .view = {0.99999106802591464, 3.8457110645325201e-06,
                  5.0862630208333331e-06},
         .label = "Near-identity"},

        {.chart = 0,
         .w = {0.00097647309303283691, -0.0012219548225402832,
               -0.0019906759262084961},
         .view = {0.92218818586940847, 0.20787508492040183,
                  0.32612502157077433},
         .label = "Near-identity view"},

        {.chart = 0,
         .w = {0.010819882154464722, -0.016599953174591064,
               0.028645873069763184},
         .view = {0.3984395379, 0.8338690325, 0.3819795573},
         .label = "Small-rotation silhouette"},

        {.chart = 0,
         .w = {0.00030419230461120605, -0.00036638975143432617,
               -0.0005896488825480144},
         .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
         .label = "Valley"},

        {.chart = 0,
         .w = {0.0003413856029510498, -0.00041025876998901367,
               -0.00066292285919189442},
         .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
         .label = "Valley transition"},

        {.chart = 0,
         .w = {0.00041022896766662598, -0.00049299001693725586,
               -0.0007966756820678712},
         .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
         .label = "Valley depth-out"},

        {.chart = 2,
         .w = {-0.28256338834762573, -0.86962884664535522,
               -0.27563470602035522},
         .view = {0.18209315363953751, 0.30716461912403265,
                  0.51074222723642981},
         .label = "Boundary"},

        {.chart = 2,
         .w = {1.0 / 6.0, 3.0 / 8.0, 3.0 / 4.0},
         .view = {0.7073170731707317, 0.12601626016260162, 0.16666666666666666},
         .label = "Box 326 (simplex boundary)"},

        {.chart = 2,
         .w = {-1.0 / 24.0, -13.0 / 16.0, -9.0 / 16.0},
         .view = {0.7073170731707317, 0.12601626016260162, 0.16666666666666666},
         .label = "Node 290 (verified Lean certificate)"},
    };

    int hard_count = 0;
    for (const auto &hp : HARD_POINTS) {
      if (hp.chart == chart) {
        priority_points.push_back(PriorityPoint{
            .view = hp.view,
            .w = hp.w,
            .chart = hp.chart,
            .solution_id = -1,
            .label = std::string(hp.label),
        });
        hard_count++;
      }
    }

    if (hard_count > 0) {
      status.Print("Loaded " ACYAN("{}")
                   " static hard point(s) in Chart {}.\n",
                   hard_count, chart);
    }

    if (chart == 0) {
      SolutionDB db;
      Polyhedron target_poly = db.AnyPolyhedronByName("nopert_229");
      auto solutions = db.GetRelatedSolutions(target_poly, max_dist);
      if (solutions.empty()) {
        status.Print(AYELLOW("No related solutions")
                     " within max_dist = {:.17g}.\n", max_dist);
      } else {
        status.Print("Found " ACYAN("{}") " related solutions "
                     "(max_dist = {:.17g}).\n",
                     solutions.size(), max_dist);

        for (const auto &sol : solutions) {
          const frame3 &o_frame = sol.outer_frame;
          const frame3 &i_frame = sol.inner_frame;

          vec3 sol_view =
              yocto::normalize(vec3{o_frame.x.z, o_frame.y.z, o_frame.z.z});

          vec3 out_cols[3] = {o_frame.x, o_frame.y, o_frame.z};
          vec3 inn_cols[3] = {i_frame.x, i_frame.y, i_frame.z};
          double R[3][3];
          for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
              R[i][j] = yocto::dot(out_cols[i], inn_cols[j]);
            }
          }
          double denom = 1.0 + R[0][0] + R[1][1] + R[2][2];
          if (std::abs(denom) > 1e-6) {
            vec3 sol_w = {
              (R[2][1] - R[1][2]) / denom,
              (R[0][2] - R[2][0]) / denom,
              (R[1][0] - R[0][1]) / denom
            };

            // Check all 5-fold rotations around z to find representation
            // in chart 0 wedge.
            for (int k = 0; k < 5; k++) {
              double theta = 2.0 * std::numbers::pi * k / 5.0;
              double c = std::cos(theta), s = std::sin(theta);
              vec3 rot_v = {c * sol_view.x - s * sol_view.y,
                            s * sol_view.x + c * sol_view.y, sol_view.z};
              ProjectiveTriangle wedge_root;
              wedge_root.corners[0] = {1.0, 0.0, 0.0};
              wedge_root.corners[1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
              wedge_root.corners[2] = {0.0, 0.0, 1.0};
              if (wedge_root.ContainsRay(rot_v) &&
                  std::abs(sol_w.z) <= 1.0 / 3.0 + 1e-6) {
                priority_points.push_back(PriorityPoint{
                    .view = rot_v,
                    .w = sol_w,
                    .chart = 0,
                    .solution_id = sol.id,
                    .label = "solution",
                });
                break;
              }
            }
          }
        }
        status.Print("Loaded " ACYAN("{}") " candidate solution poses "
                     "in Chart 0 (max_euclidean_dist = {}).\n",
                     priority_points.size() - hard_count, max_dist);
      }
    }
    active_priority = priority_points;
    num_priority_points = (int)priority_points.size();
    return priority_points;
  }

  // Prunes priority points that are not contained in any remaining node on the
  // stack (e.g. points that were already certified and eliminated prior to a
  // checkpoint, or outside the initial domain).

void SearchManager::FilterPriorityPointsToStack() {
    if (!prioritize_related || active_priority.empty() || stack.empty()) return;
    int initial_count = (int)active_priority.size();
    std::vector<PriorityPoint> remaining;
    remaining.reserve(active_priority.size());

    for (const auto &p : active_priority) {
      bool found = false;
      for (const auto &node : stack) {
        if (p.chart == node.chart &&
            node.box.Contains(p.w) &&
            node.tri.ContainsRay(p.view)) {
          found = true;
          break;
        }
      }
      if (found) {
        remaining.push_back(p);
      }
    }

    int removed = initial_count - (int)remaining.size();
    if (removed > 0) {
      status.Print(
          "Filtered out " ACYAN("{}") " priority point(s) not in remaining volume "
          "({} active remaining in stack).\n",
          removed, remaining.size());
    }
    active_priority = std::move(remaining);
    num_priority_points = (int)active_priority.size();
  }

  // Computes exact completed domain volume fraction in [0.0, 1.0] by
  // evaluating uncertified leaf weights on the stack using depth-bucketed
  // Horner evaluation. Zero floating-point accumulation error.

double SearchManager::CompletedFraction() const {
  int root_k = root_box_depth + 2 * root_view_depth;
  uint64_t stack_k[256] = {0};
  for (const auto &node : stack) {
    int k = (node.box_depth + 2 * node.view_depth) - root_k;
    if (k < 0) k = 0;
    if (k < 256) stack_k[k]++;
  }
  for (const auto &node : current_batch) {
    int k = (node.box_depth + 2 * node.view_depth) - root_k;
    if (k < 0) k = 0;
    if (k < 256) stack_k[k]++;
  }
  double pending_vol = 0.0;
  for (int k = 255; k > 0; k--) {
    pending_vol = (pending_vol + stack_k[k]) * 0.5;
  }
  pending_vol += stack_k[0];
  return std::clamp(1.0 - pending_vol, 0.0, 1.0);
}


void SearchManager::ResetState() {
  stack.clear();
  current_batch.clear();
  root_box_depth = 0;
  root_view_depth = 0;
  pre_vsplits = 0;
  ctr_loops.Reset();
  evaluated_count.Reset();
  certified_count.Reset();
  pruned_count.Reset();
  split_count.Reset();
  difficult_count.Reset();
  timed_out = false;
  max_view_depth_reached = 0;
  row_buffer.clear();
  for (int i = 0; i < 128; i++) cert_by_depth[i].store(0, std::memory_order_relaxed);
  for (int i = 0; i < 128; i++) cert_by_box_depth[i].store(0, std::memory_order_relaxed);
  for (int i = 0; i < 64; i++) cert_by_view_depth[i].store(0, std::memory_order_relaxed);
  if (cert_k_by_depth) {
    for (size_t i = 0; i < 128 * 256; i++) {
      cert_k_by_depth[i].store(0, std::memory_order_relaxed);
      cert_k_by_box_depth[i].store(0, std::memory_order_relaxed);
    }
    for (size_t i = 0; i < 64 * 256; i++) {
      cert_k_by_view_depth[i].store(0, std::memory_order_relaxed);
    }
  }
}

void SearchManager::InitRoot() {
  ResetState();
  next_node_id = 0;

  SearchNode root;
  root.id = next_node_id++;
  root.parent_id = -1;
  root.chart = chart;
  root.box.center = {0.0, 0.0, 0.0};

  if (chart == 0) {
    // 5-fold fundamental domain: z in [-1/3, 1/3]
    root.box.radii = {1.0, 1.0, 1.0 / 3.0};
  } else if (chart == 1) {
    // 5-fold fundamental domain: y in [-1/3, 1/3]
    root.box.radii = {1.0, 1.0 / 3.0, 1.0};
  } else if (chart == 2) {
    // 5-fold fundamental domain: x in [-1/3, 1/3]
    root.box.radii = {1.0 / 3.0, 1.0, 1.0};
  } else {
    root.box.radii = {1.0, 1.0, 1.0};
  }

  // Root projective view is UPPER_WEDGE_PROJECTIVE_ROOT, pre-split
  // into 4 sub-wedges.
  ProjectiveTriangle wedge_root;
  wedge_root.corners[0] = {1.0, 0.0, 0.0};
  wedge_root.corners[1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  wedge_root.corners[2] = {0.0, 0.0, 1.0};
  auto sub_wedges = wedge_root.Subdivide();

  int priority_idx = -1;
  for (int i = 0; i < 4; i++) {
    SearchNode child = root;
    child.tri = sub_wedges[i];
    if (ContainsUncertifiedPriority(child)) {
      priority_idx = i;
      break;
    }
  }

  SearchNode root_children[4];
  for (int i = 0; i < 4; i++) {
    root_children[i] = root;
    root_children[i].id = next_node_id++;
    root_children[i].parent_id = root.id;
    root_children[i].view_depth = 1;
    root_children[i].depth = 1;
    root_children[i].tri = sub_wedges[i];
  }

  for (int i = 0; i < 4; i++) {
    if (i == priority_idx) continue;
    stack.push_back(root_children[i]);
  }
  if (priority_idx >= 0) {
    stack.push_back(root_children[priority_idx]);
  }
}

void SearchManager::FlushRowsWithLock() {
  if (row_file) {
    Print(row_file, "{}", row_buffer);
  }
  row_buffer.clear();
}

void SearchManager::FlushRows() {
  MutexLock ml(&row_mutex);
  FlushRowsWithLock();
}

void SearchManager::OutputRow(std::string_view row) {
  if (row_callback) {
    row_callback(row);
  }
  if (write_row_file && row_file) {
    MutexLock ml(&row_mutex);
    row_buffer.append(row);
    if (row_buffer.size() > 32768) {
      FlushRowsWithLock();
    }
  }
}


void SearchManager::Run() {
  if (write_row_file || write_difficult_file || enable_checkpoint) {
    std::filesystem::create_directories(output_dir);
  }
  std::string log_path =
      std::format("{}/chart{}.rows.log", output_dir, chart);
  std::string ckpt_path =
      std::format("{}/chart{}.checkpoint.bin", output_dir, chart);
  difficult_path =
      std::format("{}/chart{}.difficult", output_dir, chart);

  if (show_banner) {
    status.Print(ACYAN("=== Nopert #229 Proof Search ===\n"));
    if (deep_escalate_depth > 0) {
      status.Print("Chart: {}, Batch Size: {}, Candidates: {}, Cone Samples: {} (escalate to {} at depth {}, {} at depth {}), "
                   "Max Depth: {} (box={}, view={}), Device: {}\n",
                   chart, batch_size,
                   num_candidates == 0 ? "all" : std::to_string(num_candidates),
                   cone_samples, escalate_cone_samples, escalate_depth,
                   deep_escalate_cone_samples, deep_escalate_depth,
                   max_depth, max_box_depth, max_view_depth,
                   use_gpu ? "OpenCL (GPU/CPU)" : "Multi-threaded CPU");
    } else {
      status.Print("Chart: {}, Batch Size: {}, Candidates: {}, Cone Samples: {} (escalate to {} at depth {}), "
                   "Max Depth: {} (box={}, view={}), Device: {}\n",
                   chart, batch_size,
                   num_candidates == 0 ? "all" : std::to_string(num_candidates),
                   cone_samples, escalate_cone_samples, escalate_depth,
                   max_depth, max_box_depth, max_view_depth,
                   use_gpu ? "OpenCL (GPU/CPU)" : "Multi-threaded CPU");
    }
  }

  if (prioritize_related) {
    active_priority = GetPriorityPoints(related_epsilon);
  }

  bool resumed = false;
  if (stack.empty()) {
    if (auto_init_root) {
      if (enable_checkpoint && resume && std::filesystem::exists(ckpt_path)) {
        if (LoadCheckpoint(ckpt_path)) {
          resumed = true;
          if (verbose_status) {
            status.Print(AGREEN("Resumed")
                         " from checkpoint: {} pending nodes on "
                         "stack, {} evaluated, {} certified, {} difficult, {} pruned\n",
                         FormatNum(stack.size()),
                         FormatNum(evaluated_count.Read()),
                         FormatNum(certified_count.Read()),
                         FormatNum(difficult_count.Read()),
                         FormatNum(pruned_count.Read()));
          }
        } else {
          if (verbose_status) {
            status.Print(
                "Failed to read checkpoint " AORANGE("{}")
                "; starting fresh.\n",
                ckpt_path);
          }
          std::error_code ec;
          std::filesystem::remove(ckpt_path, ec);
          InitRoot();
        }
      } else {
        if (!resume && std::filesystem::exists(ckpt_path)) {
          std::error_code ec;
          std::filesystem::remove(ckpt_path, ec);
        }
        InitRoot();
      }
    } else {
      // Nothing on stack and auto_init_root is false: nothing to search.
      return;
    }
  }

  if (prioritize_related) {
    FilterPriorityPointsToStack();
  }

  if (write_row_file) {
    if (resumed) {
      row_file = fopen(log_path.c_str(), "a");
      CHECK(row_file) << log_path;
      if (show_banner) status.Print("Appending log to: {}\n", log_path);
    } else {
      std::error_code ec;
      std::filesystem::remove(log_path, ec);
      row_file = fopen(log_path.c_str(), "w");
      CHECK(row_file) << log_path;
      if (show_banner) status.Print("Writing fresh log to: {}\n", log_path);
      if (auto_init_root) {
        OutputRow("SV 0 -1 0 1 2 3 4\n");
      }
    }
  }

  if (write_difficult_file) {
    if (resumed) {
      if (std::filesystem::exists(difficult_path)) {
        difficult_file = fopen(difficult_path.c_str(), "a");
      } else {
        difficult_file = fopen(difficult_path.c_str(), "w");
        if (difficult_file) {
          Print(difficult_file,
                "# id parent_id depth box_depth view_depth chart "
                "cx cy cz rx ry rz "
                "v0x v0y v0z v1x v1y v1z v2x v2y v2z "
                "best_margin\n");
          std::fflush(difficult_file);
        }
      }
      CHECK(difficult_file) << difficult_path;
      if (show_banner) status.Print("Difficult cells file: {}\n", difficult_path);
    } else {
      std::error_code ec;
      std::filesystem::remove(difficult_path, ec);
      difficult_file = fopen(difficult_path.c_str(), "w");
      CHECK(difficult_file) << difficult_path;
      Print(difficult_file,
            "# id parent_id depth box_depth view_depth chart "
            "cx cy cz rx ry rz "
            "v0x v0y v0z v1x v1y v1z v2x v2y v2z "
            "best_margin\n");
      std::fflush(difficult_file);
      if (show_banner) status.Print("Writing fresh difficult cells to: {}\n", difficult_path);
    }
  }

    Timer timer;
    Periodically progress_per(1.0);
    Periodically checkpoint_per(60.0);
    Periodically where_per(120.0);
    Periodically suspicious_per(30.0);
    Periodically depth_out_per(10.0);

    // Buffers for GPU batch
    std::vector<GpuBox> gpu_boxes;
    std::vector<GpuContact> all_contacts;
    std::vector<GpuTriple> all_triples;
    std::vector<GpuResult> results;
    current_batch.clear();

    if (!auto_init_root && root_box_depth == 0 && root_view_depth == 0 && !stack.empty()) {
      int min_b = stack[0].box_depth;
      int min_v = stack[0].view_depth;
      for (const auto &n : stack) {
        min_b = std::min(min_b, (int)n.box_depth);
        min_v = std::min(min_v, (int)n.view_depth);
      }
      root_box_depth = min_b;
      root_view_depth = min_v;
    }

    while (!stack.empty() && !sigint_received.load() &&
           !(stop_requested && stop_requested->load())) {
      if (max_seconds > 0.0 && timer.Seconds() >= max_seconds) {
        timed_out = true;
        break;
      }
      if (max_nodes > 0 && evaluated_count.Read() + (int64_t)stack.size() > max_nodes) {
        timed_out = true;
        break;
      }
      MaybeMiniStatus("stack");
      ctr_loops++;
      const size_t target_pool_size = (size_t)batch_size * 2;
      int count = 0;
      current_batch.clear();

      // First, extract any uncertified priority nodes into current_batch
      if (prioritize_related && !active_priority.empty()) {
        for (int i = (int)stack.size() - 1;
             i >= 0 && current_batch.size() < (size_t)batch_size; i--) {
          if (ContainsUncertifiedPriority(stack[i])) {
            current_batch.push_back(stack[i]);
            stack[i] = std::move(stack.back());
            stack.pop_back();
            if (i < (int)stack.size()) {
              i++; // Re-check slot i with the swapped-in element
            }
          }
        }
      }

      size_t remaining = batch_size - current_batch.size();
      if (stack.size() > remaining) {
        if (stack.size() < target_pool_size) {
          // Frontier not yet wide enough to keep GPU saturated.
          // Expand shallowest nodes to branch out the frontier!
          std::nth_element(stack.begin(), stack.begin() + remaining,
                           stack.end(),
                           [](const SearchNode &a, const SearchNode &b) {
                             return a.depth < b.depth;
                           });
          current_batch.insert(current_batch.end(), stack.begin(),
                               stack.begin() + remaining);
          stack.erase(stack.begin(), stack.begin() + remaining);
        } else {
          // Pure DFS: take directly from back of stack (LIFO).
          // Crucial: do NOT run std::nth_element here! Running
          // std::nth_element scrambles the stack order and destroys
          // spatial locality, mixing nodes from thousands of open
          // branches and exploding unique view triangles. Directly
          // taking from the back keeps all nodes in the same local
          // branch and sharing the SAME view triangle, certifying and
          // closing branches quickly.
          size_t pop_count = remaining;
          current_batch.insert(current_batch.end(), stack.end() - pop_count,
                               stack.end());
          stack.erase(stack.end() - pop_count, stack.end());
        }
      } else {
        current_batch.insert(current_batch.end(), stack.begin(), stack.end());
        stack.clear();
      }
      count = current_batch.size();

      gpu_boxes.clear();
      all_contacts.clear();
      all_triples.clear();
      results.assign(count, GpuResult{});

      // Periodically show the deepest node from the batch, so we can
      // note places where we got stuck, etc.
      where_per.RunIf([&]{
          if (current_batch.empty()) return;
          double completed_pct = 100.0 * CompletedFraction();
          size_t best_idx = 0;
          for (size_t i = 1; i < current_batch.size(); i++) {
            if (current_batch[i].depth > current_batch[best_idx].depth) {
              best_idx = i;
            }
          }
          const auto &node = current_batch[best_idx];
          status.Print("[{}] {:.5f}%  |  Deepest in batch: " ACYAN("#{}") "\n"
                       "  depth {}, box_depth {}, view_depth {}\n"
                       "  radii ({:.17g}, {:.17g}, {:.17g}))\n"
                       "  box ({:.17g}, {:.17g}, {:.17g})\n",
                       ANSI::Time(timer.Seconds()),
                       completed_pct,
                       node.id,
                       node.depth, node.box_depth, node.view_depth,
                       node.box.radii.x, node.box.radii.y, node.box.radii.z,
                       node.box.center.x, node.box.center.y, node.box.center.z);
        });

      // Mutex guards the stack and eval indices.
      std::mutex mu;
      std::vector<int> eval_indices;
      eval_indices.reserve(count);

      ParallelComp(count, [&](int64_t i) {
          const auto &node = current_batch[i];
          if (OutsideBall(node.box)) {
            pruned_count++;
            RecordCertification(node);
            OutputRow(std::format("PR {} {} {} RADIUS\n",
                                  node.id, node.parent_id, node.depth));
            return;
          }

          FundamentalPruneResult fund =
            CheckFundamentalPrune(node.chart, node.box);

          if (fund.prune) {
            pruned_count++;
            RecordCertification(node);
            OutputRow(std::format("PR {} {} {} FUNDAMENTAL {}\n",
                                  node.id, node.parent_id, node.depth,
                                  fund.direction));

          } else {
            double effective_tube_r = tube_radius;
            if (tube_atlas && tube_atlas->IsLoaded()) {
              double safe_r = tube_atlas->GetSafeRadiusForTriangle(node.tri.corners);
              effective_tube_r = std::max(safe_r, tube_radius);
            }

            if (effective_tube_r > 0.0 && InsideIdentityTube(node.chart, node.box, effective_tube_r)) {
              pruned_count++;
              RecordCertification(node);
              OutputRow(std::format("TU {} {} {} {:.17g}\n",
                                    node.id, node.parent_id, node.depth,
                                    effective_tube_r));

            } else if (node.chart == 0 && node.box.ContainsOrigin()) {
              if (tube_atlas && tube_atlas->IsLoaded() && effective_tube_r == 0.0 && node.view_depth < max_view_depth) {
                split_count++;
                auto sub_tris = node.tri.Subdivide();
                int64_t child_ids[4] = {-1, -1, -1, -1};
                for (int t = 3; t >= 0; t--) {
                  SearchNode child = node;
                  child.id = next_node_id++;
                  child.parent_id = node.id;
                  child.depth = node.depth + 1;
                  child.view_depth = node.view_depth + 1;
                  child.box_splits_since_view = 0;
                  child.tri = sub_tris[t];
                  child_ids[t] = child.id;
                  MutexLock ml(&mu);
                  stack.push_back(child);
                }
                OutputRow(std::format("SV {} {} {} {} {} {} {}\n", node.id,
                                      node.parent_id, node.depth,
                                      child_ids[0], child_ids[1], child_ids[2], child_ids[3]));
              } else {
                int widest = node.box.WidestAxis();
                auto [b0, b1] = node.box.Split(widest);

                SearchNode child0 = node;
                child0.id = next_node_id++;
                child0.parent_id = node.id;
                child0.depth = node.depth + 1;
                child0.box_depth = node.box_depth + 1;
                child0.box_splits_since_view = node.box_splits_since_view + 1;
                child0.box = b0;

                SearchNode child1 = node;
                child1.id = next_node_id++;
                child1.parent_id = node.id;
                child1.depth = node.depth + 1;
                child1.box_depth = node.box_depth + 1;
                child1.box_splits_since_view = node.box_splits_since_view + 1;
                child1.box = b1;

                split_count++;
                OutputRow(std::format("SO {} {} {} {} {}\n",
                                      node.id, node.parent_id, node.depth,
                                      child0.id, child1.id));

                if (child0.box.ContainsOrigin()) {
                  MutexLock ml(&mu);
                  stack.push_back(child1);
                  stack.push_back(child0);
                } else {
                  MutexLock ml(&mu);
                  stack.push_back(child0);
                  stack.push_back(child1);
                }
              }
            } else {
            auto tpool = GetTrianglePool(node.tri, EffectiveConeSamples(node));
            if (tpool->gpu_triples.empty()) {
              split_count++;
              auto sub_tris = node.tri.Subdivide();
              int64_t child_ids[4] = {-1, -1, -1, -1};
              for (int t = sub_tris.size() - 1; t >= 0; t--) {
                SearchNode child = node;
                child.id = next_node_id++;
                child.parent_id = node.id;
                child.depth = node.depth + 1;
                child.view_depth = node.view_depth + 1;
                child.box_splits_since_view = 0;
                child.tri = sub_tris[t];
                child_ids[t] = child.id;
                MutexLock ml(&mu);
                stack.push_back(child);
              }
              OutputRow(std::format("SV {} {} {} {} {} {} {}\n", node.id,
                                    node.parent_id, node.depth,
                                    child_ids[0], child_ids[1], child_ids[2], child_ids[3]));
            } else {
              MutexLock ml(&mu);
              eval_indices.push_back(i);
            }
          }
        }
      }, num_threads);

      if (!eval_indices.empty()) {
        struct EvalItem {
          int batch_idx;
          std::shared_ptr<const TrianglePool> pool;
        };
        std::vector<EvalItem> eval_items(eval_indices.size());
        ParallelComp(eval_indices.size(), [&](int64_t i) {
          int idx = eval_indices[i];
          const auto &node = current_batch[idx];
          eval_items[i] = {idx, GetTrianglePool(node.tri, EffectiveConeSamples(node))};
          MaybeMiniStatus("tris");
          }, num_threads);

        // Collate by triangle pool ID: groups identical triangles together so GPU work-items
        // within every warp execute in lockstep on identical candidate triples, with 100%
        // broadcast cache hits and zero memory divergence.
        MaybeMiniStatus("sort");
        std::sort(eval_items.begin(), eval_items.end(),
                  [](const EvalItem &a, const EvalItem &b) {
                    return a.pool->id < b.pool->id;
                  });

        static constexpr size_t MAX_POOLS_PER_DISPATCH = 256;
        static constexpr size_t MAX_TRIPLES_PER_DISPATCH = 32 * 1024 * 1024;
        size_t item_start = 0;
        while (item_start < eval_items.size()) {
          // Pass 1: Identify slice [item_start, item_end) and compute exact buffer capacities
          size_t item_end = item_start;
          uint64_t current_id = 0;
          size_t distinct_pools = 0;
          size_t total_contacts = 0;
          size_t total_triples = 0;
          while (item_end < eval_items.size()) {
            if (item_end == item_start || eval_items[item_end].pool->id != current_id) {
              const auto &tpool = eval_items[item_end].pool;
              size_t n_trip = tpool->gpu_triples.size();
              if (num_candidates > 0 && num_candidates < n_trip) {
                n_trip = num_candidates;
              }
              if (distinct_pools >= MAX_POOLS_PER_DISPATCH ||
                  total_triples + n_trip > MAX_TRIPLES_PER_DISPATCH) {
                if (distinct_pools > 0) break;
              }
              current_id = tpool->id;
              distinct_pools++;
              total_triples += n_trip;
              total_contacts += tpool->contacts.size();
            }
            item_end++;
          }

          size_t chunk_size = item_end - item_start;
          std::vector<GpuBox> active_gpu_boxes;
          active_gpu_boxes.reserve(chunk_size);
          std::vector<GpuResult> chunk_results(chunk_size);

          all_contacts.clear();
          all_contacts.reserve(total_contacts);
          all_triples.clear();
          all_triples.reserve(total_triples);

          // Pass 2: Populate contacts, triples, and boxes directly without hash map.
          // Because eval_items is sorted by pool->id, all identical pools are contiguous.
          MaybeMiniStatus("items");

          uint64_t last_pool_id = 0;
          int cur_contact_offset = 0;
          int cur_triple_offset = 0;
          int cur_num_triples = 0;
          int cur_num_contacts = 0;

          for (size_t i = item_start; i < item_end; i++) {
            const auto &node = current_batch[eval_items[i].batch_idx];
            const auto &tpool = eval_items[i].pool;

            if (i == item_start || tpool->id != last_pool_id) {
              last_pool_id = tpool->id;
              cur_contact_offset = (int)all_contacts.size();
              cur_triple_offset = (int)all_triples.size();
              cur_num_contacts = (int)tpool->contacts.size();

              int n_trip = (int)tpool->gpu_triples.size();
              if (num_candidates > 0 && num_candidates < (size_t)n_trip) {
                n_trip = (int)num_candidates;
              }
              cur_num_triples = n_trip;

              all_contacts.insert(all_contacts.end(),
                                  tpool->contacts.begin(), tpool->contacts.end());
              all_triples.insert(all_triples.end(),
                                 tpool->gpu_triples.begin(),
                                 tpool->gpu_triples.begin() + n_trip);
            }

            GpuBox box;
            box.cx = node.box.center.x;
            box.cy = node.box.center.y;
            box.cz = node.box.center.z;
            box.rx = node.box.radii.x;
            box.ry = node.box.radii.y;
            box.rz = node.box.radii.z;
            for (int c = 0; c < 3; c++) {
              box.tri[c][0] = node.tri.corners[c].x;
              box.tri[c][1] = node.tri.corners[c].y;
              box.tri[c][2] = node.tri.corners[c].z;
            }
            box.chart = node.chart;
            box.triple_offset = cur_triple_offset;
            box.num_triples = cur_num_triples;
            box.contact_offset = cur_contact_offset;
            box.num_contacts = cur_num_contacts;
            box._pad = 0;

            active_gpu_boxes.push_back(box);
          }


          if (use_gpu && cl != nullptr && !active_gpu_boxes.empty() &&
              !all_triples.empty()) {
            MaybeMiniStatus("gpu");

            cl_int err = CL_SUCCESS;
            cl_mem b_boxes = clCreateBuffer(
                cl->context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
                sizeof(GpuBox) * active_gpu_boxes.size(), active_gpu_boxes.data(),
                &err);
            CHECK_EQ(err, CL_SUCCESS) << "clCreateBuffer b_boxes failed: " << err;
            cl_mem b_contacts = clCreateBuffer(
                cl->context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
                sizeof(GpuContact) * all_contacts.size(), all_contacts.data(),
                &err);
            CHECK_EQ(err, CL_SUCCESS)
                << "clCreateBuffer b_contacts failed: " << err;
            cl_mem b_triples = clCreateBuffer(
                cl->context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
                sizeof(GpuTriple) * all_triples.size(), all_triples.data(), &err);
            CHECK_EQ(err, CL_SUCCESS)
                << "clCreateBuffer b_triples failed ("
                << (sizeof(GpuTriple) * all_triples.size() / (1024 * 1024))
                << " MB): " << err;
            cl_mem b_results = clCreateBuffer(
                cl->context, CL_MEM_WRITE_ONLY,
                sizeof(GpuResult) * active_gpu_boxes.size(), nullptr, &err);
            CHECK_EQ(err, CL_SUCCESS)
                << "clCreateBuffer b_results failed: " << err;

            int num_boxes = active_gpu_boxes.size();
            err = clSetKernelArg(kernel, 0, sizeof(cl_mem), &b_boxes);
            CHECK_EQ(err, CL_SUCCESS);
            err = clSetKernelArg(kernel, 1, sizeof(cl_mem), &b_contacts);
            CHECK_EQ(err, CL_SUCCESS);
            err = clSetKernelArg(kernel, 2, sizeof(cl_mem), &b_triples);
            CHECK_EQ(err, CL_SUCCESS);
            err = clSetKernelArg(kernel, 3, sizeof(cl_mem), &b_results);
            CHECK_EQ(err, CL_SUCCESS);
            err = clSetKernelArg(kernel, 4, sizeof(int), &num_boxes);
            CHECK_EQ(err, CL_SUCCESS);

            size_t global_work_size = ((num_boxes + 63) / 64) * 64;
            size_t local_work_size = 64;
            err = clEnqueueNDRangeKernel(cl->queue, kernel, 1, nullptr,
                                         &global_work_size, &local_work_size, 0,
                                         nullptr, nullptr);
            CHECK_EQ(err, CL_SUCCESS) << "clEnqueueNDRangeKernel failed: " << err;
            err = clEnqueueReadBuffer(cl->queue, b_results, CL_TRUE, 0,
                                      sizeof(GpuResult) * num_boxes,
                                      chunk_results.data(), 0, nullptr, nullptr);
            CHECK_EQ(err, CL_SUCCESS) << "clEnqueueReadBuffer failed: " << err;

            clReleaseMemObject(b_boxes);
            clReleaseMemObject(b_contacts);
            clReleaseMemObject(b_triples);
            clReleaseMemObject(b_results);

          } else {
            // Multi-threaded CPU fallback
            MaybeMiniStatus("cpu");
            ParallelComp(active_gpu_boxes.size(), [&](int64_t a) {
              chunk_results[a] = EvaluateBoxCPU(active_gpu_boxes[a],
                                                 all_contacts, all_triples,
                                                 &status);
            }, num_threads);
          }

          for (size_t i = 0; i < chunk_size; i++) {
            results[eval_items[item_start + i].batch_idx] = chunk_results[i];
          }

          item_start = item_end;
        }

        MaybeMiniStatus("subdiv");
        for (int idx : eval_indices) {
          evaluated_count++;
          const auto &node = current_batch[idx];
          max_view_depth_reached = std::max<int>(max_view_depth_reached, (int)node.view_depth);
          auto res = results[idx];

          bool near_depth_out = (node.depth >= max_depth - 2);
          bool deep_box_with_narrow_view =
              (node.box_depth >= max_box_depth && node.view_depth >= 20);
          bool at_limit = (node.depth >= max_depth ||
                           (node.box_depth >= max_box_depth &&
                            node.view_depth >= max_view_depth));

          bool should_escalate = at_limit ||
                                 (lp_escalate_depth > 0 && node.depth >= lp_escalate_depth) ||
                                 (lp_escalate_box_depth > 0 && node.box_depth >= lp_escalate_box_depth) ||
                                 near_depth_out || deep_box_with_narrow_view;

          if (!res.certified && should_escalate) {
            // Safety-net escalation with EvaluateBoxCPULP before declaring difficult / shelving:
            std::vector<int> cs_list = {EffectiveConeSamples(node)};
            if (cs_list[0] != 14 && (at_limit || node.depth >= deep_escalate_depth)) {
              cs_list.push_back(14);
            }
            if (at_limit && cs_list.back() != 16) {
              cs_list.push_back(16);
            }

            for (int cs : cs_list) {
              MaybeMiniStatus("cpu_lp");
              auto esc_pool = GetTrianglePool(node.tri, cs);
              GpuBox gb;
              gb.cx = node.box.center.x;
              gb.cy = node.box.center.y;
              gb.cz = node.box.center.z;
              gb.rx = node.box.radii.x;
              gb.ry = node.box.radii.y;
              gb.rz = node.box.radii.z;
              for (int c = 0; c < 3; c++) {
                gb.tri[c][0] = node.tri.corners[c].x;
                gb.tri[c][1] = node.tri.corners[c].y;
                gb.tri[c][2] = node.tri.corners[c].z;
              }
              gb.chart = node.chart;
              gb.triple_offset = 0;
              gb.num_triples = esc_pool->gpu_triples.size();
              gb.contact_offset = 0;
              gb.num_contacts = (int)esc_pool->contacts.size();
              gb._pad = 0;
              GpuResult esc_res =
                EvaluateBoxCPULP(gb, esc_pool->contacts, esc_pool->gpu_triples,
                                 /*use_optimal_translation=*/true, &status);
              if (esc_res.certified) {
                ctr_esc_certified++;
                res = esc_res;
                break;
              }
            }
          }

          if (res.certified) {
            RecordCertification(node);
            // TODO: Probably should include cone_samples here so that it's easier to interpret the triangle indices.
            OutputRow(
                std::format("CE {} {} {} {} {:.17g} {} {} {}\n",
                            node.id, node.parent_id, node.depth,
                            res.winning_triple, res.margin,
                            res.inner[0], res.inner[1], res.inner[2]));
            if (prioritize_related && !active_priority.empty()) {
              for (auto it = active_priority.begin(); it != active_priority.end(); ) {
                if (it->chart == node.chart && node.box.Contains(it->w) &&
                    node.tri.ContainsRay(it->view)) {
                  if (!it->label.empty()) {
                    status.Print(AGREEN("✔") " "
                                 "{} excluded at depth {} (margin = {:.17g})!\n",
                                 it->label, node.depth, res.margin);
                    status.Print("  Node {}: box_depth={}, view_depth={}, box.c=({:.10g}, {:.10g}, {:.10g}), r=({:.10g}, {:.10g}, {:.10g})\n"
                                 "  tri=[({:.10g}, {:.10g}, {:.10g}), ({:.10g}, {:.10g}, {:.10g}), ({:.10g}, {:.10g}, {:.10g})]\n"
                                 "  winning_triple={}, inner=[{}, {}, {}]\n",
                                 node.id, node.box_depth, node.view_depth,
                                 node.box.center.x, node.box.center.y, node.box.center.z,
                                 node.box.radii.x, node.box.radii.y, node.box.radii.z,
                                 node.tri.corners[0].x, node.tri.corners[0].y, node.tri.corners[0].z,
                                 node.tri.corners[1].x, node.tri.corners[1].y, node.tri.corners[1].z,
                                 node.tri.corners[2].x, node.tri.corners[2].y, node.tri.corners[2].z,
                                 res.winning_triple, res.inner[0], res.inner[1], res.inner[2]);
                  } else {
                    status.Print(AGREEN("✔") " "
                                 "Related sol #{} excluded at "
                                 "depth {} (margin = {:.17g})!\n",
                                 it->solution_id, node.depth, res.margin);
                  }
                  it = active_priority.erase(it);
                } else {
                  ++it;
                }
              }
            }

          } else {
            if (node.depth >= max_depth ||
                (node.box_depth >= max_box_depth &&
                 node.view_depth >= max_view_depth)) {
              if (auto witness = CheckSolutionWitness(node)) {
                status.Print(
                    "\n"
                    "==============================================\n"
                    ARED("*** SOLVED: RUPERT PASSAGE CONFIRMED! ***") "\n"
                    "==============================================\n"
                    "Clearance: {:.17g}\n"
                    "Outer Frame:\n{}\n"
                    "Inner Frame:\n{}\n"
                    "Aborting proof search.\n",
                    witness->clearance,
                    SolutionDB::FrameString(witness->outer_frame),
                    SolutionDB::FrameString(witness->inner_frame));
                SolutionDB db;
                db.AddSolution("nopert_229", witness->outer_frame,
                               witness->inner_frame,
                               SolutionDB::METHOD_TILT_GRAD, 0, 0.9998,
                               witness->clearance);
                status.Print(
                    "Saved confirmed solution to " AGREEN("ruperts.sqlite")
                    ".\n");
                exit(0);
              }

              difficult_count++;
              if (difficult_callback) {
                difficult_callback(node, res.margin);
              }
              if (difficult_file) {
                Print(difficult_file,
                      "{} {} {} {} {} {} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} "
                      "{:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g}\n",
                      node.id, node.parent_id,
                      (int)node.depth, (int)node.box_depth, (int)node.view_depth, (int)node.chart,
                      node.box.center.x, node.box.center.y, node.box.center.z,
                      node.box.radii.x, node.box.radii.y, node.box.radii.z,
                      node.tri.corners[0].x, node.tri.corners[0].y, node.tri.corners[0].z,
                      node.tri.corners[1].x, node.tri.corners[1].y, node.tri.corners[1].z,
                      node.tri.corners[2].x, node.tri.corners[2].y, node.tri.corners[2].z,
                      res.margin);
                std::fflush(difficult_file);
              }
              OutputRow(std::format("DF {} {} {} {:.17g}\n",
                                    node.id, node.parent_id, node.depth, res.margin));

              if (verbose_status) {
                depth_out_per.RunIf([&]{
                  status.Print(
                      ARED("Shelved difficult cell #{} ")
                      "(depth={}, box_depth={}, view_depth={}, "
                      "radii=({:.6g}, {:.6g}, {:.6g})) "
                      "at box ({:.6g}, {:.6g}, {:.6g}) "
                      "(margin: {:.6g}, total difficult: {})\n",
                      node.id, node.depth, node.box_depth, node.view_depth,
                      node.box.radii.x, node.box.radii.y, node.box.radii.z,
                      node.box.center.x, node.box.center.y, node.box.center.z,
                      res.margin, FormatNum(difficult_count.Read()));
                });
              }
              continue;
            }

            if (node.depth >= suspicious_depth) {
              suspicious_per.RunIf([&]{
                vec3 vc = node.tri.Centroid();
                status.Print(
                    AYELLOW("[{}] Hard point at suspicious depth (depth={}, box_depth={}, view_depth={}):\n")
                    "  w = ({:.17g}, {:.17g}, {:.17g})\n"
                    "  view = ({:.17g}, {:.17g}, {:.17g})\n"
                    "  radii = ({:.10g}, {:.10g}, {:.10g})\n",
                    ANSI::Time(timer.Seconds()),
                    node.depth, node.box_depth, node.view_depth,
                    node.box.center.x, node.box.center.y, node.box.center.z,
                    vc.x, vc.y, vc.z,
                    node.box.radii.x, node.box.radii.y, node.box.radii.z);
              });
            }

            int widest = node.box.WidestAxis();
            // Balanced subdivision: refine box first down to 1/512, then balance
            // using angular equipartition with a strict 2:1 rate-limiting constraint
            // (at least 2 box splits between view splits) to converge to equiangular
            // without exploding unique view triangles.
            bool split_box;
            if (node.box.radii[widest] > 1.0 / 512.0) {
              // Spatial partitioning phase: refine Cayley box down to 1/512
              // early so coarse volume pruning can reject large regions rapidly.
              split_box = (node.box_depth < max_box_depth);
            } else {
              double rot_diam = 2.0 * node.box.radii[widest];
              double view_diam = node.tri.AngularDiameter();
              split_box = ShouldSplitBox(
                  node.box_depth, max_box_depth,
                  node.view_depth, max_view_depth,
                  /*box_span=*/0.0, /*view_penalty=*/0.0,
                  rot_diam, view_diam,
                  split_kappa, pre_vsplits, root_view_depth,
                  node.box_splits_since_view);
            }

            if (split_box) {
              auto [b0, b1] = node.box.Split(widest);

              SearchNode child0 = node;
              child0.id = next_node_id++;
              child0.parent_id = node.id;
              child0.depth = node.depth + 1;
              child0.box_depth = node.box_depth + 1;
              child0.box_splits_since_view = node.box_splits_since_view + 1;
              child0.box = b0;

              SearchNode child1 = node;
              child1.id = next_node_id++;
              child1.parent_id = node.id;
              child1.depth = node.depth + 1;
              child1.box_depth = node.box_depth + 1;
              child1.box_splits_since_view = node.box_splits_since_view + 1;
              child1.box = b1;

              split_count++;
              OutputRow(std::format("SP {} {} {} {} {}\n",
                                    node.id, node.parent_id, node.depth,
                                    child0.id, child1.id));

              if (ContainsUncertifiedPriority(child0)) {
                stack.push_back(child1);
                stack.push_back(child0);
              } else if (ContainsUncertifiedPriority(child1)) {
                stack.push_back(child0);
                stack.push_back(child1);
              } else {
                stack.push_back(child1);
                stack.push_back(child0);
              }
            } else {
              split_count++;
              max_view_depth_reached = std::max<int>(max_view_depth_reached, (int)node.view_depth + 1);
              auto sub_tris = node.tri.Subdivide();
              int priority_idx = -1;
              for (int t = 0; t < 4; t++) {
                SearchNode child = node;
                child.tri = sub_tris[t];
                if (ContainsUncertifiedPriority(child)) {
                  priority_idx = t;
                  break;
                }
              }

              int64_t child_ids[4] = {-1, -1, -1, -1};
              for (int t = sub_tris.size() - 1; t >= 0; t--) {
                if (t == priority_idx) continue;
                SearchNode child = node;
                child.id = next_node_id++;
                child.parent_id = node.id;
                child.depth = node.depth + 1;
                child.view_depth = node.view_depth + 1;
                child.box_splits_since_view = 0;
                child.tri = sub_tris[t];
                child_ids[t] = child.id;
                stack.push_back(child);
              }
              if (priority_idx >= 0) {
                SearchNode child = node;
                child.id = next_node_id++;
                child.parent_id = node.id;
                child.depth = node.depth + 1;
                child.view_depth = node.view_depth + 1;
                child.box_splits_since_view = 0;
                child.tri = sub_tris[priority_idx];
                child_ids[priority_idx] = child.id;
                stack.push_back(child);
              }

              OutputRow(std::format("SV {} {} {} {} {} {} {}\n",
                                    node.id, node.parent_id, node.depth,
                                    child_ids[0], child_ids[1], child_ids[2],
                                    child_ids[3]));
            }
          }
        }
      }

      if (verbose_status && progress_per.ShouldRun()) {
        double elapsed = timer.Seconds();
        double rate = evaluated_count.Read() / std::max(1e-6, elapsed);
        double completed_frac = CompletedFraction();

        std::string pool_str;
        if (!status_detail.empty()) {
          pool_str = status_detail;
        } else if (prioritize_related) {
          pool_str = std::format("{}/{} priority left",
                                 active_priority.size(),
                                 num_priority_points);
        } else {
          pool_str = AGREY("Related solution pool: inactive");
        }

        std::string row0 = StatusCounters();

        std::string depth_hist_str = FormatDepthHistogram();
        status.Status(
            "{}\n"
            "Stack: {} " AGREY("|")
            " Done: " AFGCOLOR(161, 240, 188, "{:.4f}%") " " AGREY("|")
            " Depth: {} " AGREY("|")
            " {} boxes/s " AGREY("|")
            " {}\n"
            "{}\n"
            "{}",
            row0,
            FormatNum(stack.size()),
            completed_frac * 100.0,
            current_batch.empty() ? 0 : current_batch[0].depth,
            FormatNum((int64_t)rate), ANSI::Time(elapsed),
            depth_hist_str,
            pool_str);
        // Only output incremental status updates if the major status output
        // hasn't run recently.
        mini_status_per.Reset();
        last_op.clear();
      }

      if (max_seconds > 0.0 && timer.Seconds() >= max_seconds) {
        timed_out = true;
        break;
      }

      bool interrupted = sigint_received.load() || (stop_requested && stop_requested->load());
      if ((enable_checkpoint && checkpoint_per.ShouldRun()) || interrupted) {
        if (enable_checkpoint) {
          SaveCheckpoint(ckpt_path);
        }
        FlushRows();
        if (difficult_file) std::fflush(difficult_file);
        if (interrupted) {
          if (show_banner) {
            PrintDepthDistribution();
            status.Print("\n"
                         AYELLOW("Interrupted") ".\n");
            if (enable_checkpoint) {
              status.Print("Saved checkpoint with {} nodes to {}.\n",
                           FormatNum(stack.size()), ckpt_path);
            }
            status.Print("Exiting...\n");
            std::fflush(stdout);
            std::fflush(stderr);
          }
          break;
        }
      }
    }


    bool interrupted = sigint_received.load() || (stop_requested && stop_requested->load()) || timed_out;
    if (!interrupted && stack.empty()) {
      // Completed full tree!
      if (enable_checkpoint) {
        std::error_code ec;
        std::filesystem::remove(ckpt_path, ec);
      }
      if (show_banner) {
        status.Print(AGREEN("\n=== ☻ Search Completed ☻ ===\n")
                     "Took {}s.",
                     ANSI::Time(timer.Seconds()));
        PrintDepthDistribution();
      }
    }

    FlushRows();
    if (row_file) {
      fclose(row_file);
      row_file = nullptr;
    }
    if (difficult_file) {
      std::fflush(difficult_file);
      fclose(difficult_file);
      difficult_file = nullptr;
    }
    if (show_banner) {
      status.Print("Total evaluated: {}\n"
                   "Total certified: {}\n"
                   "Total difficult (shelved): {}\n"
                   "Total pruned: {}\n"
                   "Total splits: {}\n",
                    evaluated_count.Read(),
                    certified_count.Read(),
                    difficult_count.Read(),
                    pruned_count.Read(),
                    split_count.Read());
    }
  }


std::string SearchManager::StatusCounters() {
    #define BAR " " ANSI_GREY "|" ANSI_DARK_WHITE " "
    return std::format(
        ANSI_BG(0, 0, 80)
        "{}" AWHITE("×") BAR
        "{}" AYELLOW("⊞") BAR
        "{}" AFGCOLOR(128, 190, 128, "✔") BAR
        "{}" ARED("☠") BAR
        "{}≷" BAR
        "{}⊿" BAR
        "{}/{}⚡ "
        ANSI_RESET,
        FormatNum(ctr_loops.Read()),
        FormatNum(evaluated_count.Read()),
        FormatNum(certified_count.Read()),
        FormatNum(difficult_count.Read()),
        FormatNum(pruned_count.Read()),
        FormatNum(ctr_built_triangles.Read()),
        FormatNum(ctr_esc_certified.Read()),
        FormatNum(ctr_cpu.Read()));
  }


void SearchManager::MaybeMiniStatus(std::string_view op) {
  if (!verbose_status) return;
  bool op_changed = (op != last_op);
  if (op_changed || mini_status_per.ShouldRun()) {
    if (op_changed) {
      mini_status_per.Reset();
      last_op = op;
    }
    status.LineStatus(0, "{} " ABLUE("{}"), StatusCounters(), op);
  }
}
