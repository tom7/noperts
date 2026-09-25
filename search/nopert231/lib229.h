#ifndef _RUPERTS_LIB229_H
#define _RUPERTS_LIB229_H

#include <CL/cl.h>
#include <CL/cl_platform.h>
#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <functional>
#include <memory>
#include <mutex>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <unordered_map>
#include <vector>

#include "base/logging.h"
#include "geom/polyhedra.h"
#include "periodically.h"
#include "status-bar.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

namespace tubetree229 {
class TubeAtlas;
}

// Lean 4 displacement error parameters:
// In AtlasProjectiveGlobalCertificate.lean:
//   Box.displacementError = 300 * box.dBound * tightVertexErrorQ
inline constexpr double TIGHT_VERTEX_ERROR = 6e-16;

// Binary formats matching OpenCL kernel layouts
struct GpuBox {
  double cx, cy, cz;
  double rx, ry, rz;
  double tri[3][3];
  int chart;
  int num_triples;
  int triple_offset;
  int contact_offset;
  int num_contacts;
  int _pad;
};
static_assert(sizeof(GpuBox) == 144, "GpuBox struct size mismatch");

struct GpuContact {
  int vertex;
  double edge[3];
  double defect;
};

struct GpuTriple {
  // Local contact indices in this pool (0 to num_contacts - 1)
  uint8_t c0, c1, c2;
  uint8_t _pad[5];
  double weighted_defect_upper;
};
static_assert(sizeof(GpuTriple) == 16, "GpuTriple struct size mismatch");

struct GpuResult {
  int certified;
  int winning_triple;
  int inner[3];
  double margin;
};
static_assert(sizeof(GpuResult) == 32, "GpuResult struct size mismatch");

inline constexpr int MAX_GPU_CONTACTS = 256;

// Projective view triangle
struct ProjectiveTriangle {
  std::array<vec3, 3> corners;

  vec3 Centroid() const {
    return (corners[0] + corners[1] + corners[2]) / 3.0;
  }

  double AngularDiameter() const {
    vec3 u0 = yocto::normalize(corners[0]);
    vec3 u1 = yocto::normalize(corners[1]);
    vec3 u2 = yocto::normalize(corners[2]);
    double d01 = yocto::length(u0 - u1);
    double d12 = yocto::length(u1 - u2);
    double d20 = yocto::length(u2 - u0);
    return std::max({d01, d12, d20});
  }

  std::array<ProjectiveTriangle, 4> Subdivide() const {
    vec3 m01 = (corners[0] + corners[1]) * 0.5;
    vec3 m12 = (corners[1] + corners[2]) * 0.5;
    vec3 m20 = (corners[2] + corners[0]) * 0.5;
    return {{
      {corners[0], m01, m20},
      {m01, corners[1], m12},
      {m20, m12, corners[2]},
      {m01, m12, m20}
    }};
  }

  bool ContainsRay(const vec3 &v) const {
    double det = yocto::dot(corners[0], yocto::cross(corners[1], corners[2]));
    if (std::abs(det) < 1e-15) return false;
    double s = (det > 0.0) ? 1.0 : -1.0;
    double d0 = s * yocto::dot(v, yocto::cross(corners[1], corners[2]));
    double d1 = s * yocto::dot(v, yocto::cross(corners[2], corners[0]));
    double d2 = s * yocto::dot(v, yocto::cross(corners[0], corners[1]));
    return d0 >= -1e-12 && d1 >= -1e-12 && d2 >= -1e-12;
  }
};

// 3D Cayley box
struct CayleyBox {
  vec3 center;
  vec3 radii;

  bool Contains(const vec3 &w) const {
    return std::abs(w.x - center.x) <= radii.x + 1e-12 &&
           std::abs(w.y - center.y) <= radii.y + 1e-12 &&
           std::abs(w.z - center.z) <= radii.z + 1e-12;
  }

  int WidestAxis() const {
    int axis = 0;
    if (radii.y > radii[axis]) axis = 1;
    if (radii.z > radii[axis]) axis = 2;
    return axis;
  }

  std::pair<CayleyBox, CayleyBox> Split(int axis) const {
    CayleyBox left = *this;
    CayleyBox right = *this;
    left.radii[axis] *= 0.5;
    right.radii[axis] *= 0.5;
    left.center[axis] -= left.radii[axis];
    right.center[axis] += right.radii[axis];
    return {left, right};
  }

  bool ContainsOrigin() const {
    return std::abs(center.x) <= radii.x &&
           std::abs(center.y) <= radii.y &&
           std::abs(center.z) <= radii.z;
  }
};

inline bool OutsideBall(const CayleyBox &b) {
  double d2 = 0.0;
  for (int c = 0; c < 3; c++) {
    double v = std::abs(b.center[c]) - b.radii[c];
    if (v > 0.0) d2 += v * v;
  }
  return d2 > 1.0;
}

struct FundamentalPruneResult {
  bool prune = false;
  int direction = 0; // -1 or 1
};

inline FundamentalPruneResult CheckFundamentalPrune(
    int chart, const CayleyBox &b) {
  if (chart == 0) {
    if (b.center.z - b.radii.z > 1.0 / 3.0) return {true, -1};
    if (b.center.z + b.radii.z < -1.0 / 3.0) return {true, 1};
  } else if (chart == 1) {
    if (b.center.y - b.radii.y > 1.0 / 3.0) return {true, 1};
    if (b.center.y + b.radii.y < -1.0 / 3.0) return {true, -1};
  } else if (chart == 2) {
    if (b.center.x - b.radii.x > 1.0 / 3.0) return {true, 1};
    if (b.center.x + b.radii.x < -1.0 / 3.0) return {true, -1};
  }

  static constexpr const double K_a = -690983.0 / 1000000.0;
  static constexpr const double K_b_base = 951057.0 / 1000000.0;
  static constexpr const double approx_error = 2.0 / 125000.0; // 1.6e-5

  for (int dir : {-1, 1}) {
    double K_b = dir * K_b_base;
    double c0 = 0.0, cx = 0.0, cy = 0.0, cz = 0.0;
    double cxx = 0.0, cyy = 0.0, czz = 0.0, cxy = 0.0;

    if (chart == 0) {
      c0 = 2.0 * K_a;
      cz = -4.0 * K_b;
      czz = -2.0 * K_a;
    } else if (chart == 1) {
      cxx = 2.0 * K_a;
      cyy = -2.0 * K_a;
      cxy = 4.0 * K_b;
    } else if (chart == 2) {
      cxx = -2.0 * K_a;
      cyy = 2.0 * K_a;
      cxy = -4.0 * K_b;
    }

    double x = b.center.x, y = b.center.y, z = b.center.z;
    double rx = b.radii.x, ry = b.radii.y, rz = b.radii.z;

    double val0 = c0 + cx*x + cy*y + cz*z +
                  cxx*x*x + cyy*y*y + czz*z*z + cxy*x*y;

    double gx = cx + 2.0*cxx*x + cxy*y;
    double gy = cy + cxy*x + 2.0*cyy*y;
    double gz = cz + 2.0*czz*z;

    double center =
        val0 + 0.5 * (cxx * rx * rx + cyy * ry * ry + czz * rz * rz);
    double radius =
        (std::abs(gx) * rx + std::abs(gy) * ry + std::abs(gz) * rz) +
        std::abs(cxy) * rx * ry +
        0.5 * (std::abs(cxx) * rx * rx + std::abs(cyy) * ry * ry +
               std::abs(czz) * rz * rz);

    double lower = center - radius;
    if (lower > approx_error) {
      return {true, dir};
    }
  }

  return {false, 0};
}

inline bool InsideIdentityTube(int chart, const CayleyBox &b,
                               double tube_r = 1e-4) {
  if (chart != 0) return false;
  double mx = std::abs(b.center.x) + b.radii.x;
  double my = std::abs(b.center.y) + b.radii.y;
  double mz = std::abs(b.center.z) + b.radii.z;
  static constexpr double IDENTITY_FACTOR = 2.0;
  return IDENTITY_FACTOR * std::sqrt(mx*mx + my*my + mz*mz) <= tube_r;
}

// Search node in the branch-and-bound tree
struct SearchNode {
  int64_t id = 0;
  int64_t parent_id = -1;
  CayleyBox box;
  ProjectiveTriangle tri;
  uint8_t depth = 0;
  uint8_t view_depth = 0;
  uint8_t box_depth = 0;
  uint8_t chart = 0;
  uint8_t box_splits_since_view = 0;
};
static_assert(sizeof(SearchNode) == 144, "SearchNode struct size mismatch");

// A difficult/shelved node recorded in chart0.difficult format
struct DifficultCell {
  int64_t id = 0;
  int64_t parent_id = 0;
  int depth = 0;
  int box_depth = 0;
  int view_depth = 0;
  int chart = 0;
  vec3 c{0, 0, 0};
  vec3 r{0, 0, 0};
  vec3 v[3];
  double best_margin = 0.0;

  vec3 ViewCentroid() const {
    return yocto::normalize(v[0] + v[1] + v[2]);
  }

  SearchNode ToSearchNode() const {
    SearchNode node;
    node.id = id;
    node.parent_id = parent_id;
    node.depth = (uint8_t)std::min(255, depth);
    node.box_depth = (uint8_t)std::min(255, box_depth);
    node.view_depth = (uint8_t)std::min(255, view_depth);
    node.chart = (uint8_t)std::min(255, chart);
    node.box.center = c;
    node.box.radii = r;
    node.tri.corners[0] = v[0];
    node.tri.corners[1] = v[1];
    node.tri.corners[2] = v[2];
    return node;
  }

  std::string ToString() const {
    return std::format(
        "{} {} {} {} {} {} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} "
        "{:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g} {:.17g}\n",
        id, parent_id, depth, box_depth, view_depth, chart,
        c.x, c.y, c.z, r.x, r.y, r.z,
        v[0].x, v[0].y, v[0].z,
        v[1].x, v[1].y, v[1].z,
        v[2].x, v[2].y, v[2].z,
        best_margin);
  }
};

std::vector<DifficultCell> ReadDifficultFile(const std::string &path);
bool WriteDifficultFile(const std::string &path, const std::vector<DifficultCell> &cells);

struct TrianglePool {
  uint64_t id = 0;
  std::vector<GpuContact> contacts;
  std::vector<GpuTriple> gpu_triples;
};

inline uint64_t HashTriangle(const ProjectiveTriangle &tri) {
  uint64_t h = 0xcbf29ce484222325ULL;
  for (int c = 0; c < 3; c++) {
    uint64_t ux, uy, uz;
    std::memcpy(&ux, &tri.corners[c].x, 8);
    std::memcpy(&uy, &tri.corners[c].y, 8);
    std::memcpy(&uz, &tri.corners[c].z, 8);
    h ^= ux; h *= 0x100000001b3ULL;
    h ^= uy; h *= 0x100000001b3ULL;
    h ^= uz; h *= 0x100000001b3ULL;
  }
  return h;
}

double ComputeWeightedDefectUpper(const ProjectiveTriangle &tri,
                                 const std::vector<GpuContact> &contacts,
                                 int c0, int c1, int c2,
                                 const vec3 w_coeff[3]);

std::shared_ptr<const TrianglePool> BuildTrianglePool(
    const ProjectiveTriangle &tri, int cone_samples = 6, uint64_t id = 0);

std::shared_ptr<const TrianglePool> GetTrianglePool(
    const ProjectiveTriangle &tri, int cone_samples = 6);

extern size_t g_max_triangle_cache_size;

GpuResult EvaluateBoxCPU(
    const GpuBox &box,
    const std::vector<GpuContact> &contacts,
    const std::vector<GpuTriple> &triples,
    StatusBar *status = nullptr);

GpuResult EvaluateBoxCPULP(
    const GpuBox &box,
    const std::vector<GpuContact> &contacts,
    const std::vector<GpuTriple> &triples,
    bool use_optimal_translation = true,
    StatusBar *status = nullptr);

// Result of certifying a node via a convex mixture of triples (N <= 4)
// mathematically matching Lean 4's AtlasProjectiveMixedGlobalCertificate.
struct FarkasCageHint {
  uint64_t pool_id = 0;
  int num_components = 0;
  int triples[4] = {-1, -1, -1, -1};
  int inners[4][3] = {{-1, -1, -1}, {-1, -1, -1}, {-1, -1, -1}, {-1, -1, -1}};
};

struct FarkasCageCache {
  static constexpr int CAPACITY = 8;
  FarkasCageHint entries[CAPACITY];
  int count = 0;
  int next_idx = 0;

  void Insert(const FarkasCageHint &h) {
    if (h.num_components < 1) return;
    for (int i = 0; i < count; i++) {
      if (entries[i].pool_id == h.pool_id && entries[i].num_components == h.num_components) {
        bool match = true;
        for (int k = 0; k < h.num_components; k++) {
          if (entries[i].triples[k] != h.triples[k]) { match = false; break; }
        }
        if (match) return;
      }
    }
    entries[next_idx] = h;
    next_idx = (next_idx + 1) % CAPACITY;
    if (count < CAPACITY) count++;
  }
};

// Result of certifying a node via a convex mixture of triples (N <= 4)
// mathematically matching Lean 4's AtlasProjectiveMixedGlobalCertificate.
struct MixtureResult {
  bool certified = false;
  int num_components = 0;
  int triples[4] = {-1, -1, -1, -1};
  int inners[4][3] = {{-1, -1, -1}, {-1, -1, -1}, {-1, -1, -1}, {-1, -1, -1}};
  double weights[4] = {0.0, 0.0, 0.0, 0.0};
  double margin = -1e30;
  double view_penalty = 0.0;
  double box_span = 0.0;
  int num_candidates = 0;
  int strategy_used = 0; // 0=single triple, 1=corner+center, 2=greedy column gen, 3=warm-start Farkas cage
  int chosen_ranks[4] = {-1, -1, -1, -1}; // 0-indexed rank in sorted evaluated[] list
  int max_rank_looked = 0; // deepest rank in evaluated[] examined
  int pool_tested = 0; // candidates in cand_pool tested
  uint64_t pool_id = 0;
};

// Evaluates a box and projective triangle view using a convex mixture
// of up to max_components (default 4) triples.
// Prioritizes mathematical power over speed for difficult cells.
MixtureResult EvaluateBoxCPUMixture(
    int chart, const CayleyBox &box, const ProjectiveTriangle &tri,
    int cone_samples = 8, int max_components = 4,
    const FarkasCageCache *cache = nullptr);

// ============================================================================
// Numerical Mixture Weight Solvers
// ============================================================================

// Evaluates the worst-case margin across 162 Bernstein control points given
// mixture weights alpha on the probability simplex Delta_{K-1}:
//   f(alpha) = min_{j=0..161} sum_{k=0}^{K-1} alpha_k * margins[k][j]
// Optionally returns the index of the worst-performing control point.
double EvalMixtureMargin(int K, const double *const margins[],
                         const double alpha[],
                         int *out_worst_idx = nullptr);

// Euclidean projection of a vector x in R^K onto the probability simplex
// Delta_{K-1} = {alpha in R^K : alpha_k >= 0, sum_k alpha_k = 1}.
void ProjectToSimplex(int K, const double x[], double out[]);

// Solves for optimal mixture weights alpha in Delta_{K-1} maximizing the
// worst-case margin over 162 Bernstein control points:
//   max_{alpha in Delta_{K-1}} min_{j=0..161} sum_{k=0}^{K-1} alpha_k * margins[k][j]
//
// Parameters:
//   K: Number of components, in {1, 2, 3, 4}.
//   margins: Array of K pointers, each pointing to 162 control point margins.
//   out_alpha: Output buffer of size 4 receiving the optimal weights.
//   polish: If true, runs higher-iteration search or Nelder-Mead polish.
//   warm_alpha: Optional prior weights for warm-starting.
//   target_margin: Target margin threshold for Chebyshev centering or termination.
// Returns the achieved worst-case margin.
double SolveOptimalWeights(int K, const double *const margins[],
                           double out_alpha[4], bool polish = true,
                           const double *warm_alpha = nullptr,
                           double target_margin = 0.0);

// Evaluates the 162 Bernstein control values minus defect penalty and displacement error
// for a single candidate triple across the 6 projective triangle sample points and 27 Bernstein
// control points of the box.
void ComputeTripleMargins(
    int chart,
    const vec3 p[6],
    double lx, double ly, double lz,
    double wx_len, double wy_len, double wz_len,
    double d_bound,
    int triple_idx,
    const int inners[3],
    std::shared_ptr<const TrianglePool> pool,
    double out_margins[162]);

// ============================================================================
// Hierarchical View Quadtree
// ============================================================================
//
// Represents a 4-ary subdivision tree of a projective view triangle.
// Serializes to / parses from a pre-order string ('S' = split, '.' = leaf):
//   e.g. "S . . . ." (uniform depth 1: 4 leaves)
//   e.g. "S . . . S . . . ." (non-uniform: child 3 split into 4 sub-leaves, total 7 leaves)
// Also supports legacy single-integer depth notation: "3" -> uniform depth 3.
//
struct ViewQuadtree {
  bool is_split = false;
  std::array<std::unique_ptr<ViewQuadtree>, 4> children;

  ViewQuadtree();
  ~ViewQuadtree();
  ViewQuadtree(const ViewQuadtree &other);
  ViewQuadtree &operator=(const ViewQuadtree &other);
  ViewQuadtree(ViewQuadtree &&) noexcept;
  ViewQuadtree &operator=(ViewQuadtree &&) noexcept;

  // Make a uniform quadtree of depth N (N=0 is 1 leaf, N=1 is 4 leaves, etc.)
  static ViewQuadtree MakeUniform(int depth);

  // Serialize to compact pre-order string ("S . . . .")
  std::string ToString() const;

  // Parse from pre-order string or legacy integer
  static std::optional<ViewQuadtree> FromString(std::string_view s);

  // Split a leaf along a path of child indices (each in {0, 1, 2, 3})
  void SplitPath(std::span<const int> path);

  struct LeafNode {
    std::vector<int> path; // relative path from root
    int depth = 0;
    ProjectiveTriangle tri;
  };

  std::vector<LeafNode> GetLeaves(const ProjectiveTriangle &root_tri) const;

  int CountLeaves() const;
  int MaxDepth() const;
};

// Given a root projective triangle and a descendant sub-triangle,
// computes the sequence of child indices (0..3) from root to sub-triangle.
std::vector<int> FindTrianglePath(
    const ProjectiveTriangle &root_tri,
    const ProjectiveTriangle &sub_tri,
    int max_search_depth = 12);

// Sidecar helpers supporting both legacy integer and hierarchical quadtree format:
std::unordered_map<int64_t, ViewQuadtree> LoadQuadtreeSplitsFile(const std::string &path);
bool SaveQuadtreeSplitsFile(const std::string &path, const std::unordered_map<int64_t, ViewQuadtree> &splits);

struct MixtureProgress {
  double elapsed_seconds = 0.0;
  int64_t total_nodes = 0;
  int64_t certified_leaves = 0;
  int64_t k1_count = 0;
  int64_t mx_count = 0;
  int min_leaf_depth = 0;
  int max_leaf_depth = 0;
  int64_t queue_nodes = 0;
  double worst_margin = 1e30;
  double nodes_per_sec = 0.0;
};

using MixtureProgressCallback = std::function<void(const MixtureProgress &)>;

struct MixtureSolveStats {
  bool solved = false;
  int64_t total_nodes = 0;
  int64_t certified_leaves = 0;
  int64_t pruned_leaves = 0;
  int64_t ceiling_hits = 0;
  int64_t remaining_nodes = 0;
  int64_t rows_written = 0;
  int max_view_depth_reached = 0;
  double worst_margin = 1e30;
  double elapsed_seconds = 0.0;

  // Candidate depth and strategy instrumentation
  int64_t k1_count = 0;
  int64_t corner_count = 0;
  int64_t greedy_count = 0;
  int64_t warm_count = 0;
  int64_t max_candidate_rank = 0;
  int64_t rank_histogram[8] = {0}; // [0], [1-3], [4-7], [8-15], [16-31], [32-63], [64-127], [128+]
  double sum_candidate_pool_size = 0.0;
  int64_t count_evaluations = 0;

  // Certified leaves depth statistics & histogram (0..159)
  int min_leaf_depth = 999999;
  int max_leaf_depth = 0;
  int64_t leaf_depth_histogram[160] = {0};

  // Remaining open search frontier (unresolved branch nodes on stack/queue)
  int min_frontier_depth = 999999;
  int max_frontier_depth = 0;
  int min_frontier_box_depth = 999999;
  int max_frontier_box_depth = 0;
  int min_frontier_view_depth = 999999;
  int max_frontier_view_depth = 0;
  int64_t frontier_depth_histogram[160] = {0};
  int64_t frontier_box_depth_histogram[100] = {0};
  int64_t frontier_view_depth_histogram[30] = {0};

  // Learned hierarchical view quadtree (captures in-search view splits + timed-out leaves)
  ViewQuadtree learned_quadtree;

  // Formats human-readable depth histograms and search frontier diagnostics
  std::string FormatHistogramReport(int max_depth, int max_box_depth, int max_view_depth) const;
};

// Solves a single difficult cell using a branch-and-bound tree with
// EvaluateBoxCPUMixture, using the analytical splitting criterion.
// Outputs standard SP, SV, PR, TU, SO, CE, and MX rows via row_callback.
MixtureSolveStats SolveCellMixture(
    const DifficultCell &cell,
    int max_depth = 54,
    int max_box_depth = 42,
    int max_view_depth = 14,
    int max_nodes = 64,
    int max_split_delta = 4,
    int cone_samples = 8,
    int max_components = 4,
    double split_kappa = 0.5,
    double tube_radius = 1e-4,
    double time_limit_sec = 10.0,
    std::function<void(std::string_view)> row_callback = nullptr,
    std::atomic<bool> *interrupted = nullptr,
    int pre_vsplits = 0,
    const ViewQuadtree *initial_quadtree = nullptr,
    const tubetree229::TubeAtlas *tube_atlas = nullptr,
    MixtureProgressCallback progress_callback = nullptr);

// Solves a single difficult cell in parallel using num_threads worker threads.
// Employs a two-tier work-stealing architecture:
//   Tier 1: Workers partition independent leaf view cones (constant candidate pool,
//           >90% Farkas cage cache hits, pure binary box splits).
//   Tier 2: When active view cones < num_threads, idle workers steal coarse Cayley
//           boxes from busy workers, ensuring 100% machine saturation without stragglers.
MixtureSolveStats SolveCellMixtureParallel(
    const DifficultCell &cell,
    int num_threads = 16,
    int max_depth = 54,
    int max_box_depth = 42,
    int max_view_depth = 14,
    int max_nodes = 64,
    int max_split_delta = 4,
    int cone_samples = 8,
    int max_components = 4,
    double split_kappa = 0.5,
    double tube_radius = 1e-4,
    double time_limit_sec = 10.0,
    std::function<void(std::string_view)> row_callback = nullptr,
    std::atomic<bool> *interrupted = nullptr,
    const ViewQuadtree *initial_quadtree = nullptr,
    const tubetree229::TubeAtlas *tube_atlas = nullptr,
    MixtureProgressCallback progress_callback = nullptr);

// Returns true if the node should be bisected along its widest Cayley box axis (SP),
// or false if the projective view triangle should be subdivided into 4 sub-triangles (SV).
//
// Decision hierarchy:
// 1. Hard depth constraints:
//    - If box_depth >= max_box_depth, cannot split box -> return false (SV).
//    - If view_depth >= max_view_depth, cannot split view -> return true (SP).
// 2. Pre-split constraint:
//    - If pre_vsplits > 0 and view_depth >= root_view_depth + pre_vsplits,
//      the view cone is locked -> return true (SP).
// 3. Analytical Geometry-Specific Rule:
//    - If view_penalty > 0 and box_span > 0:
//      - If box_span >= view_penalty: box rotation error dominates -> return true (SP).
//      - If view_penalty > box_span: view defect dominates -> return false (SV).
// 4. Fallback Geometric Ratio:
//    - If rot_diam >= split_kappa * view_diam -> return true (SP).
//    - Else if box_splits_since_view >= 0 -> return (box_splits_since_view < 2).
//    - Else -> return false (SV).
bool ShouldSplitBox(
    int box_depth, int max_box_depth,
    int view_depth, int max_view_depth,
    double box_span, double view_penalty,
    double rot_diam, double view_diam,
    double split_kappa = 0.5,
    int pre_vsplits = 0,
    int root_view_depth = 0,
    int box_splits_since_view = -1);

// Sidecar view-split cache helpers (reads/writes <cell_id> <vsplits> format).
std::unordered_map<int64_t, int> LoadSplitsFile(const std::string &path);
bool SaveSplitsFile(const std::string &path, const std::unordered_map<int64_t, int> &splits);

// ============================================================================
// Bernstein Polynomial Transformation Functions
// ============================================================================
//
// These functions represent quadratic polynomials in 3 variables on a 3D box
// [lx, lx + wx] x [ly, ly + wy] x [lz, lz + wz] using the tensored degree-2
// Bernstein basis:
//
//   P(x, y, z) = C[0] + C[1]*x + C[2]*y + C[3]*z +
//                C[4]*x^2 + C[5]*x*y + C[6]*x*z +
//                C[7]*y^2 + C[8]*y*z + C[9]*z^2
//
// Local coordinates (u, v, w) in [0, 1]^3 map to (x, y, z) via:
//   x = lx + u * wx,  y = ly + v * wy,  z = lz + w * wz.
//
// The 1D degree-2 Bernstein basis polynomials on [0, 1] are:
//   B_{0,2}(t) = (1 - t)^2,  B_{1,2}(t) = 2*t*(1 - t),  B_{2,2}(t) = t^2.
//
// The 27 control points out_controls[idx] are indexed with
//   idx = 9 * bi + 3 * bj + bk  for bi, bj, bk in {0, 1, 2}.
//
// Fundamental Mathematical Invariants:
// 1. Convex Hull Property:
//      min_idx out_controls[idx] <= P(x, y, z) <= max_idx out_controls[idx]
//    for all points (x, y, z) in the box.
// 2. Corner Interpolation:
//    At the 8 vertices of the box, the corresponding corner control points
//    exactly interpolate P(x, y, z).
// 3. Partition of Unity:
//    sum_{bi, bj, bk} B_{bi,2}(u) * B_{bj,2}(v) * B_{bk,2}(w) = 1.
//
void ComputeBernstein27Controls(
    const double C[10],
    double lx, double ly, double lz,
    double wx, double wy, double wz,
    double out_controls[27]);

// Computes the minimum value among the 27 Bernstein control points of polynomial C
// over the box [lx, lx + wx] x [ly, ly + wy] x [lz, lz + wz].
// This provides a guaranteed lower bound on P(x, y, z) across the box.
double Bernstein27Min(
    const double C[10],
    double lx, double ly, double lz,
    double wx, double wy, double wz);

Polyhedron GetPolyhedron229();


struct SolutionWitness {
  frame3 outer_frame;
  frame3 inner_frame;
  double clearance = 0.0;
};

std::optional<SolutionWitness> CheckSolutionWitness(const SearchNode &node);

// Binary checkpoint format
struct CheckpointHeader {
  static constexpr uint64_t kMagic = 0x4e4f504552543232ULL; // "NOPERT22"
  static constexpr uint32_t kVersion = 2;
  uint64_t magic = kMagic;
  uint32_t version = kVersion;
  uint32_t chart = 0;
  int64_t next_node_id = 0;
  uint64_t evaluated_count = 0;
  uint64_t certified_count = 0;
  uint64_t pruned_count = 0;
  uint64_t split_count = 0;
  uint64_t difficult_count = 0;
  uint64_t stack_size = 0;
};

void InstallSignalHandlers();
bool SigIntReceived();
void SetSigInt();

struct SearchManager {
  int chart = 0;
  int batch_size = 32768;

  int max_depth = 40;
  int max_box_depth = 32;
  int max_view_depth = 10;
  int suspicious_depth = 36;
  size_t num_candidates = 0; // 0 = all
  int cone_samples = 8;
  int escalate_depth = 32;
  int escalate_cone_samples = 12;
  int deep_escalate_depth = 38;
  int deep_escalate_cone_samples = 14;
  int lp_escalate_depth = 0;
  int lp_escalate_box_depth = 0;
  int num_threads = 8;
  int64_t max_nodes = 0;

  int EffectiveConeSamples(const SearchNode &node) const {
    if (deep_escalate_depth > 0 && node.depth >= deep_escalate_depth) {
      return deep_escalate_cone_samples;
    }
    if (escalate_depth > 0 && node.depth >= escalate_depth) {
      return escalate_cone_samples;
    }
    return cone_samples;
  }

  bool use_gpu = true;
  bool resume = true;
  bool prioritize_related = true;
  double related_epsilon = 0.05;
  double tube_radius = 1e-4;
  const tubetree229::TubeAtlas *tube_atlas = nullptr;
  double split_kappa = 1.0;
  int pre_vsplits = 0;
  int root_view_depth = 0;
  int root_box_depth = 0;
  int max_view_depth_reached = 0;
  std::string output_dir = ".artifacts/nopert229";

  std::vector<SearchNode> stack; // DFS LIFO stack
  std::vector<SearchNode> current_batch; // Active batch nodes being evaluated
  int64_t next_node_id = 0;

  static constexpr int kMaxTrackDepth = 128;
  static constexpr int kMaxTrackK = 256;

  std::atomic<uint64_t> cert_by_depth[kMaxTrackDepth]{};
  std::atomic<uint64_t> cert_by_box_depth[kMaxTrackDepth]{};
  std::atomic<uint64_t> cert_by_view_depth[64]{};

  std::unique_ptr<std::atomic<uint64_t>[]> cert_k_by_depth;
  std::unique_ptr<std::atomic<uint64_t>[]> cert_k_by_box_depth;
  std::unique_ptr<std::atomic<uint64_t>[]> cert_k_by_view_depth;

  SearchManager();

  static double EvalKVolume(const std::atomic<uint64_t> *k_table, int row, int num_k = kMaxTrackK) {
    if (!k_table) return 0.0;
    double vol = 0.0;
    for (int k = num_k - 1; k > 0; k--) {
      uint64_t c = k_table[row * num_k + k].load(std::memory_order_relaxed);
      vol = (vol + c) * 0.5;
    }
    vol += k_table[row * num_k + 0].load(std::memory_order_relaxed);
    return vol;
  }

  StatusBar status{4};
  Periodically mini_status_per = Periodically(1.0);
  std::string last_op;
  std::string status_detail;

  cl_program program = nullptr;
  cl_kernel kernel = nullptr;

  struct PriorityPoint {
    vec3 view;
    vec3 w;
    int chart = 0;
    int solution_id = 0;
    std::string label;
  };
  std::vector<PriorityPoint> active_priority;
  int num_priority_points = 0;

  std::mutex row_mutex;
  std::string row_buffer;
  FILE *row_file = nullptr;
  FILE *difficult_file = nullptr;
  std::string difficult_path;

  // Output and lifecycle callbacks
  std::function<void(std::string_view)> row_callback = nullptr;
  std::function<void(const SearchNode &node, double margin)> difficult_callback = nullptr;
  bool auto_init_root = true;
  bool write_row_file = true;
  bool write_difficult_file = true;
  bool enable_checkpoint = true;
  bool show_banner = true;
  bool verbose_status = true;
  double max_seconds = 0.0;
  bool timed_out = false;
  std::atomic<bool> *stop_requested = nullptr;

  void ResetState();

  void RecordCertification(const SearchNode &node);
  std::string FormatDepthHistogram() const;
  void PrintDepthDistribution();
  void WriteDepthHistogramFile(const std::string &filename) const;
  static std::string CLPreamble();
  void InitOpenCL();
  bool SaveCheckpoint(const std::string &path);
  bool LoadCheckpoint(const std::string &path);
  bool ContainsUncertifiedPriority(const SearchNode &node) const;
  std::vector<PriorityPoint> GetPriorityPoints(double max_dist = 0.05);
  void FilterPriorityPointsToStack();
  double CompletedFraction() const;
  void InitRoot();
  void FlushRowsWithLock();
  void FlushRows();
  void OutputRow(std::string_view row);
  void Run();
  static std::string StatusCounters();
  void MaybeMiniStatus(std::string_view op);
};

#endif
