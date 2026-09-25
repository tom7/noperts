#ifndef RUPERTS_TUBETREE229_H_
#define RUPERTS_TUBETREE229_H_

#include <algorithm>
#include <array>
#include <cstdint>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "bignum/big.h"
#include "bignum/big-vec.h"
#include "yocto-math.h"

namespace tubetree229 {

using vec3 = yocto::vec<double, 3>;

// Exact projective spherical triangle with 3 rational vertices.
struct TriangleQ {
  BigVecQ3 corners[3];

  // Deterministic 4-way quaternary subdivision into children 0, 1, 2, 3:
  // Child 0: (corners[0], m01, m20)
  // Child 1: (corners[1], m12, m01)
  // Child 2: (corners[2], m20, m12)
  // Child 3: (m01, m12, m20)
  void Subdivide(TriangleQ children[4]) const;
};

// Returns the canonical root upper wedge triangle:
// Corners: (1, 0, 0), (10/41, 31/41, 0), (0, 0, 1).
TriangleQ GetRootWedge();

// Deterministically constructs the exact rational triangle corresponding to a
// canonical base-4 path string (e.g. "0", "01", "0321").
// An empty path "" represents the full root wedge.
TriangleQ TriangleFromPath(std::string_view path);

// Information identifying a contact point on the silhouette.
struct ContactInfo {
  int edge_start = 0;
  int edge_finish = 0;
  int edge_start2 = 0;
  int edge_finish2 = 0;
  int mix = 1000; // 0..1000 representing interpolation weight (mix / 1000)
  int vertex = 0; // support vertex index (0..19 for Nopert #229)
};

// A single axis certificate consisting of 3 contacts enclosing the axis in 2D.
struct AxisCertificate {
  ContactInfo contacts[3];
  int nonzero_witness[3] = {-1, -1, -1};
  BigRat B;
};

// A complete 4-axis identity tube certificate.
struct TubeCertificate {
  AxisCertificate axes[4];
  BigRat c;     // Certified net margin: FloorTo(cover_radius - delta)
  BigRat delta; // Maximum variation bound across the triangle
  BigRat r;     // Certified tube radius satisfying r^2 * (1 + c^2) <= 4 * c^2
  int symmetry_index = 0;
};

// A decomposed / annular identity tube certificate for cells where the
// projected convex hull undergoes silhouette topological collapse (e.g.
// eclipsed slivers where an interior vertex violates outer contact support).
//
// Proved correct via the Three-Way Split theorem:
// 1. Inner core: For adversary rotations with ||Q - 1|| <= r_min, an axis certificate
//    with contacts strictly on the true projected convex hull provides positive linear
//    displacement rate, preventing any Rupert pose.
// 2. Annular exceptional cone: For r_min <= ||Q - 1|| <= r within a cone of half-angle
//    arccos(c_cone) around the exceptional axis, quadratic rotation displacement dominates
//    the bounded support defect D.
// 3. Complementary directions: For adversary rotations outside the exceptional cone,
//    the complement axes (e.g. inherited from a sibling cell) have zero support defect
//    and enclose all adversary directions with net margin >= c_comp > 0.
struct DecomposedCertificate {
  // 1. Inner Core Certificate (contacts on true projected hull)
  // When a multi-axis flock is used, core_flock_axes holds the K core axes.
  // For single-axis compatibility, inner_core_axis holds a single axis.
  AxisCertificate inner_core_axis;
  int inner_index[3] = {-1, -1, -1};
  std::vector<AxisCertificate> core_flock_axes;

  // 2. Annular Certificate for the exceptional cone
  AxisCertificate annular_axis;
  BigRat r_min{0};   // Inner core boundary (e.g. 1/10000)
  BigRat r{0};       // Certified outer tube radius (e.g. 1/2000)
  BigRat c_cone{0};  // Cone cosine threshold (e.g. 99/100)
  BigRat delta{0};   // Triangle variation bound
  BigRat defect_D{0};// Maximum support defect budget (e.g. 8/10000000)
  std::array<BigRat, 3> defect0{BigRat(0), BigRat(0), BigRat(0)};
  BigRat c_core{0};  // Core cosine threshold (e.g. 2/1000)
  BigRat lam{0};     // Projection lambda
  std::array<BigRat, 3> w{BigRat(0), BigRat(0), BigRat(0)};

  // 3. Complementary Axes covering outside the exceptional cone
  std::vector<AxisCertificate> complement_axes;
  BigRat c_comp{0};  // Certified coverage margin outside the cone

  int symmetry_index = 0;
};

// ============================================================================
// BOUNDS ARCHITECTURE & CRITICAL NOTE ON DIRECT VS. EFFECTIVE BOUNDS
// ============================================================================
//
// DIRECT BOUNDS (stored on disk):
// - direct_r_lower, direct_c_lower: The margin and tube radius certified
//   STRICTLY by this single triangle's attached certificate covering its entire
//   spherical area (or 0 if no direct certificate has been found).
// - direct_r_upper, direct_c_upper: The upper bound computed directly on this
//   triangle via Wolfe support analysis (or 0 if not computed).
//
// EFFECTIVE BOUNDS (computed in memory via ComputeEffectiveBounds):
// - The BEST AVAILABLE / EFFECTIVE bound for a triangle is NOT simply the bound
//   recorded on the triangle itself; it is the collective bound over its children:
//     effective_r_lower = max(direct_r_lower, min_{i=0..3}(child[i].effective_r_lower))
//     effective_r_upper = min(direct_r_upper, max_{i=0..3}(child[i].effective_r_upper))
// - If the children are unresolved or incomplete, effective_r_lower falls back
//   to direct_r_lower (the parent triangle's certificate acts as an umbrella).
//
// DO NOT STORE EFFECTIVE BOUNDS ON DISK:
// Storing effective bounds on disk would cause a cascading write across all
// ancestor files up to the root whenever a single deep leaf is resolved.
// Instead, on disk each node stores strictly its own DIRECT data, keeping
// files small, decoupled, and safe for parallel editing.
// ============================================================================

struct NodeBounds {
  BigRat direct_r_lower{0};
  BigRat direct_r_upper{0};
  BigRat direct_c_lower{0};
  BigRat direct_c_upper{0};
};

struct EffectiveBounds {
  BigRat r_lower{0};
  BigRat r_upper{0};
  BigRat c_lower{0};
  BigRat c_upper{0};
  bool complete = false; // true if all sub-branches are fully certified
};

struct TreeNode {
  // Canonical base-4 hierarchical path string (e.g. "0", "013", "0321").
  // Alphabet is strictly {'0', '1', '2', '3'}.
  // Depth is path.size().
  std::string path;

  // Optional direct certificate covering this exact triangle (standard 4-axis cage).
  std::optional<TubeCertificate> direct_cert;

  // Optional decomposed certificate covering this exact triangle (Three-Way Split).
  std::optional<DecomposedCertificate> decomposed_cert;

  // Direct bounds computed directly on this triangle.
  NodeBounds direct_bounds;

  // If external is true, this node's 4 children are stored in a separate
  // external file named SubtreeFilename(path), e.g. "tree_013.json".
  bool external = false;

  // In-memory children (size is 4 when subdivided, empty when leaf or unexpanded external).
  std::vector<std::unique_ptr<TreeNode>> children;

  int depth() const { return static_cast<int>(path.size()); }
  bool is_leaf() const { return children.empty() && !external; }
  bool is_split() const { return !children.empty() || external; }
  bool has_certificate() const {
    return direct_cert.has_value() || decomposed_cert.has_value();
  }
  BigRat GetCertifiedRadius() const {
    if (direct_cert.has_value()) return direct_cert->r;
    if (decomposed_cert.has_value()) return decomposed_cert->r;
    return BigRat(0);
  }

  TriangleQ GetTriangle() const {
    return TriangleFromPath(path);
  }
};

// Recursively computes effective lower and upper bounds for node in memory.
// Walks children if present, taking min over children for r_lower and max for r_upper,
// and taking max with node's own direct_r_lower.
EffectiveBounds ComputeEffectiveBounds(const TreeNode &node);

// Returns the canonical subtree filename for a given path, e.g.:
// SubtreeFilename("013", ".artifacts/nopert229") -> ".artifacts/nopert229/tree_013.json"
std::string SubtreeFilename(std::string_view path, std::string_view base_dir = "");

// Serializes a tree or subtree to JSON.
// If shallow is true, nodes marked external = true are emitted as references
// ("external": true) without recursing into their children.
// If shallow is false, the full in-memory tree is serialized inline.
bool SaveTreeJson(const TreeNode &root, const std::string &filepath, bool shallow = true);

// Deserializes a tree from JSON.
// If load_external is true and base_dir is non-empty, any node marked external = true
// has its subtree loaded recursively from SubtreeFilename(path, base_dir).
// If load_external is false, external nodes are retained as unexpanded stubs (external = true).
std::unique_ptr<TreeNode> LoadTreeJson(
    const std::string &filepath,
    bool load_external = false,
    std::string_view base_dir = "");

// Detaches the children of node into a separate file tree_<node->path>.json in base_dir.
// Sets node->external = true and clears node->children.
bool DetachSubtreeToFile(TreeNode *node, const std::string &base_dir);

// Attaches the children from tree_<node->path>.json in base_dir into node->children.
// Sets node->external = false.
bool AttachSubtreeFromFile(TreeNode *node, const std::string &base_dir);

// Tree statistics.
struct TreeStats {
  int total_nodes = 0;
  int leaves = 0;
  int split_nodes = 0;
  int external_refs = 0;
  int direct_certificates = 0;
  int decomposed_certificates = 0;
  int max_depth = 0;
};

TreeStats ComputeTreeStats(const TreeNode &root);

// Result returned by FindNearestCertifiedNode queries.
struct NearestCertifiedNodeResult {
  std::string path;
  double direct_r_lower = 0.0;
  double effective_r_lower = 0.0;
  BigRat direct_r_rat{0};
  BigRat effective_r_rat{0};
  double angular_distance = 0.0; // angular distance in radians between query direction and triangle center (0 if contained)
  vec3 triangle_center{0.0, 0.0, 0.0};
  bool contains_direction = false; // true if the query direction is inside the certified spherical triangle

  double safe_radius() const {
    return std::max(direct_r_lower, effective_r_lower);
  }
  BigRat safe_radius_rat() const {
    return BigRat::Max(direct_r_rat, effective_r_rat);
  }
};

// Fast, thread-safe atlas of identity tube trees for querying view-dependent certified radii.
class TubeAtlas {
 public:
  struct FastNode {
    std::string path;
    double direct_r_lower = 0.0;
    double effective_r_lower = 0.0;
    BigRat direct_r_rat{0};
    BigRat effective_r_rat{0};
    bool is_leaf = false;
    std::unique_ptr<FastNode> children[4];
  };

  TubeAtlas() = default;

  // Loads tree_0.json .. tree_3.json from base_dir.
  // Returns number of trees successfully loaded (0..4).
  int LoadFromDir(const std::string &base_dir);

  // Loads a single tree into subwedge slot (0..3).
  bool LoadTree(int subwedge, const std::string &filepath);

  // Checks if any tree is loaded.
  bool IsLoaded() const {
    return roots_[0] || roots_[1] || roots_[2] || roots_[3];
  }
  bool IsLoaded(int subwedge) const {
    return subwedge >= 0 && subwedge < 4 && roots_[subwedge] != nullptr;
  }

  // Returns the certified safe tube radius (as double) for a given base-4 path string (e.g. "0", "1032").
  // If the path descends deeper than the tree, the enclosing leaf's bound applies.
  // If the tree node has effective_r_lower > 0, returns effective_r_lower.
  // Returns 0.0 if not certified or tree not loaded.
  double GetSafeRadiusForPath(std::string_view path) const;

  // Returns the exact rational bound.
  BigRat GetSafeRadiusRatForPath(std::string_view path) const;

  // Given triangle corners, finds its base-4 path from the root wedge
  // and returns the safe tube radius.
  double GetSafeRadiusForTriangle(const vec3 corners[3], int max_depth = 20) const;
  double GetSafeRadiusForTriangle(const std::array<vec3, 3> &corners, int max_depth = 20) const {
    return GetSafeRadiusForTriangle(corners.data(), max_depth);
  }

  // Given a base-4 path, returns the matching FastNode (or enclosing leaf) if available.
  const FastNode *FindNode(std::string_view path) const;

  // Root node pointer access for inspection / debugging.
  const FastNode *GetRoot(int subwedge) const {
    if (subwedge >= 0 && subwedge < 4) return roots_[subwedge].get();
    return nullptr;
  }

  // Finds the nearest certified node (direct_r_lower > 0 or effective_r_lower > 0)
  // to a given 3D unit direction vector.
  // If subwedge is in 0..3, restricts search to that tree. If -1, searches all loaded trees.
  std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNode(
      const vec3 &direction, int subwedge = -1) const;

  // Finds the nearest certified node to a spherical view triangle.
  std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNodeForTriangle(
      const vec3 corners[3], int subwedge = -1) const;
  std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNodeForTriangle(
      const std::array<vec3, 3> &corners, int subwedge = -1) const {
    return FindNearestCertifiedNodeForTriangle(corners.data(), subwedge);
  }

  // Finds the nearest certified node to a given base-4 path.
  std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNodeForPath(
      std::string_view path, int subwedge = -1) const;

 private:
  struct CertifiedCacheEntry {
    const FastNode *node = nullptr;
    vec3 center{0.0, 0.0, 0.0};
    vec3 corners[3];
    int subwedge = 0;
  };

  std::unique_ptr<FastNode> roots_[4];
  mutable std::vector<CertifiedCacheEntry> certified_cache_;
  mutable bool certified_cache_built_ = false;
  mutable std::mutex cache_mutex_;

  void EnsureCertifiedCache() const;

  static std::unique_ptr<FastNode> BuildFastNode(const TreeNode &node);
  static void ComputeFastEffectiveBounds(FastNode *node);
};

// Finds the nearest certified node in an in-memory TreeNode tree to a given direction.
std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNode(
    const TreeNode &root, const vec3 &direction);


} // namespace tubetree229

#endif // RUPERTS_TUBETREE229_H_
