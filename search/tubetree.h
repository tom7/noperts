#ifndef NOPERT_TUBETREE_H_
#define NOPERT_TUBETREE_H_

#include <algorithm>
#include <array>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "bignum/big.h"
#include "bignum/big-vec.h"
#include "yocto-math.h"

namespace tubetree {

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

// Contact directions mix two edges with weight mix / kMixScale. Must match
// Lean's AxisCertificate.mix : Fin 1001 with mixQ = mix / 1000.
inline constexpr int kMixScale = 1000;

// Information identifying a contact point on the silhouette.
struct ContactInfo {
  int edge_start = 0;
  int edge_finish = 0;
  int edge_start2 = 0;
  int edge_finish2 = 0;
  int mix = kMixScale; // 0..kMixScale: interpolation weight mix / kMixScale
  int vertex = 0; // support vertex index (into the model's vertex list)
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
// On disk each node stores only its own DIRECT data.
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
  // Base-4 path from the root of the tree (a code triangle), e.g. "", "013".
  // Digit k selects child k of TriangleQ::Subdivide. Depth is path.size().
  std::string path;

  // Optional direct certificate covering this exact triangle (standard 4-axis cage).
  std::optional<TubeCertificate> direct_cert;

  // Optional decomposed certificate covering this exact triangle (Three-Way Split).
  std::optional<DecomposedCertificate> decomposed_cert;

  // Direct bounds computed directly on this triangle.
  NodeBounds direct_bounds;

  // Children (4 when subdivided, empty for a leaf).
  std::vector<std::unique_ptr<TreeNode>> children;

  int depth() const { return static_cast<int>(path.size()); }
  bool is_leaf() const { return children.empty(); }
  bool is_split() const { return !children.empty(); }
  bool has_certificate() const {
    return direct_cert.has_value() || decomposed_cert.has_value();
  }
  BigRat GetCertifiedRadius() const {
    if (direct_cert.has_value()) return direct_cert->r;
    if (decomposed_cert.has_value()) return decomposed_cert->r;
    return BigRat(0);
  }

  // The node's triangle, when known (tubecode sets it on every node it
  // builds; it is not serialized).
  std::optional<TriangleQ> explicit_triangle;

  // Returns explicit_triangle; fails if it is not set.
  TriangleQ GetTriangle() const;
};

// Recursively computes effective lower and upper bounds for node in memory.
// Walks children if present, taking min over children for r_lower and max for r_upper,
// and taking max with node's own direct_r_lower.
EffectiveBounds ComputeEffectiveBounds(const TreeNode &node);

// Tree statistics.
struct TreeStats {
  int total_nodes = 0;
  int leaves = 0;
  int split_nodes = 0;
  int direct_certificates = 0;
  int decomposed_certificates = 0;
  int max_depth = 0;
};

TreeStats ComputeTreeStats(const TreeNode &root);

// Tree representation for a single projective triangle belonging to a code cell.
struct CodeTriangleTree {
  int triangle_index = 0;
  TriangleQ triangle;
  std::unique_ptr<TreeNode> root;
};

// Tree representation for an entire code cell X, containing trees for all its projective triangles.
struct CodeTree {
  int code_id = 0;
  std::string code_hex;
  std::vector<CodeTriangleTree> triangles;

  int TotalLeaves() const;
  bool IsFullyCertified() const;
};

// Serializes a CodeTree to JSON (tree.X.json).
bool SaveCodeTreeJson(const CodeTree &code_tree, const std::string &filepath);

// Deserializes a CodeTree from JSON.
std::unique_ptr<CodeTree> LoadCodeTreeJson(const std::string &filepath);

} // namespace tubetree

#endif // NOPERT_TUBETREE_H_
