#ifndef _RUPERTS_TUBE229_H
#define _RUPERTS_TUBE229_H

#include <vector>
#include <string>
#include <array>
#include <set>

#include "tubetree229.h"
#include "yocto-math.h"
#include "bignum/big.h"
#include "bignum/big-vec.h"

// Collection of geometric, optimization, and exact verification routines
// for 4-axis identity tube certificates of Nopert #229.
class Tube229 {
 public:
  using vec2 = yocto::vec<double, 2>;
  using vec3 = yocto::vec<double, 3>;

  struct CandidateTriple {
    tubetree229::ContactInfo contacts[3];
    vec3 normalized_a;
    double strict_slack = 0.0;
    double B = 0.0;
  };

  // Exact rational vertex access for Nopert #229 (0..19).
  static BigVecQ3 VertexQ(int v);

  // Approximate double edge vector for a contact.
  static vec3 GetDoubleEdge(const tubetree229::ContactInfo &c);

  // Exact rational edge vector for a contact.
  static BigVecQ3 GetExactEdge(const tubetree229::ContactInfo &c);

  // 2D convex hull of projected silhouette points.
  static std::vector<int> ConvexHull2D(const std::vector<vec2> &points);

  // Generates silhouette boundary contacts for a given view direction with specified mix values.
  static std::vector<tubetree229::ContactInfo> GenerateSilhouetteContacts(
      const vec3 &view,
      const std::vector<int> &mix_samples_permille);

  // Generates valid 3-contact CandidateTriples over a triangle with configurable screening tolerance.
  static std::vector<CandidateTriple> GenerateCandidateTriples(
      const tubetree229::TriangleQ &tri,
      const std::vector<tubetree229::ContactInfo> &contacts,
      double screen_support_error = 1e-12);

  // Generates valid candidate triples over triangle tri for a specific view direction.
  // Computes view-specific 2D convex hull, silhouette contacts, and valid 3-contact combinations.
  static std::vector<CandidateTriple> GenerateCandidatesForView(
      const vec3 &view,
      const tubetree229::TriangleQ &tri,
      bool evaluate_over_triangle = true,
      int cone_samples = 4,
      bool include_boundaries = false,
      double screen_support_error = 1e-12);

  // Targeted Opposing Search (Tom Idea Point 4):
  // Given an unblocked direction n, specifically finds candidate triples with a · n < 0 (maximizing a · (-n)).
  static std::vector<CandidateTriple> FindOpposingCandidates(
      const tubetree229::TriangleQ &tri,
      const vec3 &oppose_dir,
      int max_candidates = 50,
      double screen_support_error = 1e-12);

  // Simplex geometry checks
  static bool PointInTetrahedron(
      const vec3 &p, const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3,
      double *out_margin = nullptr);

  // Finds closest face of simplex to origin and returns outward normal.
  static bool ClosestOriginFace(
      const std::vector<CandidateTriple> &candidates,
      const std::array<int, 4> &simplex,
      std::array<int, 3> *out_face,
      vec3 *out_normal);

  // Wolfe's minimum norm point / balanced tetrahedron algorithm.
  // If origin is not enclosed, returns false and optionally writes separating normal to out_separating_normal.
  static bool FindBalancedTetrahedron(
      const std::vector<vec3> &pts,
      std::array<int, 4> *out_simplex,
      vec3 *out_separating_normal = nullptr);

  static bool FindBalancedTetrahedron(
      const std::vector<CandidateTriple> &candidates,
      std::array<int, 4> *out_simplex,
      vec3 *out_separating_normal = nullptr);

  // Refines an active point pool from pts using cutting-plane iterations to enclose the origin.
  // Correctly handles near-origin faces (squared distance < 1e-12) without premature early return.
  static bool RefinePoolCuttingPlane(
      const std::vector<vec3> &pts,
      std::set<int> *in_out_pool,
      std::array<int, 4> *out_simplex,
      double *out_margin = nullptr,
      int max_iters = 50);

  // Fast double-precision validation of a 3-contact axis over triangle tri.
  // Checks support over all vertices and corners, positive weights over all corners.
  // Returns true and fills out_cand if geometrically valid.
  static bool DoubleCheckAxis(
      const tubetree229::TriangleQ &tri,
      const tubetree229::ContactInfo contacts[3],
      CandidateTriple *out_cand = nullptr,
      double screen_support_error = 1e-12);

  // Exact rational inscribed octahedron / axis radius.
  static BigRat ExactTetrahedronAxisRadius(const BigVecQ3 pts[4]);

  // Audits a single 3-contact axis over triangle tri in exact
  // rational arithmetic.
  static bool AuditAxis(
      const tubetree229::TriangleQ &tri,
      tubetree229::ContactInfo contacts[3],
      tubetree229::AxisCertificate *out_cert,
      BigVecQ3 *out_center,
      BigRat *out_delta,
      std::string *fail_reason = nullptr,
      const BigRat &max_allowed_defect = BigRat(0));

  // Exact adaptive rational audit of a 4-axis cage.
  static bool AuditCertificateAdaptive(
      const tubetree229::TriangleQ &tri,
      const tubetree229::TubeCertificate &test_cert,
      tubetree229::TubeCertificate *out_cert,
      std::string *fail_reason = nullptr);

  // Extremal regular tetrahedron orientation search.
  static bool FindExtremalTetrahedron(
      const std::vector<vec3> &pts,
      std::array<int, 4> *out_indices);
  static bool FindExtremalTetrahedron(
      const std::vector<CandidateTriple> &candidates,
      std::array<int, 4> *out_indices);

  // Fast single-view synthesis for easy leaves:
  // Samples centroid only, tests balanced tet, with one-shot opposing fallback.
  static bool SynthesizeCertificateFast(
      const tubetree229::TriangleQ &tri,
      int depth,
      tubetree229::TubeCertificate *out_cert,
      const std::vector<tubetree229::ContactInfo> &extra_contacts = {},
      const std::vector<CandidateTriple> &extra_axes = {});

  // Powerful multi-view & iterative cutting-plane synthesis for hard / canyon leaves:
  // Samples centroid + 3 corners across a rich mix permille grid, incorporates extra_axes,
  // and executes an iterative cutting-plane loop with FindOpposingCandidates,
  // RefinePoolCuttingPlane, and FindExtremalTetrahedron up to max_opposing_iters.
  static bool SynthesizeCertificateIterative(
      const tubetree229::TriangleQ &tri,
      int depth,
      tubetree229::TubeCertificate *out_cert,
      const std::vector<tubetree229::ContactInfo> &extra_contacts = {},
      const std::vector<CandidateTriple> &extra_axes = {},
      int max_opposing_iters = 5);

  // General synthesis: runs SynthesizeCertificateFast first; if that fails and !fast_only,
  // escalates to SynthesizeCertificateIterative.
  static bool SynthesizeCertificate(
      const tubetree229::TriangleQ &tri,
      int depth,
      tubetree229::TubeCertificate *out_cert,
      const std::vector<tubetree229::ContactInfo> &extra_contacts = {},
      const std::vector<CandidateTriple> &extra_axes = {},
      bool fast_only = false);

  // ============================================================================
  // DECOMPOSED & ANNULAR CERTIFICATE ROUTINES (THREE-WAY SPLIT THEOREM)
  // ============================================================================

  // Searches for a 3-contact axis certificate whose contacts lie strictly on the
  // true projected 2D convex hull of Polyhedron #229 for triangle tri (Idea 3 from TINY_SLIVER.md).
  //
  // Unlike standard silhouette generation where contact chords must be incident on
  // their support vertex, this searches over decoupled combinations of extreme hull
  // chords and true hull support vertices.
  //
  // Requirements checked:
  // - All 20 vertices have support upper bounds <= 0 across all 3 corners of tri.
  // - Outward 2D normals enclose the origin (positive linear displacement for the inner core).
  // - Weight lower bounds across tri are non-negative, with at least one strictly positive.
  // - Strict negative witness exists for each contact.
  //
  // Returns true and populates out_cert (and optionally out_center, out_delta) on success.
  static bool FindHullSupportAxis(
      const tubetree229::TriangleQ &tri,
      tubetree229::AxisCertificate *out_cert,
      BigVecQ3 *out_center = nullptr,
      BigRat *out_delta = nullptr,
      std::string *fail_reason = nullptr);

  struct AuditedAxis {
    tubetree229::AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
  };

  static std::vector<AuditedAxis> FindAllHullSupportAxes(
      const tubetree229::TriangleQ &tri,
      size_t max_axes = 200);

  // Verifies the annular dominance condition for an axis with a known support defect D:
  //   ((1/2) * r^2 * B + D)^2 <= r_min^2 * (1 - (1/4) * r^2) * (c_cone - delta)^2 * B^2
  //
  // Inputs:
  // - B: Bounding multiplier of the annular axis (> 0)
  // - defect_D: Total support defect budget across contacts (>= 0)
  // - c_cone: Cosine of the half-aperture of the exceptional cone (e.g. 99/100)
  // - delta: Variation bound of the axis across tri (>= 0, with delta < c_cone)
  // - in_out_r_min, in_out_r: If positive, tests the provided radii in exact arithmetic.
  //   If non-positive, automatically solves for valid conservative radii satisfying
  //   the inequality and writes them back.
  //
  // Returns true if the dominance condition holds with 0 < r_min < r and r^2 < 4.
  static bool CheckAnnularDominance(
      const BigRat &B,
      const BigRat &defect_D,
      const BigRat &c_cone,
      const BigRat &delta,
      BigRat *in_out_r_min,
      BigRat *in_out_r);

  // Evaluates whether a collection of candidate axes (e.g. inherited from a sibling cell)
  // covers all unit directions on S^2 outside the exceptional cone around exceptional_axis:
  //   For all omega in S^2 with dot(omega, exceptional_axis) < c_cone:
  //     max_{j} dot(omega, axis_j) >= c_comp > 0.
  //
  // Also audits each candidate axis over tri to verify that its support upper bounds
  // against all 20 vertices are <= 0.
  //
  // Returns true and writes out_c_comp if coverage is certified with margin > 0.
  static bool EvaluateComplementConeCoverage(
      const tubetree229::TriangleQ &tri,
      const std::vector<tubetree229::AxisCertificate> &axes,
      const vec3 &exceptional_axis_dir,
      double c_cone_thresh,
      BigRat *out_c_comp,
      int sphere_samples = 50000);

  // Complete synthesis of a DecomposedCertificate for difficult / canyon sliver cells:
  // 1. Searches for the 9-vertex hull inner core axis via FindHullSupportAxis.
  // 2. Evaluates the defect on the exceptional axis (or sibling axis 0) and computes
  //    defect bound D and valid radii r_min, r via CheckAnnularDominance.
  // 3. Verifies complementary direction coverage for sibling/candidate axes outside
  //    the exceptional cone via EvaluateComplementConeCoverage.
  // 4. Assembles the resulting DecomposedCertificate.
  //
  // Returns true and populates out_decomp on success.
  static bool SynthesizeDecomposedCertificate(
      const tubetree229::TriangleQ &tri,
      int depth,
      tubetree229::DecomposedCertificate *out_decomp,
      const tubetree229::TubeCertificate *sibling_cert = nullptr,
      std::string *fail_reason = nullptr);
};

#endif  // _RUPERTS_TUBE229_H
