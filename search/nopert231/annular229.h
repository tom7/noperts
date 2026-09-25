// Copyright 2026 Google LLC. Apache 2.0 License.
//
// Standalone library for synthesizing Decomposed Annular / Flock Certificates
// for stubborn cells in Nopert #229 (e.g. canyon seam cells like 03121303200).
//
// ============================================================================
// MATHEMATICAL ARCHITECTURE & GEOMETRIC MOTIVATION
// ============================================================================
// In the search for non-Rupertness certificates on Polyhedron #229, standard
// 4-axis projective cages fail on narrow horizon cells (the "seam" along vertex
// v14) due to the Obtuse Core Obstruction (see nopert229/notes/OBTUSE_CORE.md).
// Specifically, all zero-defect candidate axes at this horizon point in mutual
// obtuse directions, leaving a pinhole opening around the identity orientation.
//
// To circumvent this obstruction without endless subdivision, orientation space
// is decomposed into three geometrically distinct zones:
//
//   1. ANNULAR AXIS a0:
//      An axis that pushes the shadow boundary strictly outward faster than
//      any worst-case perturbation D0, covering an intermediate cylinder
//      [r_min, r] everywhere EXCEPT inside an exceptional forward cone C(u0, c_cone).
//      u0 = center(a0) / B(a0).
//
//   2. COMPLEMENT CAGE (3 zero-defect axes):
//      Three axes pointing opposing to u0 (i.e. dot(v_comp, u0) < 0) that strictly
//      enclose -u0 in their conical hull. They cage all adversary rotation axes
//      lying OUTSIDE the exceptional cone C(u0, c_cone).
//
//   3. CORE FLOCK (K zero-defect axes):
//      A collection of K zero-defect axes pointing towards u0 whose spherical
//      coverage footprints collectively cover 100% of the spherical cap
//      C(u0, c_cone) with positive margin >= c_core.
//
// This trihedral-plus-flock decomposition is formally verified by the Lean 4
// kernel theorem:
//   not_rupertPose_of_annular_exceptional_cone_certificate
// in Noperthedron/Noperthedron/Nopert229/AtlasProjectiveAnnularCertificate.lean.
// ============================================================================

#ifndef _RUPERTS_ANNULAR229_H
#define _RUPERTS_ANNULAR229_H

#include <vector>
#include <string>
#include <array>
#include <memory>

#include "tubetree229.h"
#include "tube229.h"
#include "yocto-math.h"
#include "bignum/big.h"
#include "bignum/big-vec.h"

namespace annular229 {

using vec3 = yocto::vec<double, 3>;

// Represents a candidate axis audited over a specific triangle, caching
// both its exact rational certificate and its floating-point center direction.
struct AuditedCandidate {
  tubetree229::AxisCertificate cert;
  // Variation center direction: approxNormalizedCenter = center / cert.B.
  // Note: Length is approximately ||center|| / B ~ 1.397, matching Lean's convention.
  vec3 approx_center;
  BigRat delta;
};

// Configuration parameters for annular certificate search.
// Parameters are coupled by Lean rational inequalities:
//
//   1. Annular Dominance:
//      ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4) * r^2) * ((c_cone - delta)^2 * B0^2)
//      => Sets lower bound on r_min * (c_cone - delta).
//
//   2. Core Angle:
//      r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
//      => Roughly r_min <= 2 * (c_core - delta). Sets upper bound on r_min for given c_core.
//
//   3. Complement Angle:
//      r^2 * (1 + (c_comp - delta)^2) <= 4 * (c_comp - delta)^2
struct AnnularConfig {
  // Outer radius: bounded by mismatchRadius of the triangle box.
  BigRat target_r{4, 100000};          // 4/100000 = 4e-5

  // Max variation ball radius across view triangle: ~1.66e-4 at depth 11.
  BigRat target_delta{195, 1000000};    // 195/1000000 = 1.95e-4

  // Complement cage margin: minimum barycentric coordinate / dot product margin.
  BigRat target_c_comp{35, 1000};      // 35/1000 = 0.035

  // Cone cutoff: dot(u0, v) >= c_cone defines the exceptional cap.
  BigRat target_c_cone{30, 1000};      // 30/1000 = 0.030

  // Core flock threshold: each flock axis covers dot(a_k, v) >= c_core.
  BigRat target_c_core{12, 10000};     // 12/10000 = 0.0012

  // Inner radius: cylinder radius separating core from annulus.
  BigRat target_r_min{19, 10000};      // 19/10000 = 0.0019

  // Defect bounds for annular axis a0.
  BigRat max_contact_defect{21, 100000}; // Max single contact defect
  BigRat max_D0{736, 10000000};        // Total weighted defect budget 7.36e-5

  // Solver search limits.
  int max_flock_size = 8;
  int cap_sample_count = 2000;
  int hull_axes_limit = 50000;

  // If true, automatically computes r_min and c_core from (B0, D0, delta, c_cone).
  bool auto_tune_parameters = true;
};

// Result of synthesis attempt.
struct AnnularSynthesisResult {
  bool success = false;
  tubetree229::DecomposedCertificate cert;
  std::string explanation;
};

// ============================================================================
// 1. Exact Rational Inequality Checks (matching Lean theorems)
// ============================================================================

// Evaluates annular dominance:
// ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4) * r^2) * ((c_cone - delta)^2 * B0^2)
bool CheckAnnularDominance(
    const BigRat &r, const BigRat &r_min,
    const BigRat &B0, const BigRat &D0,
    const BigRat &c_cone, const BigRat &delta);

// Evaluates core angle condition:
// r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
bool CheckCoreAngle(
    const BigRat &r_min, const BigRat &c_core,
    const BigRat &delta);

// Evaluates complement angle condition:
// r^2 * (1 + (c_comp - delta)^2) <= 4 * (c_comp - delta)^2
bool CheckComplementAngle(
    const BigRat &r, const BigRat &c_comp,
    const BigRat &delta);

// Evaluates whether barycentric coordinates of -u0 with respect to
// the complement axes are strictly positive.
bool CheckBarycentricEnclosure(
    const vec3 &u0,
    const std::array<vec3, 3> &comp_axes,
    double c_cone,
    double *out_min_coord = nullptr);

// Computes exact analytical lower bounds on r_min and c_core given (B0, D0, delta, c_cone).
// Returns true if valid parameters exist satisfying both inequalities.
bool DeriveAnalyticalParameters(
    const BigRat &r,
    const BigRat &B0,
    const BigRat &D0,
    const BigRat &delta,
    const BigRat &c_cone,
    BigRat *out_r_min,
    BigRat *out_c_core);

// ============================================================================
// 2. Geometric Synthesis Routines
// ============================================================================

// Audits a candidate pool of zero-defect axes over triangle tri
// whose variation radius satisfies delta <= max_delta.
std::vector<tubetree229::AxisCertificate> CollectZeroDefectPool(
    const tubetree229::TriangleQ &tri,
    int max_axes = 50000,
    const BigRat &max_delta = BigRat(3, 10000));

// Given annular axis center u0, searches zero_defect_pool for 3 axes
// forming a complement cage that strictly encloses -u0 with margin >= c_comp.
bool FindComplementCage(
    const tubetree229::TriangleQ &tri,
    const vec3 &u0,
    const std::vector<tubetree229::AxisCertificate> &zero_defect_pool,
    double c_cone,
    std::array<tubetree229::AxisCertificate, 3> *out_cage);

// Solves spherical cap set cover using greedy approximation:
// Samples the spherical cap C(u0, c_cone) with N quasi-uniform points
// (Fibonacci spiral), and greedily chooses axes from pool that maximize
// uncovered sample points where dot(axis, pt) >= c_core.
bool FindCoreFlockGreedy(
    const tubetree229::TriangleQ &tri,
    const vec3 &u0,
    double c_cone,
    double c_core,
    const std::vector<tubetree229::AxisCertificate> &zero_defect_pool,
    std::vector<tubetree229::AxisCertificate> *out_flock,
    int max_k = 8,
    int num_samples = 2000);

// ============================================================================
// 3. End-to-End Annular Synthesizer
// ============================================================================

// Master entry point: synthesizes a complete decomposed annular certificate
// for triangle tri. Designed as a fallback when standard 4-axis caging fails.
AnnularSynthesisResult SynthesizeAnnularCertificate(
    const tubetree229::TriangleQ &tri,
    const std::vector<tubetree229::AxisCertificate> &seed_axes = {},
    const AnnularConfig &config = AnnularConfig{});

}  // namespace annular229

#endif  // _RUPERTS_ANNULAR229_H
