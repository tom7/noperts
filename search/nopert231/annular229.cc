// Copyright 2026 Google LLC. Apache 2.0 License.
//
// Implementation of Standalone Decomposed Annular Synthesizer for Nopert #229.
//
// ============================================================================
// DESIGN RATIONALE, SUBTLETIES, AND PITFALL WARNINGS
// ============================================================================
// 1. THE VECTOR CONVENTION CRITICAL PITFALL:
//    In Lean 4 (AtlasProjectiveLocalCertificate.lean, lines 176-178),
//    approxNormalizedCenter is defined as:
//      coordinate => (box.variationBall j coordinate).center / (box.certificate j).B
//    Crucially, this vector is NOT normalized to Euclidean unit length!
//    Its norm is ||center|| / B ~ 1.397.
//    In the Lean theorem, the inner product tested is:
//      (c_core : R) <= inner R axis (toR3 (approxNormalizedCenter))
//    where `axis` is a unit vector (||axis|| = 1).
//    If the C++ code normalizes approxNormalizedCenter to unit length,
//    every dot product is scaled down by ~1/1.397 ~ 0.716 (a 28.5% loss!).
//    This subtle discrepancy causes valid flock axes to fail the c_core
//    threshold. In this library, GetAxisCenterDirection ALWAYS returns
//    center / B (unnormalized), matching Lean exactly.
//
// 2. PARAMETER COUPLING & THE CAP SHRINKAGE PROPERTY:
//    The parameters r_min, c_cone, c_core, and delta are coupled:
//      - Annular Dominance requires:
//          r_min >= ((1/2) r^2 B0 + D0) / (sqrt(1 - (1/4) r^2) * (c_cone - delta) * B0)
//      - Core Angle requires:
//          c_core >= delta + r_min / sqrt(4 - r_min^2)
//    Notice the monotonicity:
//      As c_cone increases:
//        (c_cone - delta) increases -> r_min lower bound decreases
//        -> c_core lower bound decreases -> flock axes have WIDER footprints!
//      Simultaneously, the cap half-angle alpha satisfies:
//        cos(alpha) = c_cone / ||u0||
//        -> Increasing c_cone SHRINKS the cap!
//    Therefore, increasing c_cone makes greedy cap coverage strictly easier
//    in both ways (smaller cap + wider flock footprints). The only limit
//    is that the complement cage must still enclose outside the cone.
//    In practice, c_cone in [0.025, 0.035] works reliably across all cells.
//
// 3. DEAD ENDS & HISTORICAL PITFALLS (see nopert229/notes/OBTUSE_CORE.md):
//    - Dead End A: Attempting 4-axis cage synthesis on the seam horizon.
//      Proven impossible due to the Obtuse Core Obstruction.
//    - Dead End B: Single-axis core caging. A single axis pointing at u0
//      cannot cover the entire 75-degree cone without leaving rim deficits.
//      A flock of K >= 1 zero-defect axes is required.
//    - Dead End C: Coarse mix candidate pools. Standard hull generation with
//      mix steps of 0.1 may leave a 0.05% pinhole at the extreme rim.
//      Tuning c_cone or using fine mixes (333, 666, 800) eliminates the gap.
// ============================================================================

#include "annular229.h"

#include <iostream>
#include <cmath>
#include <algorithm>
#include <set>
#include <vector>

#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"
#include "base/logging.h"
#include "bignum/big-overloads.h"

namespace annular229 {

using namespace tubetree229;

// ============================================================================
// 1. Exact Rational Inequality Checks (matching Lean theorems)
// ============================================================================

// Evaluates annular dominance:
// ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4) * r^2) * ((c_cone - delta)^2 * B0^2)
// Matches Lean: AtlasProjectiveAnnularCertificate.lean, lines 607-610.
bool CheckAnnularDominance(
    const BigRat &r, const BigRat &r_min,
    const BigRat &B0, const BigRat &D0,
    const BigRat &c_cone, const BigRat &delta) {
  BigRat diff = c_cone - delta;
  if (diff <= BigRat(0)) return false;

  BigRat lhs = BigRat(1, 2) * r * r * B0 + D0;
  lhs = lhs * lhs;

  BigRat rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (diff * diff * B0 * B0);
  return lhs <= rhs;
}

// Evaluates core angle condition:
// r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
// Matches Lean: AtlasProjectiveAnnularCertificate.lean, lines 1542-1543.
bool CheckCoreAngle(
    const BigRat &r_min, const BigRat &c_core, const BigRat &delta) {
  BigRat diff = c_core - delta;
  if (diff <= BigRat(0)) return false;

  BigRat lhs = r_min * r_min * (BigRat(1) + diff * diff);
  BigRat rhs = BigRat(4) * diff * diff;
  return lhs <= rhs;
}

// Evaluates complement angle condition:
// r^2 * (1 + (c_comp - delta)^2) <= 4 * (c_comp - delta)^2
// Matches Lean: AtlasProjectiveAnnularCertificate.lean, line 1558.
bool CheckComplementAngle(
    const BigRat &r, const BigRat &c_comp, const BigRat &delta) {
  BigRat diff = c_comp - delta;
  if (diff <= BigRat(0)) return false;

  BigRat lhs = r * r * (BigRat(1) + diff * diff);
  BigRat rhs = BigRat(4) * diff * diff;
  return lhs <= rhs;
}

// Evaluates whether barycentric coordinates of target = -u0 with respect to
// the complement axes {v0, v1, v2} are strictly positive.
// Matches Lean: decomposedBarycentricValid in AtlasProjectiveAnnularCertificate.lean.
bool CheckBarycentricEnclosure(
    const vec3 &u0,
    const std::array<vec3, 3> &comp_axes,
    double c_cone,
    double *out_min_coord) {
  const vec3 &v0 = comp_axes[0];
  const vec3 &v1 = comp_axes[1];
  const vec3 &v2 = comp_axes[2];

  double det = yocto::dot(v0, yocto::cross(v1, v2));
  if (std::abs(det) < 1e-12) return false;

  vec3 target = -u0;
  double lam0 = yocto::dot(target, yocto::cross(v1, v2)) / det;
  double lam1 = yocto::dot(target, yocto::cross(v2, v0)) / det;
  double lam2 = yocto::dot(target, yocto::cross(v0, v1)) / det;

  double min_lam = std::min({lam0, lam1, lam2});
  if (out_min_coord) *out_min_coord = min_lam;

  // Strict enclosure requires all conical coordinates to be positive.
  return min_lam > 1e-6;
}

// Derives analytical parameters r_min and c_core from (B0, D0, delta, c_cone, r)
// by inverting the two governing rational inequalities.
bool DeriveAnalyticalParameters(
    const BigRat &r,
    const BigRat &B0,
    const BigRat &D0,
    const BigRat &delta,
    const BigRat &c_cone,
    BigRat *out_r_min,
    BigRat *out_c_core) {
  double r_d = r.ToDouble();
  double B0_d = B0.ToDouble();
  double D0_d = D0.ToDouble();
  double delta_d = delta.ToDouble();
  double c_cone_d = c_cone.ToDouble();

  if (c_cone_d <= delta_d) return false;

  // 1. Invert Annular Dominance for lower bound on r_min:
  //    numer = (1/2) * r^2 * B0 + D0
  //    denom = sqrt(1 - (1/4) * r^2) * (c_cone - delta) * B0
  double numer = 0.5 * (r_d * r_d) * B0_d + D0_d;
  double denom = std::sqrt(std::max(0.0, 1.0 - 0.25 * (r_d * r_d))) * (c_cone_d - delta_d) * B0_d;
  if (denom <= 1e-12) return false;
  double r_min_lower = numer / denom;

  // Round up to multiple of 1e-4 with safety margin
  double r_min_cand = std::ceil(r_min_lower * 10000.0) / 10000.0;
  if (r_min_cand - r_min_lower < 1e-5) r_min_cand += 1e-4;

  // 2. Invert Core Angle for lower bound on c_core:
  //    c_core >= delta + r_min / sqrt(4 - r_min^2)
  if (r_min_cand >= 2.0) return false;
  double c_core_lower = delta_d + r_min_cand / std::sqrt(4.0 - r_min_cand * r_min_cand);

  // Round up to multiple of 1e-4 with safety margin
  double c_core_cand = std::ceil(c_core_lower * 10000.0) / 10000.0;
  if (c_core_cand - c_core_lower < 1e-5) c_core_cand += 1e-4;

  // Convert to exact rationals
  int r_min_num = std::round(r_min_cand * 10000.0);
  int c_core_num = std::round(c_core_cand * 10000.0);
  BigRat r_min_rat(r_min_num, 10000);
  BigRat c_core_rat(c_core_num, 10000);

  // Ensure exact rational inequalities hold, bumping numerator if needed
  while (!CheckAnnularDominance(r, r_min_rat, B0, D0, c_cone, delta)) {
    r_min_num++;
    r_min_rat = BigRat(r_min_num, 10000);
  }
  while (!CheckCoreAngle(r_min_rat, c_core_rat, delta)) {
    c_core_num++;
    c_core_rat = BigRat(c_core_num, 10000);
  }

  if (out_r_min) *out_r_min = r_min_rat;
  if (out_c_core) *out_c_core = c_core_rat;
  return true;
}

// ============================================================================
// 2. Geometric Helper Routines
// ============================================================================

// Returns center / B (unnormalized, norm ~ 1.397) matching Lean's approxNormalizedCenter.
static vec3 GetAxisCenterDirection(const TriangleQ &tri, const AxisCertificate &ax) {
  BigVecQ3 center;
  BigRat delta;
  std::string err;
  AxisCertificate audited_cert;
  ContactInfo contacts[3] = {ax.contacts[0], ax.contacts[1], ax.contacts[2]};
  if (Tube229::AuditAxis(tri, contacts, &audited_cert, &center, &delta, &err, BigRat(1, 100))) {
    double B = audited_cert.B.ToDouble();
    return vec3{center.x.ToDouble() / B, center.y.ToDouble() / B, center.z.ToDouble() / B};
  }
  return {0, 0, 1};
}

// Audits hull support axes on tri and collects those satisfying delta <= max_delta.
std::vector<AxisCertificate> CollectZeroDefectPool(
    const TriangleQ &tri,
    int max_axes,
    const BigRat &max_delta) {
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, max_axes);
  std::vector<AxisCertificate> pool;
  pool.reserve(hull_axes.size());

  for (auto &cand : hull_axes) {
    if (cand.delta <= max_delta) {
      pool.push_back(cand.cert);
    }
  }
  return pool;
}

// Generates points on spherical cap C(u0, c_cone) using quasi-uniform Fibonacci spiral.
// The cap is defined by dot(axis, u0) >= c_cone where axis is unit length.
// Therefore, the angle alpha from normalize(u0) satisfies:
//   cos(alpha) = c_cone / length(u0).
static std::vector<vec3> SampleSphericalCap(
    const vec3 &u0_unnormalized, double c_cone, int count) {
  std::vector<vec3> pts;
  pts.reserve(count);

  double norm_u0 = yocto::length(u0_unnormalized);
  if (norm_u0 < 1e-12) return pts;
  vec3 w = u0_unnormalized / norm_u0;
  double cos_theta_min = c_cone / norm_u0;
  if (cos_theta_min > 1.0) cos_theta_min = 1.0;
  if (cos_theta_min < -1.0) cos_theta_min = -1.0;

  vec3 a = (std::abs(w.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 u = yocto::normalize(yocto::cross(w, a));
  vec3 v = yocto::cross(w, u);

  const double golden_ratio = (1.0 + std::sqrt(5.0)) / 2.0;

  for (int i = 0; i < count; i++) {
    double z = 1.0 - (1.0 - cos_theta_min) * (double(i) + 0.5) / double(count);
    double r_cyl = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = 2.0 * M_PI * i / golden_ratio;

    double x = r_cyl * std::cos(phi);
    double y = r_cyl * std::sin(phi);

    vec3 pt = x * u + y * v + z * w;
    pts.push_back(yocto::normalize(pt));
  }
  return pts;
}

// Solves greedy spherical cap set cover.
bool FindCoreFlockGreedy(
    const TriangleQ &tri,
    const vec3 &u0,
    double c_cone,
    double c_core,
    const std::vector<AxisCertificate> &zero_defect_pool,
    std::vector<AxisCertificate> *out_flock,
    int max_k,
    int num_samples) {
  if (zero_defect_pool.empty()) return false;

  std::vector<vec3> cap_samples = SampleSphericalCap(u0, c_cone, num_samples);
  const size_t N = cap_samples.size();

  // Convert pool axes to unnormalized variation centers (center / B)
  std::vector<vec3> pool_dirs;
  pool_dirs.reserve(zero_defect_pool.size());
  for (const auto &ax : zero_defect_pool) {
    pool_dirs.push_back(GetAxisCenterDirection(tri, ax));
  }

  // Precompute coverage bitsets: which sample points does each candidate cover?
  std::vector<std::vector<int>> covered_by_axis(pool_dirs.size());
  for (size_t a = 0; a < pool_dirs.size(); a++) {
    for (size_t s = 0; s < N; s++) {
      if (yocto::dot(pool_dirs[a], cap_samples[s]) >= c_core) {
        covered_by_axis[a].push_back(s);
      }
    }
  }

  // Greedy set cover loop
  std::vector<bool> sample_covered(N, false);
  size_t remaining_uncovered = N;
  std::vector<int> selected_axes;

  std::cout << "  [FindCoreFlockGreedy] pool=" << zero_defect_pool.size()
            << ", cap=" << N << ", c_cone=" << c_cone << ", c_core=" << c_core
            << ", max_k=" << max_k << "\n";

  for (int iter = 0; iter < max_k && remaining_uncovered > 0; iter++) {
    int best_axis = -1;
    size_t best_new_covered = 0;

    for (size_t a = 0; a < pool_dirs.size(); a++) {
      size_t newly_covered = 0;
      for (int s_idx : covered_by_axis[a]) {
        if (!sample_covered[s_idx]) newly_covered++;
      }
      if (newly_covered > best_new_covered) {
        best_new_covered = newly_covered;
        best_axis = a;
      }
    }

    if (best_axis == -1 || best_new_covered == 0) {
      std::cout << "    iter " << iter << ": no more coverage progress! remaining = "
                << remaining_uncovered << "\n";
      break;
    }

    selected_axes.push_back(best_axis);
    for (int s_idx : covered_by_axis[best_axis]) {
      if (!sample_covered[s_idx]) {
        sample_covered[s_idx] = true;
        remaining_uncovered--;
      }
    }
    std::cout << "    iter " << iter << ": added axis " << best_axis
              << ", newly covered: " << best_new_covered
              << ", remaining uncovered: " << remaining_uncovered << " / " << N << "\n";
  }

  if (remaining_uncovered == 0) {
    if (out_flock) {
      out_flock->clear();
      for (int a_idx : selected_axes) {
        out_flock->push_back(zero_defect_pool[a_idx]);
      }
    }
    return true;
  }
  return false;
}

// Searches zero_defect_pool for 3 axes forming a complement cage enclosing -u0.
bool FindComplementCage(
    const TriangleQ &tri,
    const vec3 &u0,
    const std::vector<AxisCertificate> &zero_defect_pool,
    double c_cone,
    std::array<AxisCertificate, 3> *out_cage) {
  if (zero_defect_pool.size() < 3) return false;

  std::vector<vec3> dirs;
  dirs.reserve(zero_defect_pool.size());
  for (const auto &ax : zero_defect_pool) {
    dirs.push_back(GetAxisCenterDirection(tri, ax));
  }

  // Find candidate axes that point roughly opposite to u0 (dot < 0)
  std::vector<int> opposing;
  for (size_t i = 0; i < dirs.size(); i++) {
    if (yocto::dot(u0, dirs[i]) < 0.0) opposing.push_back(i);
  }

  // Search triplets of opposing axes
  for (size_t i0 = 0; i0 < opposing.size(); i0++) {
    for (size_t i1 = i0 + 1; i1 < opposing.size(); i1++) {
      for (size_t i2 = i1 + 1; i2 < opposing.size(); i2++) {
        int a0 = opposing[i0], a1 = opposing[i1], a2 = opposing[i2];
        std::array<vec3, 3> triplet = {dirs[a0], dirs[a1], dirs[a2]};
        double min_bary = 0.0;
        if (CheckBarycentricEnclosure(u0, triplet, c_cone, &min_bary)) {
          if (out_cage) {
            (*out_cage)[0] = zero_defect_pool[a0];
            (*out_cage)[1] = zero_defect_pool[a1];
            (*out_cage)[2] = zero_defect_pool[a2];
          }
          return true;
        }
      }
    }
  }
  return false;
}

// ============================================================================
// 3. End-to-End Annular Synthesizer
// ============================================================================

AnnularSynthesisResult SynthesizeAnnularCertificate(
    const TriangleQ &tri,
    const std::vector<AxisCertificate> &seed_axes,
    const AnnularConfig &initial_config) {
  AnnularSynthesisResult res;
  AnnularConfig config = initial_config;

  // 1. Collect zero-defect candidate axes, seeded with any prior valid axes
  auto pool = seed_axes;
  auto hull_pool = CollectZeroDefectPool(tri, config.hull_axes_limit, config.target_delta);
  pool.insert(pool.end(), hull_pool.begin(), hull_pool.end());
  if (pool.empty()) {
    res.explanation = "Failed to collect any zero-defect axes under target delta.";
    return res;
  }

  // 2. Audit Annular Axis a0 (boundary contacts along seam)
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, config.max_contact_defect)) {
    res.explanation = "Failed to audit annular axis a0: " + err;
    return res;
  }

  // 3. Analytical Parameter Tuning or Direct Check
  if (config.auto_tune_parameters) {
    BigRat auto_r_min, auto_c_core;
    if (!DeriveAnalyticalParameters(config.target_r, ax0.B, config.max_D0,
                                    config.target_delta, config.target_c_cone,
                                    &auto_r_min, &auto_c_core)) {
      res.explanation = "Failed to derive valid analytical parameters.";
      return res;
    }
    config.target_r_min = auto_r_min;
    config.target_c_core = auto_c_core;
    std::cout << "  [AutoTune] r_min=" << config.target_r_min.ToString()
              << ", c_core=" << config.target_c_core.ToString()
              << ", c_cone=" << config.target_c_cone.ToString() << "\n";
  } else {
    if (!CheckAnnularDominance(config.target_r, config.target_r_min, ax0.B, config.max_D0,
                               config.target_c_cone, config.target_delta)) {
      res.explanation = "Annular dominance inequality failed.";
      return res;
    }
    if (!CheckCoreAngle(config.target_r_min, config.target_c_core, config.target_delta)) {
      res.explanation = "Core angle inequality failed.";
      return res;
    }
  }

  if (!CheckComplementAngle(config.target_r, config.target_c_comp, config.target_delta)) {
    res.explanation = "Complement angle inequality failed.";
    return res;
  }

  // 4. Find complement cage enclosing -u0
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  std::array<AxisCertificate, 3> comp_cage;
  if (!FindComplementCage(tri, u0, pool, config.target_c_cone.ToDouble(), &comp_cage)) {
    res.explanation = "Failed to find complement cage strictly enclosing -u0.";
    return res;
  }

  // 5. Find core flock covering cap C(u0, c_cone)
  // If greedy cover on the initial c_cone leaves an uncovered boundary point,
  // we step c_cone slightly larger in [0.028, 0.035].
  std::vector<AxisCertificate> flock;
  bool flock_ok = false;

  std::vector<double> cone_sweep;
  if (config.auto_tune_parameters) {
    cone_sweep = {config.target_c_cone.ToDouble(), 0.030, 0.032, 0.035};
  } else {
    cone_sweep = {config.target_c_cone.ToDouble()};
  }

  for (double c_cone_val : cone_sweep) {
    BigRat cur_c_cone(std::round(c_cone_val * 1000.0), 1000);
    BigRat cur_r_min, cur_c_core;
    if (config.auto_tune_parameters) {
      if (!DeriveAnalyticalParameters(config.target_r, ax0.B, config.max_D0,
                                      config.target_delta, cur_c_cone,
                                      &cur_r_min, &cur_c_core)) {
        continue;
      }
    } else {
      cur_c_cone = config.target_c_cone;
      cur_r_min = config.target_r_min;
      cur_c_core = config.target_c_core;
    }

    if (FindCoreFlockGreedy(tri, u0, cur_c_cone.ToDouble(), cur_c_core.ToDouble(),
                            pool, &flock, config.max_flock_size, config.cap_sample_count)) {
      config.target_c_cone = cur_c_cone;
      config.target_r_min = cur_r_min;
      config.target_c_core = cur_c_core;
      flock_ok = true;
      break;
    }
  }

  if (!flock_ok) {
    res.explanation = "Failed to cover spherical cap with greedy core flock.";
    return res;
  }

  // Assemble full decomposed certificate
  res.success = true;
  res.cert.annular_axis = ax0;
  res.cert.r = config.target_r;
  res.cert.r_min = config.target_r_min;
  res.cert.delta = config.target_delta;
  res.cert.c_comp = config.target_c_comp;
  res.cert.c_cone = config.target_c_cone;
  res.cert.c_core = config.target_c_core;
  res.cert.defect_D = config.max_D0;
  res.cert.complement_axes = {comp_cage[0], comp_cage[1], comp_cage[2]};
  res.cert.core_flock_axes = flock;
  res.explanation = "Successfully synthesized decomposed annular certificate with K=" +
                    std::to_string(flock.size()) + " core flock axes.";
  return res;
}

}  // namespace annular229
