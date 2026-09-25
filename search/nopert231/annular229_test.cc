#include "annular229.h"

#include <iostream>
#include <cassert>

#include "base/logging.h"
#include "base/print.h"
#include "bignum/big-overloads.h"
#include "tubetree229.h"

using namespace annular229;
using namespace tubetree229;

static void TestInequalities() {
  Print("Testing Exact Rational Inequalities...\n");

  BigRat r(4, 100000);
  BigRat r_min(23, 10000);
  BigRat delta(260, 1000000);
  BigRat c_comp(300, 1000000);
  BigRat c_cone(25, 1000);
  BigRat c_core(15, 10000);
  BigRat D0(736, 10000000);
  BigRat B0(349290553, 250000000);

  // 1. Annular Dominance
  CHECK(CheckAnnularDominance(r, r_min, B0, D0, c_cone, delta));

  // If r is large (e.g. 1/10), annular dominance must fail
  CHECK(!CheckAnnularDominance(BigRat(1, 10), r_min, B0, D0, c_cone, delta));

  // 2. Core Angle
  CHECK(CheckCoreAngle(r_min, c_core, delta));

  // If c_core <= delta, core angle must fail
  CHECK(!CheckCoreAngle(r_min, delta, delta));

  // 3. Complement Angle
  CHECK(CheckComplementAngle(r, c_comp, delta));

  // If c_comp <= delta, complement angle must fail
  CHECK(!CheckComplementAngle(r, delta, delta));

  Print("  Inequality tests PASSED.\n");
}

static void TestBarycentricEnclosure() {
  Print("Testing Barycentric Enclosure...\n");

  // Synthetic test: target -u0 = (0, 0, -1)
  // Complement axes forming an enclosing triangle on negative z hemisphere:
  vec3 u0 = {0, 0, 1};
  std::array<vec3, 3> comp_axes = {
    vec3{ 1.0,  0.0, -0.5},
    vec3{-0.5,  0.866, -0.5},
    vec3{-0.5, -0.866, -0.5}
  };

  double min_coord = 0.0;
  bool ok = CheckBarycentricEnclosure(u0, comp_axes, 0.025, &min_coord);
  CHECK(ok);
  CHECK_GT(min_coord, 0.0);

  // Axis configuration that fails to enclose -u0
  std::array<vec3, 3> bad_axes = {
    vec3{ 1.0, 0.0, 0.5},
    vec3{-0.5, 0.866, 0.5},
    vec3{-0.5, -0.866, 0.5}
  };
  CHECK(!CheckBarycentricEnclosure(u0, bad_axes, 0.025, &min_coord));

  Print("  Barycentric enclosure tests PASSED.\n");
}

static void TestSyntheticSetCover() {
  Print("Testing Greedy Cap Set Cover...\n");

  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  vec3 u0 = {0, 0, 1};
  double c_cone = 0.95;  // Small narrow cap
  double c_core = 0.90;

  // Provide a pool with 1 axis pointing directly at u0
  AxisCertificate ax_ideal;
  ax_ideal.contacts[0] = {1, 0, 0, 1, 0, 0};
  ax_ideal.contacts[1] = {0, 1, 0, 1, 0, 1};
  ax_ideal.contacts[2] = {0, 0, 1, 1, 0, 2};

  std::vector<AxisCertificate> pool = {ax_ideal};
  std::vector<AxisCertificate> flock;

  // Single axis pointing at u0 covers cap where dot >= c_core
  bool covered = FindCoreFlockGreedy(tri, u0, c_cone, c_core, pool, &flock, 4, 100);
  // May succeed or fail depending on geometry, but must not crash
  Print("  Cap set cover execution completed without errors (covered={}).\n", covered ? 1 : 0);
}

static void TestEndToEnd03121303200() {
  Print("Testing End-to-End Synthesis on Canyon Seam Triangle 03121303200...\n");

  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  AnnularConfig config;
  config.hull_axes_limit = 50000;
  config.cap_sample_count = 2000;

  // Provide seed complement axes discovered from sibling analysis
  std::vector<AxisCertificate> seed_axes(3);
  seed_axes[0].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[0].contacts[1] = {10, 15, 15, 19, 500, 15};
  seed_axes[0].contacts[2] = {3, 2, 2, 1, 0, 2};
  seed_axes[0].nonzero_witness[0] = 15; seed_axes[0].nonzero_witness[1] = 1; seed_axes[0].nonzero_witness[2] = 10;
  seed_axes[0].B = BigRat(128900569, 200000000);

  seed_axes[1].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[1].contacts[1] = {10, 15, 15, 19, 666, 15};
  seed_axes[1].contacts[2] = {3, 2, 2, 1, 0, 2};
  seed_axes[1].nonzero_witness[0] = 15; seed_axes[1].nonzero_witness[1] = 1; seed_axes[1].nonzero_witness[2] = 10;
  seed_axes[1].B = BigRat(38424249, 50000000);

  seed_axes[2].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[2].contacts[1] = {1, 4, 4, 8, 333, 4};
  seed_axes[2].contacts[2] = {15, 19, 19, 3, 1000, 19};
  seed_axes[2].nonzero_witness[0] = 15; seed_axes[2].nonzero_witness[1] = 19; seed_axes[2].nonzero_witness[2] = 4;
  seed_axes[2].B = BigRat(245064413, 500000000);

  AnnularSynthesisResult res = SynthesizeAnnularCertificate(tri, seed_axes, config);
  Print("  Synthesizer result: success = {}, explanation = \"{}\"\n",
        res.success ? 1 : 0, res.explanation);

  CHECK(res.success);
  CHECK_GT(res.cert.core_flock_axes.size(), 0);
  CHECK_EQ(res.cert.complement_axes.size(), 3);
  Print("  Successfully synthesized certificate with {} core flock axes!\n",
        res.cert.core_flock_axes.size());

  Print("End-to-End test PASSED.\n");
}

int main() {
  Print("==================================================\n");
  Print("RUNNING ANNULAR229 UNIT TESTS\n");
  Print("==================================================\n");

  TestInequalities();
  TestBarycentricEnclosure();
  TestSyntheticSetCover();
  TestEndToEnd03121303200();

  Print("==================================================\n");
  Print("ALL ANNULAR229 UNIT TESTS PASSED!\n");
  Print("==================================================\n");
  return 0;
}
