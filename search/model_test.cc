// model_test.cc: Tests of the rational model (model.h): double and rational
// coordinates agree, and the vertices have the 5-fold symmetry about z.

#include "model.h"

#include <cmath>
#include <cstdlib>
#include <numbers>
#include <vector>

#include "ansi.h"
#include "base/logging.h"
#include "base/print.h"
#include "bignum/big-overloads.h"
#include "bignum/big.h"
#include "yocto-math.h"

using vec3 = yocto::vec<double, 3>;

// Vertex SEEDS * k + s is seed s rotated by 2 pi k / 5.
static constexpr int SEEDS = NUM_VERTICES / 5;
static_assert(SEEDS * 5 == NUM_VERTICES);

// Double and rational coordinates agree to within floating-point precision.
static void TestDoubleRationalAgreement() {
  Print("[RUN] TestDoubleRationalAgreement\n");
  double max_err = 0.0;
  for (int v = 0; v < NUM_VERTICES; v++) {
    vec3 d = Vertex(v);
    CHECK_EQ(d.x, VERTICES[v][0]);
    CHECK_EQ(d.y, VERTICES[v][1]);
    CHECK_EQ(d.z, VERTICES[v][2]);
    for (int c = 0; c < 3; c++) {
      max_err = std::max(max_err, std::abs(VERTICES[v][c] - VertexQ(v)[c].ToDouble()));
    }
  }
  Print("  Max |double - rational| = {}\n", max_err);
  CHECK_LT(max_err, 1e-15);
  Print("[PASS] TestDoubleRationalAgreement\n");
}

// The 5-fold rotation about z maps orbit k to orbit k + 1, preserving z and
// the cylindrical radius (to within the model's rounding).
static void TestC5Symmetry() {
  Print("[RUN] TestC5Symmetry\n");
  constexpr double angle = 2.0 * std::numbers::pi / 5.0;
  const double c = std::cos(angle), s = std::sin(angle);
  double max_rot_err = 0.0;
  for (int k = 0; k < 5; k++) {
    for (int seed = 0; seed < SEEDS; seed++) {
      vec3 cur = Vertex(SEEDS * k + seed);
      vec3 next = Vertex(SEEDS * ((k + 1) % 5) + seed);
      vec3 rotated = {c * cur.x - s * cur.y, s * cur.x + c * cur.y, cur.z};
      max_rot_err = std::max(max_rot_err, (double)yocto::length(rotated - next));
      CHECK_LT(std::abs(cur.z - next.z), 1e-15);
      CHECK_LT(std::abs(std::hypot(cur.x, cur.y) - std::hypot(next.x, next.y)), 1e-14);
    }
  }
  Print("  Max C5 rotation error: {}\n", max_rot_err);
  CHECK_LT(max_rot_err, 1e-14);

  // Every vertex is strictly inside the unit sphere (Lean's GoodPoly invariant).
  for (int v = 0; v < NUM_VERTICES; v++) {
    double norm = yocto::length(Vertex(v));
    CHECK_LT(norm, 1.0);
    CHECK_GT(norm, 0.0);
  }
  Print("[PASS] TestC5Symmetry\n");
}

// VertexQ returns a stable reference (singleton table).
static void TestSingleton() {
  Print("[RUN] TestSingleton\n");
  CHECK_EQ(&VertexQ(0), &VertexQ(0));
  Print("[PASS] TestSingleton\n");
}

int main(int argc, char **argv) {
  ANSI::Init();
  Print("=== Model tests ({} vertices) ===\n", NUM_VERTICES);
  TestDoubleRationalAgreement();
  TestC5Symmetry();
  TestSingleton();
  Print("=== All model tests passed ===\n");
  return 0;
}
