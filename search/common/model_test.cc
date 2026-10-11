// model_test.cc: Tests of the rational model (model.h): double and rational
// coordinates agree, and the vertices are strictly inside the unit sphere.

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

// Every vertex is strictly inside the unit sphere (Lean's GoodPoly invariant).
static void TestInsideUnitSphere() {
  Print("[RUN] TestInsideUnitSphere\n");
  for (int v = 0; v < NUM_VERTICES; v++) {
    double norm = yocto::length(Vertex(v));
    CHECK_LT(norm, 1.0);
    CHECK_GT(norm, 0.0);
  }
  Print("[PASS] TestInsideUnitSphere\n");
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
  TestInsideUnitSphere();
  TestSingleton();
  Print("=== All model tests passed ===\n");
  return 0;
}
