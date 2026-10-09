#include "geom5d.h"

#include <cmath>
#include <cstdio>
#include <random>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

using namespace geom5d;

// A triangle on the plane u0+u1+u2 = 1 (the view triangle in codebdd.json).
static TriangleQ BaseTriangle() {
  return {VecQ{Q(0), Q(0), Q(1)}, VecQ{Q(500, 1343), Q(160, 1343), Q(683, 1343)},
          VecQ{Q(250, 1281), Q(115, 427), Q(98, 183)}};
}

static void TestTriangles() {
  // Exact and double splits agree; children of a triangle on the plane
  // u0+u1+u2 = 1 stay on it; the central child's corners are the midpoints.
  std::mt19937_64 rng(1);
  TriangleQ t = BaseTriangle();
  TriangleD d = ToDouble(t);
  std::string path;
  for (int depth = 0; depth < 30; depth++) {
    const int c = rng() % 4;
    path += (char)('0' + c);
    t = SplitTriangle(t, c);
    d = SplitTriangle(d, c);
    for (int i = 0; i < 3; i++) {
      CHECK(t[i][0] + t[i][1] + t[i][2] == Q(1));
      for (int k = 0; k < 3; k++) CHECK(std::abs(t[i][k].ToDouble() - d.corners[i][k]) < 1e-15);
    }
  }
  const TriangleQ t2 = SplitTrianglePath(BaseTriangle(), path);
  for (int i = 0; i < 3; i++) for (int k = 0; k < 3; k++) CHECK(t2[i][k] == t[i][k]);

  // Child 3's corners are the edge midpoints; every corner of a child is a
  // convex combination of the parent's corners with weights in {0, 1/2, 1}.
  const TriangleQ w = BaseTriangle();
  const TriangleQ c3 = SplitTriangle(w, 3);
  for (int k = 0; k < 3; k++) {
    CHECK(c3[0][k] == (w[0][k] + w[1][k]) / Q(2));
    CHECK(c3[1][k] == (w[1][k] + w[2][k]) / Q(2));
    CHECK(c3[2][k] == (w[2][k] + w[0][k]) / Q(2));
  }
  CHECK(AngularDiameter(SplitTriangle(ToDouble(w), 0)) < AngularDiameter(ToDouble(w)));
  printf("  triangles OK\n");
}

static void TestOuterDyadic() {
  // TriangleContains: a triangle contains itself and its children, not its
  // parent; corners on the boundary count.
  const TriangleQ w = BaseTriangle();
  CHECK(TriangleContains(w, w));
  for (int c = 0; c < 4; c++) {
    CHECK(TriangleContains(w, SplitTriangle(w, c)));
    if (c < 3) {
      CHECK(!TriangleContains(SplitTriangle(w, c), w));
    }
  }
  CHECK(!TriangleContains(SplitTriangle(w, 0), SplitTriangle(w, 1)));

  // OuterDyadicTriangle contains its triangle, has short dyadic coordinates
  // on the plane, and is only slightly larger.
  std::mt19937_64 rng(2);
  TriangleQ t = w;
  for (int depth = 0; depth < 25; depth++) {
    t = SplitTriangle(t, rng() % 4);
    for (int rel_bits : {10, 30}) {
      const TriangleQ o = OuterDyadicTriangle(t, rel_bits);
      CHECK(TriangleContains(o, t));
      // Not trivially contained in a big triangle: its corners are near t's.
      const TriangleD td = ToDouble(t), od = ToDouble(o);
      const double size = AngularDiameter(td);
      for (int i = 0; i < 3; i++) {
        CHECK(o[i][0] + o[i][1] + o[i][2] == Q(1));
        for (int k = 0; k < 2; k++) {
          // Dyadic with a small denominator.
          const BigInt den = o[i][k].Denominator();
          CHECK(den.ToString().size() < 40) << den.ToString();
          CHECK(std::abs(od.corners[i][k] - td.corners[i][k]) <=
                size * std::ldexp(1.0, 4 - rel_bits) + 1e-300)
              << depth << " " << rel_bits;
        }
      }
    }
  }
  printf("  outer dyadic OK\n");
}

static void TestBoxes() {
  for (int chart = 0; chart < 4; chart++) {
    const BoxQ root = RootBox(chart);
    const exact5d::Interval5 iv = exact5d::RestrictedRootInterval(chart);
    const exact5d::Interval5 iv2 = ToInterval(root);
    for (int a = 0; a < 5; a++) {
      CHECK(iv.min[a] == iv2.min[a] && iv.max[a] == iv2.max[a]);
    }
    // K: every chart is the full Cayley cube [-1, 1]^3 (no fivefold narrowing).
    for (int a = 0; a < 3; a++) CHECK(root.lo[a] == Q(-1) && root.hi[a] == Q(1));

    BoxQ b = root;
    for (int step = 0; step < 20; step++) {
      const int axis = WidestAxis(ToDouble(b));
      const BoxQ lo = LowerHalf(b, axis), hi = UpperHalf(b, axis);
      CHECK(lo.lo[axis] == b.lo[axis] && hi.hi[axis] == b.hi[axis]);
      CHECK(lo.hi[axis] == hi.lo[axis]);
      CHECK(lo.hi[axis] - lo.lo[axis] == hi.hi[axis] - hi.lo[axis]);
      b = (step % 2) ? lo : hi;
    }
  }
  CHECK(ContainsOrigin(ToDouble(RootBox(0))));
  // The quarter box [-1, -1/2] x ... no longer contains the origin.
  CHECK(!ContainsOrigin(ToDouble(LowerHalf(LowerHalf(RootBox(0), 0), 0))));
  printf("  boxes OK\n");
}

static void TestRotations() {
  std::mt19937_64 rng(2);
  std::uniform_real_distribution<double> u(-1.5, 1.5);
  const mat3 id = CayleyMatrix({0, 0, 0});
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) CHECK(id[i][j] == (i == j ? 1.0 : 0.0));
  for (int n = 0; n < 200; n++) {
    const vec3 w = {u(rng), u(rng), u(rng)};
    const mat3 r = CayleyMatrix(w);
    // Orthogonal with determinant 1.
    const mat3 rtr = yocto::transpose(r) * r;
    for (int i = 0; i < 3; i++) {
      for (int j = 0; j < 3; j++) CHECK(std::abs(rtr[i][j] - (i == j ? 1.0 : 0.0)) < 1e-12);
    }
    CHECK(std::abs(yocto::determinant(r) - 1.0) < 1e-12);
    // Independent formula ((1 - |w|^2) I + 2 w w^T + 2 [w]x) / (1 + |w|^2).
    const double ww = yocto::dot(w, w);
    for (int row = 0; row < 3; row++) {
      for (int col = 0; col < 3; col++) {
        double v = (row == col ? 1.0 - ww : 0.0) + 2 * w[row] * w[col];
        // [w]x has (row, col) entry -eps(row, col, k) w_k.
        if (row == 0 && col == 1) v += -2 * w.z;
        if (row == 1 && col == 0) v += 2 * w.z;
        if (row == 0 && col == 2) v += 2 * w.y;
        if (row == 2 && col == 0) v += -2 * w.y;
        if (row == 1 && col == 2) v += -2 * w.x;
        if (row == 2 && col == 1) v += 2 * w.x;
        CHECK(std::abs(r[col][row] - v / (1 + ww)) < 1e-12);
      }
    }
    // Charts flip two axes (a half-turn); the relative rotation stays in SO(3).
    for (int chart = 0; chart < 4; chart++) {
      CHECK(std::abs(yocto::determinant(RelativeRotation(chart, w)) - 1.0) < 1e-12);
    }
  }
  printf("  rotations OK\n");
}

int main() {
  TestTriangles();
  TestOuterDyadic();
  TestBoxes();
  TestRotations();
  printf("geom5d tests PASSED\n");
  return 0;
}
