#include "geom5d.h"

#include <algorithm>
#include <cmath>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace geom5d {

static VecQ MidQ(const VecQ &a, const VecQ &b) {
  const Q two(2);
  return {(a[0] + b[0]) / two, (a[1] + b[1]) / two, (a[2] + b[2]) / two};
}

TriangleQ SplitTriangle(const TriangleQ &t, int child) {
  switch (child) {
  case 0: return {t[0], MidQ(t[0], t[1]), MidQ(t[0], t[2])};
  case 1: return {MidQ(t[0], t[1]), t[1], MidQ(t[1], t[2])};
  case 2: return {MidQ(t[0], t[2]), MidQ(t[1], t[2]), t[2]};
  case 3: return {MidQ(t[0], t[1]), MidQ(t[1], t[2]), MidQ(t[2], t[0])};
  }
  LOG(FATAL) << "bad child " << child;
  return t;
}

TriangleQ SplitTrianglePath(TriangleQ t, std::string_view path) {
  for (char c : path) {
    CHECK(c >= '0' && c <= '3') << "bad path digit " << c;
    t = SplitTriangle(t, c - '0');
  }
  return t;
}

bool TriangleContains(const TriangleQ &outer, const TriangleQ &inner) {
  const Q one(1);
  for (const auto &t : {outer, inner}) {
    for (const auto &c : t) CHECK(c[0] + c[1] + c[2] == one) << "triangle not on x + y + z = 1";
  }
  // Barycentric coordinates in the (x, y) projection, which is affine on
  // the plane.
  const Q ax = outer[1][0] - outer[0][0], ay = outer[1][1] - outer[0][1];
  const Q bx = outer[2][0] - outer[0][0], by = outer[2][1] - outer[0][1];
  const Q det = ax * by - ay * bx;
  CHECK(BigRat::Sign(det) != 0) << "degenerate outer triangle";
  for (const auto &p : inner) {
    const Q px = p[0] - outer[0][0], py = p[1] - outer[0][1];
    // p - outer[0] = s (outer[1] - outer[0]) + u (outer[2] - outer[0]).
    const Q s = (px * by - py * bx) / det;
    const Q u = (ax * py - ay * px) / det;
    if (BigRat::Sign(s) < 0 || BigRat::Sign(u) < 0 || one < s + u) return false;
  }
  return true;
}

TriangleQ OuterDyadicTriangle(const TriangleQ &t, int rel_bits) {
  const TriangleD d = ToDouble(t);
  double size = 0.0;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      for (int k = 0; k < 3; k++) size = std::max(size, std::abs(d.corners[i][k] - d.corners[j][k]));
    }
  }
  CHECK(size > 0.0);
  const int bits = (int)std::ceil(-std::log2(size)) + rel_bits;
  const BigInt scale = BigInt::Pow(BigInt(2), bits);
  auto round = [&](const Q &v) {
    auto [num, den] = (v * Q(scale, BigInt(1)) + Q(1, 2)).Parts();
    return Q(BigInt::DivFloor(num, den), scale);
  };
  const Q third(1, 3);
  const VecQ g = {(t[0][0] + t[1][0] + t[2][0]) * third, (t[0][1] + t[1][1] + t[2][1]) * third,
                  (t[0][2] + t[1][2] + t[2][2]) * third};
  for (int e = rel_bits - 4; e > 0; e--) {
    const Q grow = Q(1) + Q(BigInt(1), BigInt::Pow(BigInt(2), e));
    TriangleQ out;
    for (int i = 0; i < 3; i++) {
      const Q x = round(g[0] + (t[i][0] - g[0]) * grow), y = round(g[1] + (t[i][1] - g[1]) * grow);
      out[i] = {x, y, Q(1) - x - y};
    }
    if (TriangleContains(out, t)) return out;
  }
  LOG(FATAL) << "no dyadic outer triangle";
  return t;
}

TriangleD ToDouble(const TriangleQ &t) {
  TriangleD d;
  for (int i = 0; i < 3; i++) {
    d.corners[i] = {t[i][0].ToDouble(), t[i][1].ToDouble(), t[i][2].ToDouble()};
  }
  return d;
}

TriangleD SplitTriangle(const TriangleD &t, int child) {
  const auto &c = t.corners;
  const vec3 m01 = (c[0] + c[1]) * 0.5, m12 = (c[1] + c[2]) * 0.5, m02 = (c[0] + c[2]) * 0.5;
  switch (child) {
  case 0: return {{c[0], m01, m02}};
  case 1: return {{m01, c[1], m12}};
  case 2: return {{m02, m12, c[2]}};
  case 3: return {{m01, m12, m02}};
  }
  LOG(FATAL) << "bad child " << child;
  return t;
}

vec3 Centroid(const TriangleD &t) {
  return (t.corners[0] + t.corners[1] + t.corners[2]) / 3.0;
}

double AngularDiameter(const TriangleD &t) {
  const vec3 u0 = yocto::normalize(t.corners[0]);
  const vec3 u1 = yocto::normalize(t.corners[1]);
  const vec3 u2 = yocto::normalize(t.corners[2]);
  return std::max({yocto::length(u0 - u1), yocto::length(u1 - u2), yocto::length(u2 - u0)});
}

BoxQ RootBox(int chart) {
  const Interval5 iv = exact5d::RestrictedRootInterval(chart);
  BoxQ b;
  for (int a = 0; a < 3; a++) {
    b.lo[a] = iv.min[a + 2];
    b.hi[a] = iv.max[a + 2];
  }
  return b;
}

BoxQ LowerHalf(const BoxQ &b, int axis) {
  BoxQ r = b;
  r.hi[axis] = (b.lo[axis] + b.hi[axis]) / Q(2);
  return r;
}

BoxQ UpperHalf(const BoxQ &b, int axis) {
  BoxQ r = b;
  r.lo[axis] = (b.lo[axis] + b.hi[axis]) / Q(2);
  return r;
}

Interval5 ToInterval(const BoxQ &b) {
  Interval5 iv;
  iv.min[0] = Q(0);
  iv.max[0] = Q(8, 5);
  iv.min[1] = Q(0);
  iv.max[1] = Q(4);
  for (int a = 0; a < 3; a++) {
    iv.min[a + 2] = b.lo[a];
    iv.max[a + 2] = b.hi[a];
  }
  return iv;
}

BoxD ToDouble(const BoxQ &b) {
  BoxD d;
  for (int a = 0; a < 3; a++) {
    d.center[a] = ((b.lo[a] + b.hi[a]) / Q(2)).ToDouble();
    d.radius[a] = ((b.hi[a] - b.lo[a]) / Q(2)).ToDouble();
  }
  return d;
}

int WidestAxis(const BoxD &b) {
  int axis = 0;
  if (b.radius.y > b.radius[axis]) axis = 1;
  if (b.radius.z > b.radius[axis]) axis = 2;
  return axis;
}

bool ContainsOrigin(const BoxD &b) {
  return std::abs(b.center.x) <= b.radius.x && std::abs(b.center.y) <= b.radius.y &&
         std::abs(b.center.z) <= b.radius.z;
}

mat3 ChartMatrix(int chart) {
  // CayleyAtlas.chartMatrix: diagonal, entry c is +1 if chart = 0 or
  // chart = c + 1, else -1.
  mat3 m = {};
  for (int c = 0; c < 3; c++) m[c][c] = (chart == 0 || chart == c + 1) ? 1.0 : -1.0;
  return m;
}

mat3 CayleyMatrix(const vec3 &w) {
  const double x = w.x, y = w.y, z = w.z;
  const double denom = 1.0 + x * x + y * y + z * z;
  // Row-major numerator (CayleyEdgeCertificate.numeratorQuadratic); yocto
  // matrices are column-major, m[col][row].
  const double n[3][3] = {
      {1 + x * x - y * y - z * z, 2 * (x * y - z), 2 * (x * z + y)},
      {2 * (x * y + z), 1 - x * x + y * y - z * z, 2 * (y * z - x)},
      {2 * (x * z - y), 2 * (y * z + x), 1 - x * x - y * y + z * z}};
  mat3 m;
  for (int row = 0; row < 3; row++) {
    for (int col = 0; col < 3; col++) m[col][row] = n[row][col] / denom;
  }
  return m;
}

mat3 RelativeRotation(int chart, const vec3 &w) {
  return ChartMatrix(chart) * CayleyMatrix(w);
}

}  // namespace geom5d
