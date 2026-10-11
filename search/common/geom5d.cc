#include "geom5d.h"

#include "solid.h"

#include <algorithm>
#include <cmath>
#include <optional>

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

int RootSign(int root, int c) { return (root >> (2 - c)) & 1 ? -1 : 1; }

bool SignedTriangleValid(int root, const TriangleQ &t) {
  for (const auto &p : t) {
    Q sum(0);
    for (int c = 0; c < 3; c++) {
      const Q v = RootSign(root, c) > 0 ? p[c] : -p[c];
      if (v < Q(0)) return false;
      sum = sum + v;
    }
    if (!(sum == Q(1))) return false;
  }
  return true;
}

int TriangleRoot(const TriangleQ &t) {
  for (int root = 0; root < 8; root++) {
    if (SignedTriangleValid(root, t)) return root;
  }
  return -1;
}

// Whether p is on root's plane.
static bool OnRootPlane(int root, const VecQ &p) {
  Q sum(0);
  for (int c = 0; c < 3; c++) sum = sum + (RootSign(root, c) > 0 ? p[c] : -p[c]);
  return sum == Q(1);
}

bool TriangleContains(const TriangleQ &outer, const TriangleQ &inner) {
  const Q one(1);
  // Both on one root plane (any root's plane through outer's corners; the
  // (x, y) projection is affine and injective on it).
  int root = -1;
  for (int r = 0; r < 8 && root < 0; r++) {
    if (OnRootPlane(r, outer[0]) && OnRootPlane(r, outer[1]) && OnRootPlane(r, outer[2])) root = r;
  }
  CHECK(root >= 0) << "outer triangle not on a root plane";
  for (const auto &c : inner) CHECK(OnRootPlane(root, c)) << "triangles not on one root plane";
  // Barycentric coordinates in the (x, y) projection, which is affine on
  // the plane.
  const Q ax = outer[1][0] - outer[0][0], ay = outer[1][1] - outer[0][1];
  const Q bx = outer[2][0] - outer[0][0], by = outer[2][1] - outer[0][1];
  const Q det = ax * by - ay * bx;
  // A degenerate outer triangle (e.g. a sliver collapsed by rounding)
  // contains no proper triangle.
  if (BigRat::Sign(det) == 0) return false;
  for (const auto &p : inner) {
    const Q px = p[0] - outer[0][0], py = p[1] - outer[0][1];
    // p - outer[0] = s (outer[1] - outer[0]) + u (outer[2] - outer[0]).
    const Q s = (px * by - py * bx) / det;
    const Q u = (ax * py - ay * px) / det;
    if (BigRat::Sign(s) < 0 || BigRat::Sign(u) < 0 || one < s + u) return false;
  }
  return true;
}

static std::optional<TriangleQ> OuterDyadicTriangleBits(const TriangleQ &t, int rel_bits) {
  // Differences are taken exactly: some code triangles (the snub's, where
  // symmetric facet planes are almost concurrent) are smaller than double
  // resolution at their coordinates (~1e-17). (#231's search took them
  // between the corners rounded to double: solid::kTriangleSizeInDouble.)
  const TriangleD d = solid::kTriangleSizeInDouble ? ToDouble(t) : TriangleD{};
  double size = 0.0;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      for (int k = 0; k < 3; k++) {
        const double diff = solid::kTriangleSizeInDouble ? d.corners[i][k] - d.corners[j][k]
                                                         : (t[i][k] - t[j][k]).ToDouble();
        size = std::max(size, std::abs(diff));
      }
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
  const int root = TriangleRoot(t);
  if (root < 0) return std::nullopt;
  const Q s0(RootSign(root, 0)), s1(RootSign(root, 1)), s2(RootSign(root, 2));
  for (int e = rel_bits - 4; e > 0; e--) {
    const Q grow = Q(1) + Q(BigInt(1), BigInt::Pow(BigInt(2), e));
    TriangleQ out;
    for (int i = 0; i < 3; i++) {
      const Q x = round(g[0] + (t[i][0] - g[0]) * grow), y = round(g[1] + (t[i][1] - g[1]) * grow);
      // On the root plane s0 x + s1 y + s2 z = 1.
      out[i] = {x, y, s2 * (Q(1) - s0 * x - s1 * y)};
    }
    // Leaving the root's octant only gets worse with more growth. (The
    // icosahedral searches did not check this: certificates over an outer
    // triangle that leaves the octant fail, and stay over the exact one.)
    if (solid::kOuterTriangleInRoot && !SignedTriangleValid(root, out)) return std::nullopt;
    if (TriangleContains(out, t)) return out;
  }
  return std::nullopt;
}

TriangleQ OuterDyadicTriangle(const TriangleQ &t, int rel_bits) {
  // Slivers (much thinner than their extent) need a finer grid; the exact
  // triangle itself is the last resort.
  for (int extra : {0, 16, 32, 64}) {
    if (auto out = OuterDyadicTriangleBits(t, rel_bits + extra)) return *out;
  }
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

Q CutPoint(const BoxQ &b, int axis, int eighths) {
  CHECK(eighths >= 1 && eighths <= 7) << eighths;
  return b.lo[axis] + (b.hi[axis] - b.lo[axis]) * Q(eighths, 8);
}

BoxQ LowerAt(const BoxQ &b, int axis, int eighths) {
  BoxQ r = b;
  r.hi[axis] = CutPoint(b, axis, eighths);
  return r;
}

BoxQ UpperAt(const BoxQ &b, int axis, int eighths) {
  BoxQ r = b;
  r.lo[axis] = CutPoint(b, axis, eighths);
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
