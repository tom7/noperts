#include "bounds5d.h"

#include <algorithm>
#include <cmath>

#include "nopert231.h"

namespace bounds5d {

Quad Add(const Quad &a, const Quad &b) {
  Quad r;
  for (int m = 0; m < 10; m++) r.c[m] = a.c[m] + b.c[m];
  return r;
}

Quad Scale(double s, const Quad &a) {
  Quad r;
  for (int m = 0; m < 10; m++) r.c[m] = s * a.c[m];
  return r;
}

double Eval(const Quad &q, const vec3 &w) {
  const double x = w.x, y = w.y, z = w.z;
  const auto &c = q.c;
  return c[0] + c[1] * x + c[2] * y + c[3] * z + c[4] * x * x + c[5] * x * y +
         c[6] * x * z + c[7] * y * y + c[8] * y * z + c[9] * z * z;
}

namespace {
// Coefficient of monomial m (Lean order) in the Cayley numerator entry
// N[row][col] (CayleyEdgeCertificate.numeratorQuadratic) and in the
// denominator 1 + x² + y² + z².
//   m: 0=1 1=x 2=y 3=z 4=xx 5=xy 6=xz 7=yy 8=yz 9=zz
double NumCoeff(int row, int col, int m) {
  static constexpr double N[3][3][10] = {
      {{1, 0, 0, 0, 1, 0, 0, -1, 0, -1}, {0, 0, 0, -2, 0, 2, 0, 0, 0, 0}, {0, 0, 2, 0, 0, 0, 2, 0, 0, 0}},
      {{0, 0, 0, 2, 0, 2, 0, 0, 0, 0}, {1, 0, 0, 0, -1, 0, 0, 1, 0, -1}, {0, -2, 0, 0, 0, 0, 0, 0, 2, 0}},
      {{0, 0, -2, 0, 0, 0, 2, 0, 0, 0}, {0, 2, 0, 0, 0, 0, 0, 0, 2, 0}, {1, 0, 0, 0, -1, 0, 0, -1, 0, 1}}};
  return N[row][col][m];
}
constexpr double kDenom[10] = {1, 0, 0, 0, 1, 0, 0, 1, 0, 1};
}  // namespace

std::array<Quad, 3> Displacement(int chart, int inner, int outer) {
  const vec3 vin = Vertex(inner), vout = Vertex(outer);
  std::array<Quad, 3> d;
  for (int c = 0; c < 3; c++) {
    const double sign = (chart == 0 || chart == c + 1) ? 1.0 : -1.0;
    for (int m = 0; m < 10; m++) {
      double v = 0.0;
      for (int j = 0; j < 3; j++) v += vin[j] * NumCoeff(c, j, m);
      d[c].c[m] = sign * v - vout[c] * kDenom[m];
    }
  }
  return d;
}

Quad ContactTerm(const std::array<Quad, 3> &d, const vec3 &n, const vec3 &e) {
  const vec3 u = yocto::cross(n, e);
  return Add(Add(Scale(u.x, d[0]), Scale(u.y, d[1])), Scale(u.z, d[2]));
}

std::array<double, 27> BernsteinCoefficients(const Quad &q, const geom5d::BoxD &box) {
  const auto &c = q.c;
  const double lx = box.center.x - box.radius.x, ly = box.center.y - box.radius.y,
               lz = box.center.z - box.radius.z;
  const double wx = 2 * box.radius.x, wy = 2 * box.radius.y, wz = 2 * box.radius.z;
  const double a0 = Eval(q, {lx, ly, lz});
  const double ax = wx * (c[1] + 2 * c[4] * lx + c[5] * ly + c[6] * lz);
  const double ay = wy * (c[2] + c[5] * lx + 2 * c[7] * ly + c[8] * lz);
  const double az = wz * (c[3] + c[6] * lx + c[8] * ly + 2 * c[9] * lz);
  const double axx = c[4] * wx * wx, ayy = c[7] * wy * wy, azz = c[9] * wz * wz;
  const double axy = c[5] * wx * wy, axz = c[6] * wx * wz, ayz = c[8] * wy * wz;
  std::array<double, 27> out;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      for (int k = 0; k < 3; k++) {
        const double u = i / 2.0, v = j / 2.0, w = k / 2.0;
        double coeff = a0 + u * ax + v * ay + w * az;
        if (i == 2) coeff += axx;
        if (j == 2) coeff += ayy;
        if (k == 2) coeff += azz;
        coeff += u * v * axy + u * w * axz + v * w * ayz;
        out[9 * i + 3 * j + k] = coeff;
      }
    }
  }
  return out;
}

double BernsteinLower(const Quad &q, const geom5d::BoxD &box) {
  const auto coeffs = BernsteinCoefficients(q, box);
  return *std::min_element(coeffs.begin(), coeffs.end());
}

double DBound(const geom5d::BoxD &box) {
  double d = 1.0;
  for (int a = 0; a < 3; a++) {
    const double e = std::abs(box.center[a]) + box.radius[a];
    d += e * e;
  }
  return d;
}

double DisplacementError(const geom5d::BoxD &box) {
  return 300.0 * DBound(box) * 6e-16;
}

}  // namespace bounds5d
