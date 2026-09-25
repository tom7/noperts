#include <iostream>
#include <vector>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static bool SolveTetraPoint(const vec3& p0, const vec3& p1,
                            const vec3& p2, const vec3& p3,
                            const vec3& target,
                            double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

  double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (std::abs(det) < 1e-12) return false;

  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero-defect Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
    std::cout << "Axis 0 audit failed: " << err << "\n";
    return 1;
  }
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int idx1 = 1283, idx2 = 4074, idx3 = 1041;
  vec3 u1 = {base_axes[idx1].center.x.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.y.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.z.ToDouble() / base_axes[idx1].cert.B.ToDouble()};
  vec3 u2 = {base_axes[idx2].center.x.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.y.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.z.ToDouble() / base_axes[idx2].cert.B.ToDouble()};
  vec3 u3 = {base_axes[idx3].center.x.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.y.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.z.ToDouble() / base_axes[idx3].cert.B.ToDouble()};

  double c_val = 0.00041;
  double delta_val = 0.00024;
  double R = 1.75 * (c_val + delta_val);
  vec3 oct[6] = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  for (double c_cone : {0.015, 0.020, 0.025, 0.028, 0.035, 0.040, 0.050, 0.060, 0.080, 0.100}) {
    double scale = (c_val + delta_val) / c_cone;
    vec3 p0 = u0 * scale;
    double min_w_all = 1.0;
    for (int k = 0; k < 6; k++) {
      double w[4];
      if (SolveTetraPoint(p0, u1, u2, u3, oct[k], w)) {
        double min_w = std::min({w[0], w[1], w[2], w[3]});
        if (min_w < min_w_all) min_w_all = min_w;
      }
    }
    std::cout << "c_cone = " << c_cone << " -> min_w_all = " << min_w_all << "\n";
  }

  return 0;
}
