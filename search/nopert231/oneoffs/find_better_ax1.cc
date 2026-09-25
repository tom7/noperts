#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

// Solves 4x4 linear system M * x = b using Cramer's rule / Gauss
// Columns of M are [p0; 1], [p1; 1], [p2; 1], [p3; 1].
bool Invert4x4(const vec3 p[4], double invM[4][4], double *det_out) {
  // M[row][col]:
  // row 0: p[col].x
  // row 1: p[col].y
  // row 2: p[col].z
  // row 3: 1
  double m[4][4];
  for (int j = 0; j < 4; j++) {
    m[0][j] = p[j].x;
    m[1][j] = p[j].y;
    m[2][j] = p[j].z;
    m[3][j] = 1.0;
  }

  // Gauss-Jordan elimination:
  double a[4][8];
  for (int r = 0; r < 4; r++) {
    for (int c = 0; c < 4; c++) a[r][c] = m[r][c];
    for (int c = 0; c < 4; c++) a[r][4 + c] = (r == c ? 1.0 : 0.0);
  }

  double det = 1.0;
  for (int i = 0; i < 4; i++) {
    int pivot = i;
    for (int r = i + 1; r < 4; r++) {
      if (std::abs(a[r][i]) > std::abs(a[pivot][i])) pivot = r;
    }
    if (std::abs(a[pivot][i]) < 1e-12) return false;
    if (pivot != i) {
      for (int c = 0; c < 8; c++) std::swap(a[i][c], a[pivot][c]);
      det = -det;
    }
    double pval = a[i][i];
    det *= pval;
    for (int c = 0; c < 8; c++) a[i][c] /= pval;
    for (int r = 0; r < 4; r++) {
      if (r != i) {
        double factor = a[r][i];
        for (int c = 0; c < 8; c++) a[r][c] -= factor * a[i][c];
      }
    }
  }

  *det_out = det;
  for (int r = 0; r < 4; r++) {
    for (int c = 0; c < 4; c++) invM[r][c] = a[r][4 + c];
  }
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};

  // ax2 = axes[24], ax3 = axes[210]
  const auto &ax2_data = axes[24];
  const auto &ax3_data = axes[210];
  double B2 = ax2_data.cert.B.ToDouble();
  double B3 = ax3_data.cert.B.ToDouble();
  vec3 u2 = vec3{ax2_data.center.x.ToDouble() / B2, ax2_data.center.y.ToDouble() / B2, ax2_data.center.z.ToDouble() / B2};
  vec3 u3 = vec3{ax3_data.center.x.ToDouble() / B3, ax3_data.center.y.ToDouble() / B3, ax3_data.center.z.ToDouble() / B3};

  double c_cone = 0.017;
  double c = 0.001;

  // 6 octahedron vertices
  vec3 oct_dir[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  std::cout << "Testing replacement for ax1 among " << axes.size() << " axes...\n";

  int found = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    double delta_i = ax.delta.ToDouble();
    if (delta_i > 0.000180) continue;

    double box_delta = std::max({del0.ToDouble(), delta_i, ax2_data.delta.ToDouble(), ax3_data.delta.ToDouble()});
    double scale0 = (c + box_delta) / c_cone;
    vec3 p0 = scale0 * u0;

    double B1 = ax.cert.B.ToDouble();
    vec3 u1 = vec3{ax.center.x.ToDouble() / B1, ax.center.y.ToDouble() / B1, ax.center.z.ToDouble() / B1};

    vec3 pts[4] = {p0, u1, u2, u3};
    double invM[4][4];
    double det;
    if (!Invert4x4(pts, invM, &det)) continue;

    // Test the 6 octahedron targets: (7/4) * (c + box_delta) * oct_dir[k]
    double target_radius = 1.75 * (c + box_delta);
    bool all_pos = true;
    for (int k = 0; k < 6; k++) {
      vec3 tgt = target_radius * oct_dir[k];
      double tgt_vec[4] = {tgt.x, tgt.y, tgt.z, 1.0};
      for (int row = 0; row < 4; row++) {
        double bary = 0;
        for (int col = 0; col < 4; col++) bary += invM[row][col] * tgt_vec[col];
        if (bary < 0) {
          all_pos = false;
          break;
        }
      }
      if (!all_pos) break;
    }

    if (all_pos) {
      std::cout << "FOUND WINNING AXIS 1! Index " << i << ", delta = " << delta_i
                << ", box_delta = " << box_delta << "\n";
      found++;
      if (found >= 5) break;
    }
  }

  std::cout << "Total winning replacements found: " << found << "\n";
  return 0;
}
