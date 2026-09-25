#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct CageAxis {
  int id;
  vec3 v;
  vec3 d;
  double delta;
};

// Invert 3x3 matrix
bool Invert3x3(const double A[3][3], double inv[3][3]) {
  double det = A[0][0]*(A[1][1]*A[2][2] - A[1][2]*A[2][1]) -
               A[0][1]*(A[1][0]*A[2][2] - A[1][2]*A[2][0]) +
               A[0][2]*(A[1][0]*A[2][1] - A[1][1]*A[2][0]);
  if (std::abs(det) < 1e-9) return false;
  double invdet = 1.0 / det;
  inv[0][0] =  (A[1][1]*A[2][2] - A[1][2]*A[2][1]) * invdet;
  inv[0][1] = -(A[0][1]*A[2][2] - A[0][2]*A[2][1]) * invdet;
  inv[0][2] =  (A[0][1]*A[1][2] - A[0][2]*A[1][1]) * invdet;
  inv[1][0] = -(A[1][0]*A[2][2] - A[1][2]*A[2][0]) * invdet;
  inv[1][1] =  (A[0][0]*A[2][2] - A[0][2]*A[2][0]) * invdet;
  inv[1][2] = -(A[0][0]*A[1][2] - A[0][2]*A[1][0]) * invdet;
  inv[2][0] =  (A[1][0]*A[2][1] - A[1][1]*A[2][0]) * invdet;
  inv[2][1] = -(A[0][0]*A[2][1] - A[0][1]*A[2][0]) * invdet;
  inv[2][2] =  (A[0][0]*A[1][1] - A[0][1]*A[1][0]) * invdet;
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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
  double norm_u0 = yocto::length(u0);

  double c_cone = 0.017;
  vec3 d0 = -u0 / norm_u0;

  double max_delta = 0.000180;
  std::vector<CageAxis> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= max_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      cands.push_back({(int)i, v, v / yocto::length(v), ax.delta.ToDouble()});
    }
  }

  std::cout << "Axes with delta <= " << max_delta << ": " << cands.size() << "\n";

  // Target vertices: 6 octahedron vertices
  double c = 0.014; // box.c
  double scale = 1.75 * (c + max_delta);
  vec3 oct[6] = {
    {scale, 0, 0}, {-scale, 0, 0},
    {0, scale, 0}, {0, -scale, 0},
    {0, 0, scale}, {0, 0, -scale}
  };

  int tested = 0;
  int step = std::max(1, (int)cands.size() / 150);

  for (size_t i = 0; i < cands.size(); i += step) {
    for (size_t j = i + step; j < cands.size(); j += step) {
      for (size_t k = j + step; k < cands.size(); k += step) {
        tested++;
        vec3 d1 = cands[i].d;
        vec3 d2 = cands[j].d;
        vec3 d3 = cands[k].d;

        // Matrix with columns d1-d0, d2-d0, d3-d0
        double M[3][3] = {
          {d1.x - d0.x, d2.x - d0.x, d3.x - d0.x},
          {d1.y - d0.y, d2.y - d0.y, d3.y - d0.y},
          {d1.z - d0.z, d2.z - d0.z, d3.z - d0.z}
        };
        double invM[3][3];
        if (!Invert3x3(M, invM)) continue;

        bool ok = true;
        double min_lambda = 1.0;
        for (int v = 0; v < 6; v++) {
          vec3 rhs = oct[v] - d0;
          double l1 = invM[0][0]*rhs.x + invM[0][1]*rhs.y + invM[0][2]*rhs.z;
          double l2 = invM[1][0]*rhs.x + invM[1][1]*rhs.y + invM[1][2]*rhs.z;
          double l3 = invM[2][0]*rhs.x + invM[2][1]*rhs.y + invM[2][2]*rhs.z;
          double l0 = 1.0 - (l1 + l2 + l3);
          if (l0 < 0 || l1 < 0 || l2 < 0 || l3 < 0) {
            ok = false;
            break;
          }
          min_lambda = std::min(min_lambda, std::min(std::min(l0, l1), std::min(l2, l3)));
        }

        if (ok) {
          std::cout << "FOUND CAGE with delta <= " << max_delta << "!\n";
          std::cout << "Axes: " << cands[i].id << " (" << cands[i].delta << "), "
                    << cands[j].id << " (" << cands[j].delta << "), "
                    << cands[k].id << " (" << cands[k].delta << ")\n";
          std::cout << "Min lambda margin: " << min_lambda << "\n";
          return 0;
        }
      }
    }
  }

  std::cout << "Tested " << tested << " triples, none valid with step " << step << "\n";
  return 1;
}
