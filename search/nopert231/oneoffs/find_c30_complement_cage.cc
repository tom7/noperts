#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static bool TetraBarycentricD(const vec3 &p0, const vec3 &p1, const vec3 &p2, const vec3 &p3,
                              const vec3 &x, double b[4]) {
  vec3 v0 = p1 - p0;
  vec3 v1 = p2 - p0;
  vec3 v2 = p3 - p0;
  vec3 vx = x - p0;

  double det = yocto::dot(v0, yocto::cross(v1, v2));
  if (std::abs(det) < 1e-12) return false;

  double det1 = yocto::dot(vx, yocto::cross(v1, v2));
  double det2 = yocto::dot(v0, yocto::cross(vx, v2));
  double det3 = yocto::dot(v0, yocto::cross(v1, vx));

  b[1] = det1 / det;
  b[2] = det2 / det;
  b[3] = det3 / det;
  b[0] = 1.0 - b[1] - b[2] - b[3];
  return true;
}

static bool TetraBarycentric(const BigVecQ3 &p0, const BigVecQ3 &p1, const BigVecQ3 &p2, const BigVecQ3 &p3,
                             const BigVecQ3 &x, BigRat b[4]) {
  BigVecQ3 v0 = {p1.x - p0.x, p1.y - p0.y, p1.z - p0.z};
  BigVecQ3 v1 = {p2.x - p0.x, p2.y - p0.y, p2.z - p0.z};
  BigVecQ3 v2 = {p3.x - p0.x, p3.y - p0.y, p3.z - p0.z};
  BigVecQ3 vx = {x.x - p0.x, x.y - p0.y, x.z - p0.z};

  BigRat det = v0.x * (v1.y * v2.z - v1.z * v2.y) -
               v0.y * (v1.x * v2.z - v1.z * v2.x) +
               v0.z * (v1.x * v2.y - v1.y * v2.x);
  if (det == 0) return false;

  BigRat det1 = vx.x * (v1.y * v2.z - v1.z * v2.y) -
                vx.y * (v1.x * v2.z - v1.z * v2.x) +
                vx.z * (v1.x * v2.y - v1.y * v2.x);

  BigRat det2 = v0.x * (vx.y * v2.z - vx.z * v2.y) -
                v0.y * (vx.x * v2.z - vx.z * v2.x) +
                v0.z * (vx.x * v2.y - v1.y * v2.x);

  BigRat det3 = v0.x * (v1.y * vx.z - v1.z * vx.y) -
                v0.y * (v1.x * vx.z - v1.z * vx.x) +
                v0.z * (v1.x * vx.y - v1.y * vx.x);

  b[1] = det1 / det;
  b[2] = det2 / det;
  b[3] = det3 / det;
  b[0] = BigRat(1) - b[1] - b[2] - b[3];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0_d = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};

  std::vector<int> zd_indices;
  std::vector<BigVecQ3> zd_u;
  std::vector<vec3> zd_ud;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      zd_indices.push_back(i);
      BigVecQ3 ui = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      zd_u.push_back(ui);
      zd_ud.push_back({ui.x.ToDouble(), ui.y.ToDouble(), ui.z.ToDouble()});
    }
  }
  std::cout << "Audited zero-defect axes: " << zd_indices.size() << "\n";

  BigRat zero(0);
  for (double c_target_d : {0.003, 0.002, 0.001, 0.0005}) {
    BigRat c_target((int)(c_target_d * 10000), 10000);
    for (double c_cone_d : {0.030, 0.028, 0.026, 0.024, 0.022, 0.020}) {
      BigRat c_cone((int)(c_cone_d * 1000), 1000);
      BigRat r_target = (c_target + del0) * 7 / 4;
      double r_target_d = r_target.ToDouble();
      vec3 oct_d[6] = {
        vec3{(float)r_target_d, 0, 0}, vec3{-(float)r_target_d, 0, 0},
        vec3{0, (float)r_target_d, 0}, vec3{0, -(float)r_target_d, 0},
        vec3{0, 0, (float)r_target_d}, vec3{0, 0, -(float)r_target_d}
      };
      BigVecQ3 oct[6] = {
        BigVecQ3(r_target, zero, zero), BigVecQ3(-r_target, zero, zero),
        BigVecQ3(zero, r_target, zero), BigVecQ3(zero, -r_target, zero),
        BigVecQ3(zero, zero, r_target), BigVecQ3(zero, zero, -r_target)
      };

      BigRat scale = (c_target + del0) / c_cone;
      BigVecQ3 p0 = {scale * u0.x, scale * u0.y, scale * u0.z};
      vec3 p0_d = (float)scale.ToDouble() * u0_d;

      int N = zd_indices.size();
      bool found = false;
      for (int i = 0; i < N && !found; i++) {
        for (int j = i + 1; j < N && !found; j++) {
          for (int k = j + 1; k < N; k++) {
            bool all_ok = true;
            for (int v = 0; v < 6; v++) {
              double b[4];
              if (!TetraBarycentricD(p0_d, zd_ud[i], zd_ud[j], zd_ud[k], oct_d[v], b) ||
                  b[0] < 1e-6 || b[1] < 1e-6 || b[2] < 1e-6 || b[3] < 1e-6) {
                all_ok = false;
                break;
              }
            }
            if (all_ok) {
              // Exact verify in BigRat
              bool exact_ok = true;
              for (int v = 0; v < 6; v++) {
                BigRat b[4];
                if (!TetraBarycentric(p0, zd_u[i], zd_u[j], zd_u[k], oct[v], b) ||
                    b[0] < 0 || b[1] < 0 || b[2] < 0 || b[3] < 0) {
                  exact_ok = false;
                  break;
                }
              }
              if (exact_ok) {
                std::cout << "FOUND COMPLEMENT CAGE FOR c_cone = " << c_cone_d
                          << ", c_target = " << c_target_d << "!\n";
                std::cout << "Indices: " << zd_indices[i] << ", " << zd_indices[j] << ", " << zd_indices[k] << "\n";
                return 0;
              }
            }
          }
        }
      }
    }
  }
  std::cout << "No valid cage found with c_cone >= 0.020.\n";
  return 0;
}
