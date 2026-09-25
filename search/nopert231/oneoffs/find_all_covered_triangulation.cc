#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

struct Triangle3D {
  vec3 A, B, C;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0005;

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  for (int N : {16, 20, 24, 32}) {
    double tan_alpha = std::tan(alpha);
    double tan_outer = tan_alpha / std::cos(M_PI / N);
    double psi_outer = std::atan(tan_outer);

    for (int R_rings : {2, 3, 4, 5}) {
      std::vector<Triangle3D> tris;
      vec3 apex = u0;

      std::vector<std::vector<vec3>> rings(R_rings + 1, std::vector<vec3>(N));
      for (int r = 1; r <= R_rings; r++) {
        double psi = (double)r / R_rings * psi_outer;
        for (int k = 0; k < N; k++) {
          double phi = k * 2.0 * M_PI / N;
          rings[r][k] = yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
        }
      }

      // Ring 0 to 1
      for (int k = 0; k < N; k++) {
        tris.push_back({apex, rings[1][k], rings[1][(k + 1) % N]});
      }
      // Outer rings: try both diagonal splits for each quad!
      bool all_quads_ok = true;
      int quad_fail = 0;
      for (int r = 1; r < R_rings; r++) {
        for (int k = 0; k < N; k++) {
          int next_k = (k + 1) % N;
          vec3 A = rings[r][k];
          vec3 B = rings[r + 1][k];
          vec3 C = rings[r + 1][next_k];
          vec3 D = rings[r][next_k];

          // Diagonal 1: (A, B, C) and (A, C, D)
          bool d1_ok = false;
          bool t1_ok = false, t2_ok = false;
          for (size_t i = 0; i < all_v.size(); i++) {
            if (!t1_ok && yocto::dot(A, all_v[i]) >= c_core && yocto::dot(B, all_v[i]) >= c_core && yocto::dot(C, all_v[i]) >= c_core) t1_ok = true;
            if (!t2_ok && yocto::dot(A, all_v[i]) >= c_core && yocto::dot(C, all_v[i]) >= c_core && yocto::dot(D, all_v[i]) >= c_core) t2_ok = true;
          }
          if (t1_ok && t2_ok) d1_ok = true;

          // Diagonal 2: (B, C, D) and (B, D, A)
          bool d2_ok = false;
          bool t3_ok = false, t4_ok = false;
          for (size_t i = 0; i < all_v.size(); i++) {
            if (!t3_ok && yocto::dot(B, all_v[i]) >= c_core && yocto::dot(C, all_v[i]) >= c_core && yocto::dot(D, all_v[i]) >= c_core) t3_ok = true;
            if (!t4_ok && yocto::dot(B, all_v[i]) >= c_core && yocto::dot(D, all_v[i]) >= c_core && yocto::dot(A, all_v[i]) >= c_core) t4_ok = true;
          }
          if (t3_ok && t4_ok) d2_ok = true;

          if (!d1_ok && !d2_ok) {
            all_quads_ok = false;
            quad_fail++; std::cout << "Failed quad r=" << r << " k=" << k << "\n";
          }
        }
      }

      std::cout << "N=" << N << " rings=" << R_rings << ": quad_fail = " << quad_fail << "\n";
      if (all_quads_ok) {
        std::cout << ">>> 100% COVERED! N=" << N << " rings=" << R_rings << "\n";
      }
    }
  }

  return 0;
}
