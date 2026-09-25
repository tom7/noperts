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
  double alpha = std::acos(cos_alpha); // ~69.2 deg
  double c_core = 0.0001;

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  for (int N : {12, 16, 24, 32, 48}) {
    double tan_alpha = std::tan(alpha);
    double tan_outer = tan_alpha / std::cos(M_PI / N);
    double psi_outer = std::atan(tan_outer);

    for (int R_rings : {2, 3, 4}) {
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

      // Ring 0 to Ring 1: apex triangles
      for (int k = 0; k < N; k++) {
        tris.push_back({apex, rings[1][k], rings[1][(k + 1) % N]});
      }
      // Ring r to Ring r+1
      for (int r = 1; r < R_rings; r++) {
        for (int k = 0; k < N; k++) {
          int next_k = (k + 1) % N;
          tris.push_back({rings[r][k], rings[r + 1][k], rings[r + 1][next_k]});
          tris.push_back({rings[r][k], rings[r + 1][next_k], rings[r][next_k]});
        }
      }

      int uncov = 0;
      for (size_t t = 0; t < tris.size(); t++) {
        bool cov = false;
        for (size_t i = 0; i < all_v.size(); i++) {
          if (yocto::dot(tris[t].A, all_v[i]) >= c_core &&
              yocto::dot(tris[t].B, all_v[i]) >= c_core &&
              yocto::dot(tris[t].C, all_v[i]) >= c_core) {
            cov = true;
            break;
          }
        }
        if (!cov) uncov++;
      }
      std::cout << "N=" << N << ", rings=" << R_rings << " (" << tris.size() << " tris): uncov = " << uncov << "\n";
      if (uncov == 0) {
        std::cout << "SUCCESS at N=" << N << ", rings=" << R_rings << "!\n";
        return 0;
      }
    }
  }
  return 0;
}
