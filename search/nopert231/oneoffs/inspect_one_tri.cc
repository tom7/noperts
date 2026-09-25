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
  double c_core = 0.0001;

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  int N = 16;
  int R_rings = 2;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  std::vector<std::vector<vec3>> rings(R_rings + 1, std::vector<vec3>(N));
  for (int r = 1; r <= R_rings; r++) {
    double psi = (double)r / R_rings * psi_outer;
    for (int k = 0; k < N; k++) {
      double phi = k * 2.0 * M_PI / N;
      rings[r][k] = yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
    }
  }

  struct TriInfo {
    int id;
    std::string desc;
    vec3 A, B, C;
  };
  std::vector<TriInfo> tris;
  vec3 apex = u0;
  for (int k = 0; k < N; k++) {
    tris.push_back({(int)tris.size(), "apex_" + std::to_string(k), apex, rings[1][k], rings[1][(k + 1) % N]});
  }
  for (int k = 0; k < N; k++) {
    int next_k = (k + 1) % N;
    tris.push_back({(int)tris.size(), "outerA_" + std::to_string(k), rings[1][k], rings[2][k], rings[2][next_k]});
    tris.push_back({(int)tris.size(), "outerB_" + std::to_string(k), rings[1][k], rings[2][next_k], rings[1][next_k]});
  }

  for (size_t t = 0; t < tris.size(); t++) {
    double best_min = -1e9;
    int best_ax = -1;
    for (size_t i = 0; i < all_v.size(); i++) {
      double d = std::min({yocto::dot(tris[t].A, all_v[i]),
                           yocto::dot(tris[t].B, all_v[i]),
                           yocto::dot(tris[t].C, all_v[i])});
      if (d > best_min) {
        best_min = d;
        best_ax = i;
      }
    }
    if (best_min < c_core) {
      std::cout << "Triangle " << tris[t].id << " (" << tris[t].desc << ") UNCOVERED: best_min = "
                << best_min << " with axis " << best_ax << "\n";
    }
  }

  return 0;
}
