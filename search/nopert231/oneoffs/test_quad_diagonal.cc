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
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  for (double psi_ratio : {0.5, 0.55, 0.6, 0.65}) {
    double psi_inner = psi_ratio * psi_outer;
    std::vector<vec3> ring1(N), ring2(N);
    for (int k = 0; k < N; k++) {
      double phi = k * 2.0 * M_PI / N;
      ring1[k] = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi) * ex + std::sin(phi) * ey));
      ring2[k] = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi) * ex + std::sin(phi) * ey));
    }

    int uncov_quads = 0;
    for (int k = 0; k < N; k++) {
      int next_k = (k + 1) % N;
      // Option 1: diagonal (ring1[k] -> ring2[next_k])
      bool opt1_t1 = false, opt1_t2 = false;
      for (size_t i = 0; i < all_v.size(); i++) {
        if (!opt1_t1 && yocto::dot(ring1[k], all_v[i]) >= c_core &&
            yocto::dot(ring2[k], all_v[i]) >= c_core &&
            yocto::dot(ring2[next_k], all_v[i]) >= c_core) opt1_t1 = true;
        if (!opt1_t2 && yocto::dot(ring1[k], all_v[i]) >= c_core &&
            yocto::dot(ring2[next_k], all_v[i]) >= c_core &&
            yocto::dot(ring1[next_k], all_v[i]) >= c_core) opt1_t2 = true;
      }
      bool opt1_ok = (opt1_t1 && opt1_t2);

      // Option 2: diagonal (ring2[k] -> ring1[next_k])
      bool opt2_t1 = false, opt2_t2 = false;
      for (size_t i = 0; i < all_v.size(); i++) {
        if (!opt2_t1 && yocto::dot(ring1[k], all_v[i]) >= c_core &&
            yocto::dot(ring2[k], all_v[i]) >= c_core &&
            yocto::dot(ring1[next_k], all_v[i]) >= c_core) opt2_t1 = true;
        if (!opt2_t2 && yocto::dot(ring2[k], all_v[i]) >= c_core &&
            yocto::dot(ring2[next_k], all_v[i]) >= c_core &&
            yocto::dot(ring1[next_k], all_v[i]) >= c_core) opt2_t2 = true;
      }
      bool opt2_ok = (opt2_t1 && opt2_t2);

      if (!opt1_ok && !opt2_ok) {
        uncov_quads++;
        std::cout << "Quad " << k << " cannot be covered with either diagonal! (ratio " << psi_ratio << ")\n";
      } else if (!opt1_ok && opt2_ok) {
        std::cout << "Quad " << k << " SAVED by Option 2! (ratio " << psi_ratio << ")\n";
      }
    }
    std::cout << "psi_ratio = " << psi_ratio << ": total uncov_quads = " << uncov_quads << "\n";
  }

  return 0;
}
