#include <iostream>
#include <vector>
#include <cmath>
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
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.z.ToDouble() / ax0.B.ToDouble()});
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0003;

  int N = 20;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  int k = 17;
  double psi1 = 0.5 * psi_outer;
  double psi2 = psi_outer;
  double phi1 = k * 2.0 * M_PI / N;
  double phi2 = (k + 1) * 2.0 * M_PI / N;

  int sub_r = 2;
  int sub_phi = 2;
  for (int ir = 0; ir < sub_r; ir++) {
    for (int ip = 0; ip < sub_phi; ip++) {
      double p_psi1 = psi1 + (psi2 - psi1) * (double)ir / sub_r;
      double p_psi2 = psi1 + (psi2 - psi1) * (double)(ir + 1) / sub_r;
      double p_phi1 = phi1 + (phi2 - phi1) * (double)ip / sub_phi;
      double p_phi2 = phi1 + (phi2 - phi1) * (double)(ip + 1) / sub_phi;

      vec3 A = get_pt(p_psi1, p_phi1);
      vec3 B = get_pt(p_psi2, p_phi1);
      vec3 C = get_pt(p_psi2, p_phi2);
      vec3 D = get_pt(p_psi1, p_phi2);

      auto max_corner_dot = [&](vec3 p) {
        double md = -1e9;
        int bi = -1;
        for (size_t i = 0; i < axes.size(); i++) {
          vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                        axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                        axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
          double d = yocto::dot(p, v);
          if (d > md) { md = d; bi = i; }
        }
        return std::pair<double, int>{md, bi};
      };

      std::cout << "Sub-quad ir=" << ir << " ip=" << ip << ":\n";
      auto mA = max_corner_dot(A);
      auto mB = max_corner_dot(B);
      auto mC = max_corner_dot(C);
      auto mD = max_corner_dot(D);
      std::cout << "  A: max=" << mA.first << " by " << mA.second << "\n";
      std::cout << "  B: max=" << mB.first << " by " << mB.second << "\n";
      std::cout << "  C: max=" << mC.first << " by " << mC.second << "\n";
      std::cout << "  D: max=" << mD.first << " by " << mD.second << "\n";

      // Check common axes covering subsets:
      std::vector<int> cov_ABC, cov_ACD, cov_BCD, cov_BDA;
      for (size_t i = 0; i < axes.size(); i++) {
        vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                      axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                      axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
        double dA = yocto::dot(A, v), dB = yocto::dot(B, v), dC = yocto::dot(C, v), dD = yocto::dot(D, v);
        if (dA >= c_core && dB >= c_core && dC >= c_core) cov_ABC.push_back(i);
        if (dA >= c_core && dC >= c_core && dD >= c_core) cov_ACD.push_back(i);
        if (dB >= c_core && dC >= c_core && dD >= c_core) cov_BCD.push_back(i);
        if (dB >= c_core && dD >= c_core && dA >= c_core) cov_BDA.push_back(i);
      }
      std::cout << "  cov_ABC=" << cov_ABC.size() << " cov_ACD=" << cov_ACD.size()
                << " cov_BCD=" << cov_BCD.size() << " cov_BDA=" << cov_BDA.size() << "\n";
    }
  }

  return 0;
}
