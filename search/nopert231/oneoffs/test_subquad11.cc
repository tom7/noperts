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

  double c_cone = 0.027;
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
  double phi1 = k * 2.0 * M_PI / N;
  double phi2 = (k + 1) * 2.0 * M_PI / N;
  double psi1 = 0.5 * psi_outer;
  double psi2 = psi_outer;

  // Subquad (1, 1): psi in [0.75 * psi_outer, psi_outer], phi in [mid_phi, phi2]
  double p_lo = 0.75 * psi_outer;
  double p_hi = psi_outer;
  double f_lo = 0.5 * (phi1 + phi2);
  double f_hi = phi2;

  // Let's test subdividing subquad (1, 1) into m x n
  for (int m = 1; m <= 4; m++) {
    for (int n = 1; n <= 4; n++) {
      int fail = 0;
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          double pa = p_lo + (p_hi - p_lo) * i / m;
          double pb = p_lo + (p_hi - p_lo) * (i + 1) / m;
          double fa = f_lo + (f_hi - f_lo) * j / n;
          double fb = f_lo + (f_hi - f_lo) * (j + 1) / n;
          vec3 A = get_pt(pa, fa);
          vec3 B = get_pt(pb, fa);
          vec3 C = get_pt(pb, fb);
          vec3 D = get_pt(pa, fb);

          auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
            for (size_t a = 0; a < axes.size(); a++) {
              vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                            axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                            axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
              if (yocto::dot(p1, v) >= c_core && yocto::dot(p2, v) >= c_core && yocto::dot(p3, v) >= c_core) {
                return (int)a;
              }
            }
            return -1;
          };
          bool d1 = (check_tri(A, B, C) >= 0 && check_tri(A, C, D) >= 0);
          bool d2 = (check_tri(B, C, D) >= 0 && check_tri(B, D, A) >= 0);
          if (!d1 && !d2) fail++;
        }
      }
      std::cout << "m=" << m << " n=" << n << " -> fail=" << fail << "\n";
      if (fail == 0) goto done;
    }
  }
done:
  return 0;
}
