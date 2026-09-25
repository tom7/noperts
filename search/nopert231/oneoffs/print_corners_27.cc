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
  vec3 A = get_pt(0.5 * psi_outer, phi1);
  vec3 B = get_pt(psi_outer, phi1);
  vec3 C = get_pt(psi_outer, phi2);
  vec3 D = get_pt(0.5 * psi_outer, phi2);

  auto best_dot = [&](vec3 p) {
    double m = -1e9;
    int best = -1;
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      double d = yocto::dot(p, v);
      if (d > m) { m = d; best = i; }
    }
    return std::pair<double, int>(m, best);
  };

  std::cout << "Corner A: max_dot = " << best_dot(A).first << " by " << best_dot(A).second << "\n";
  std::cout << "Corner B: max_dot = " << best_dot(B).first << " by " << best_dot(B).second << "\n";
  std::cout << "Corner C: max_dot = " << best_dot(C).first << " by " << best_dot(C).second << "\n";
  std::cout << "Corner D: max_dot = " << best_dot(D).first << " by " << best_dot(D).second << "\n";

  // Check how many axes cover pairs of corners:
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    bool oA = yocto::dot(A, v) >= c_core;
    bool oB = yocto::dot(B, v) >= c_core;
    bool oC = yocto::dot(C, v) >= c_core;
    bool oD = yocto::dot(D, v) >= c_core;
    if ((oA && oB && oC) || (oA && oC && oD) || (oB && oC && oD) || (oB && oD && oA)) {
      std::cout << "Axis " << i << " covers a triangle: "
                << "A=" << oA << " B=" << oB << " C=" << oC << " D=" << oD << "\n";
    }
  }

  return 0;
}
