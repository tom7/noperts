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
  int N = 40;
  double tan_outer = std::tan(alpha) / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= 0.0003 && yocto::dot(p2, v) >= 0.0003 && yocto::dot(p3, v) >= 0.0003) {
        return (int)a;
      }
    }
    return -1;
  };

  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    vec3 qA = get_pt(0.5 * psi_outer, phi1);
    vec3 qB = get_pt(psi_outer, phi1);
    vec3 qC = get_pt(psi_outer, phi2);
    vec3 qD = get_pt(0.5 * psi_outer, phi2);
    bool d1 = (check_tri(qA, qB, qC) >= 0 && check_tri(qA, qC, qD) >= 0);
    bool d2 = (check_tri(qB, qC, qD) >= 0 && check_tri(qB, qD, qA) >= 0);
    if (!d1 && !d2) {
      std::cout << "Quad " << k << " failed! phi = [" << phi1 * 180 / M_PI << ", " << phi2 * 180 / M_PI << "]\n";
      // Find max dot product at each vertex:
      auto max_d = [&](vec3 p) {
        double md = -1e9;
        for (const auto& a : axes) {
          vec3 v = vec3{a.center.x.ToDouble() / a.cert.B.ToDouble(), a.center.y.ToDouble() / a.cert.B.ToDouble(), a.center.z.ToDouble() / a.cert.B.ToDouble()};
          md = std::max(md, (double)yocto::dot(p, v));
        }
        return md;
      };
      std::cout << "  max_d(A)=" << max_d(qA) << ", max_d(B)=" << max_d(qB) << ", max_d(C)=" << max_d(qC) << ", max_d(D)=" << max_d(qD) << "\n";
    }
  }
  return 0;
}
