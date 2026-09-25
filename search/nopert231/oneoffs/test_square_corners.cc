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

  double c_cone = 0.020;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0005;

  std::cout << "alpha = " << alpha * 180.0 / M_PI << " deg\n";

  // Check corner of square: tan(psi) = sqrt(2) * tan(alpha)
  double tan_corner = std::sqrt(2.0) * std::tan(alpha);
  double psi_corner = std::atan(tan_corner);
  std::cout << "psi_corner = " << psi_corner * 180.0 / M_PI << " deg\n";

  for (double phi : {M_PI / 4, 3 * M_PI / 4, 5 * M_PI / 4, 7 * M_PI / 4}) {
    vec3 p = yocto::normalize(std::cos(psi_corner) * u0 + std::sin(psi_corner) * (std::cos(phi) * ex + std::sin(phi) * ey));
    double best_dot = -1.0;
    int best_a = -1;
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      double d = yocto::dot(p, v);
      if (d > best_dot) { best_dot = d; best_a = a; }
    }
    std::cout << "phi=" << phi * 180.0 / M_PI << " deg: best_dot=" << best_dot << " (axis " << best_a << ")\n";
  }
  return 0;
}
