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

  for (int num = 15; num <= 27; num++) {
    double c_cone = num / 1000.0;
    double cos_alpha = c_cone / norm_u0;
    double alpha = std::acos(cos_alpha);

    double min_dot = 1e9;
    double min_phi = -1;
    for (int step = 0; step < 1800; step++) {
      double phi = step * 2.0 * M_PI / 1800.0;
      vec3 p = yocto::normalize(std::cos(alpha) * u0 + std::sin(alpha) * (std::cos(phi) * ex + std::sin(phi) * ey));
      double max_d = -1e9;
      for (size_t a = 0; a < axes.size(); a++) {
        vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                      axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                      axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
        double d = yocto::dot(p, v);
        if (d > max_d) max_d = d;
      }
      if (max_d < min_dot) {
        min_dot = max_d;
        min_phi = phi * 180.0 / M_PI;
      }
    }
    std::cout << "c_cone = " << c_cone << " (alpha = " << alpha * 180 / M_PI << " deg): min_dot = " << min_dot << " at phi = " << min_phi << " deg\n";
  }

  return 0;
}
