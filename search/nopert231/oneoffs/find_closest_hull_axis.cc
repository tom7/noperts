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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Found " << hull_axes.size() << " hull support axes\n";

  double best_dot = -1.0;
  int best_idx = -1;

  for (size_t i = 0; i < hull_axes.size(); i++) {
    const auto &ax = hull_axes[i];
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    vec3 u_dir = yocto::normalize(u);
    double dot = yocto::dot(u0_dir, u_dir);
    if (dot > best_dot) {
      best_dot = dot;
      best_idx = i;
    }
  }

  if (best_idx >= 0) {
    double angle_deg = std::acos(std::clamp(best_dot, -1.0, 1.0)) * 180.0 / M_PI;
    std::cout << "Best hull axis idx " << best_idx << ": dot = " << best_dot
              << ", angle = " << angle_deg << " deg\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = hull_axes[best_idx].cert.contacts[m];
      std::cout << "  contact " << m << ": ["
                << c.edge_start << "->" << c.edge_finish << ", "
                << c.edge_start2 << "->" << c.edge_finish2 << ", mix " << c.mix
                << ", v " << c.vertex << "]\n";
    }
  }
  return 0;
}
