#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  std::vector<std::pair<double, int>> angles;
  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ax = base_axes[i];
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    vec3 u_dir = yocto::normalize(u);
    double dot = yocto::dot(u0_dir, u_dir);
    double angle_deg = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
    angles.push_back({angle_deg, (int)i});
  }

  std::sort(angles.begin(), angles.end());
  std::cout << "Top 10 closest zero-defect axes among 5000 to u0:\n";
  for (int i = 0; i < 10; i++) {
    std::cout << i << ": axis " << angles[i].second << " at " << angles[i].first << " degrees (dot = "
              << std::cos(angles[i].first * M_PI / 180.0) << ")\n";
  }

  return 0;
}
