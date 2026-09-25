#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct MyVec3 {
  double x, y, z;
  double dot(const MyVec3 &o) const { return x*o.x + y*o.y + z*o.z; }
  double norm() const { return std::sqrt(dot(*this)); }
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo contacts0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, contacts0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }

  MyVec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  double u0_len = u0.norm();

  struct Stat {
    int idx;
    double cos_theta;
    double len;
    double lambda;
    double w_len;
  };
  std::vector<Stat> stats;

  for (size_t i = 0; i < valid_axes.size(); i++) {
    MyVec3 v = {valid_axes[i].center.x.ToDouble(),
                valid_axes[i].center.y.ToDouble(),
                valid_axes[i].center.z.ToDouble()};
    double v_len = v.norm();
    if (v_len < 1e-6) continue;
    double cos_th = v.dot(u0) / (v_len * u0_len);
    double lambda = v.dot(u0) / (u0_len * u0_len);
    MyVec3 w = {v.x - lambda * u0.x, v.y - lambda * u0.y, v.z - lambda * u0.z};
    stats.push_back({(int)i, cos_th, v_len, lambda, w.norm()});
  }

  std::sort(stats.begin(), stats.end(), [](const Stat &a, const Stat &b) {
    return a.cos_theta > b.cos_theta;
  });

  std::cout << "Top 10 axes by cos(theta) with u0:\n";
  for (int i = 0; i < 10 && i < (int)stats.size(); i++) {
    std::cout << "Axis " << stats[i].idx << ": cos = " << stats[i].cos_theta
              << ", angle = " << (std::acos(stats[i].cos_theta) * 180.0 / M_PI) << " deg"
              << ", ||v|| = " << stats[i].len
              << ", lambda = " << stats[i].lambda
              << ", ||w|| = " << stats[i].w_len << "\n";
  }
  return 0;
}
