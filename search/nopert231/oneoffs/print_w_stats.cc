#include <iostream>
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct MyVec3 {
  double x, y, z;
  double dot(const MyVec3 &o) const { return x*o.x + y*o.y + z*o.z; }
  double norm_sq() const { return dot(*this); }
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
  double u0_norm_sq = u0.norm_sq();

  double min_w = 1e9;
  double max_lambda = -1e9;
  int min_w_idx = -1;

  for (size_t i = 0; i < valid_axes.size(); i++) {
    MyVec3 v = {valid_axes[i].center.x.ToDouble(),
                valid_axes[i].center.y.ToDouble(),
                valid_axes[i].center.z.ToDouble()};
    double lambda = v.dot(u0) / u0_norm_sq;
    if (lambda <= 0) continue;
    MyVec3 w = {v.x - lambda * u0.x, v.y - lambda * u0.y, v.z - lambda * u0.z};
    double w_norm = std::sqrt(w.norm_sq());
    if (w_norm < min_w) {
      min_w = w_norm;
      min_w_idx = i;
    }
    if (lambda > max_lambda) max_lambda = lambda;
  }
  std::cout << "min_w = " << min_w << " (axis " << min_w_idx << "), max_lambda = " << max_lambda << "\n";
  std::cout << "For axis " << min_w_idx << ":\n";
  MyVec3 v = {valid_axes[min_w_idx].center.x.ToDouble(),
              valid_axes[min_w_idx].center.y.ToDouble(),
              valid_axes[min_w_idx].center.z.ToDouble()};
  double lambda = v.dot(u0) / u0_norm_sq;
  std::cout << "  lambda = " << lambda << ", ||v|| = " << std::sqrt(v.norm_sq()) << "\n";
  return 0;
}
