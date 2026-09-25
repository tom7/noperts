#include <iostream>
#include <vector>
#include <cmath>
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
  vec3 dir_u0 = yocto::normalize(u0);

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << base_axes.size() << " hull support axes.\n";

  int zero_defect_count = 0;
  double best_dot = -1.0;
  int best_idx = -1;

  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ax = base_axes[i];
    if (ax.delta == BigRat(0)) {
      zero_defect_count++;
      vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
      double dot = yocto::dot(yocto::normalize(u), dir_u0);
      if (dot > best_dot) {
        best_dot = dot;
        best_idx = i;
      }
    }
  }

  std::cout << "Zero defect axes among 5000: " << zero_defect_count << "\n";
  std::cout << "Best dot among zero defect axes: " << best_dot
            << " (angle = " << (std::acos(best_dot) * 180 / M_PI) << " deg)\n";
  if (best_idx >= 0) {
    const auto &ax = base_axes[best_idx];
    std::cout << "Best zero-defect axis: B = " << ax.cert.B.ToString() << "\n";
    std::cout << "center = (" << ax.center.x.ToString() << ", " << ax.center.y.ToString() << ", " << ax.center.z.ToString() << ")\n";
  }

  return 0;
}
