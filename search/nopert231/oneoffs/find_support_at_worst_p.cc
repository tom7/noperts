#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0_raw = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.017;
  double cos_cap = c_cone / norm_u0;
  double alpha_cap = std::acos(cos_cap);
  double dphi = 2.0 * M_PI / 16.0;

  double worst_r = 0.985312;
  double worst_phi = 5.58614;
  vec3 pt = yocto::normalize(std::cos(worst_r) * u0 + std::sin(worst_r) * (std::cos(worst_phi) * k1 + std::sin(worst_phi) * k2));

  std::cout << "worst_p: (" << pt.x << ", " << pt.y << ", " << pt.z << ")\n";

  // Let's find which vertices of the polyhedron have maximal dot product with pt!
  // Wait, pt is an axis direction in the adversary frame!
  // The polyhedron has support function h(d) for d in R^3.
  // Here, an axis certificate gives an axis direction v.
  // We want an axis certificate whose direction v has dot(v, pt) > 0!
  // In FindAllHullSupportAxes, why didn't we find an axis with dot(v, pt) > 0?
  // Let's see: ALL axes in FindAllHullSupportAxes:
  // Did ANY axis have dot(v, pt) > 0, regardless of delta?
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);
  double max_dot_any = -1e9;
  int best_any_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double d = yocto::dot(pt, v);
    if (d > max_dot_any) {
      max_dot_any = d;
      best_any_idx = i;
    }
  }

  std::cout << "Max dot among ALL 50000 axes (regardless of delta): " << max_dot_any << "\n";
  std::cout << "Best axis idx: " << best_any_idx << ", delta: " << axes[best_any_idx].delta.ToDouble() << "\n";

  return 0;
}
