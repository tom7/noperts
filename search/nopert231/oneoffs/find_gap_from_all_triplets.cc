#include <iostream>
#include <iomanip>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  double box_delta = 234013.0 / 1000000000.0;

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double X = 18.7029, Y = -23.5236; // Gap point
  vec3 p = P0 + X * E1 + Y * E2;
  double norm_p = yocto::length(p);
  vec3 a_unit = p / norm_p;

  std::cout << "Target unit direction at gap: " << a_unit.x << ", " << a_unit.y << ", " << a_unit.z << "\n";
  std::cout << "Target dot threshold: " << box_delta << "\n";

  // Let's get all valid contacts for tri:
  // We can call FindAllHullSupportAxes with 20000 to get a large pool,
  // or directly inspect all axes returned by FindAllHullSupportAxes!
  auto axes = Tube229::FindAllHullSupportAxes(tri, 20000);
  std::cout << "Found " << axes.size() << " axes from FindAllHullSupportAxes.\n";

  double best_dot = -1.0;
  int best_idx = -1;

  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    double del = ax.delta.ToDouble();
    if (del > box_delta) continue;
    vec3 v = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    double dot_val = yocto::dot(a_unit, v);
    if (dot_val > best_dot) {
      best_dot = dot_val;
      best_idx = i;
    }
  }

  std::cout << "Best dot at gap from 20000 axes: " << best_dot << " (index " << best_idx << ")\n";
  if (best_idx >= 0) {
    const auto &ax = axes[best_idx];
    std::cout << "Best axis delta: " << ax.delta.ToDouble() << "\n";
    std::cout << "Contacts:\n";
    for (int k = 0; k < 3; k++) {
      const auto &c = ax.cert.contacts[k];
      std::cout << "  v=" << c.vertex << " mix=" << c.mix
                << " (" << c.edge_start << "->" << c.edge_finish
                << " & " << c.edge_start2 << "->" << c.edge_finish2 << ")\n";
    }
  }

  return 0;
}
