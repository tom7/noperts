#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo new_c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {8, 9, 9, 10, 0, 9}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, new_c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::vector<vec3> p;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      p.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                   ctr.y.ToDouble() / cert.B.ToDouble(),
                   ctr.z.ToDouble() / cert.B.ToDouble()});
    }
  }

  vec3 target_ray = -u0;
  int count = 0;
  for (size_t i = 0; i < p.size(); i++) {
    for (size_t j = i + 1; j < p.size(); j++) {
      for (size_t k = j + 1; k < p.size(); k++) {
        double d = Det3(p[i], p[j], p[k]);
        if (std::abs(d) < 1e-12) continue;
        double a = Det3(target_ray, p[j], p[k]) / d;
        double b = Det3(p[i], target_ray, p[k]) / d;
        double c = Det3(p[i], p[j], target_ray) / d;
        if (a > 0 && b > 0 && c > 0) {
          count++;
        }
      }
    }
  }
  std::cout << "Triples containing -u0 in their conical hull: " << count << "\n";
  return 0;
}
