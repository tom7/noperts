#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  double X = 18.681, Y = -23.545;
  vec3 p = P0 + X * E1 + Y * E2;
  vec3 a = yocto::normalize(p);

  double box_delta = 234013.0 / 1000000000.0;

  struct Hit {
    int idx;
    double dot;
    double delta;
  };
  std::vector<Hit> hits;

  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() > box_delta) continue;
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(a, v);
    if (d > 0.0001) {
      hits.push_back({(int)i, d, axes[i].delta.ToDouble()});
    }
  }

  std::sort(hits.begin(), hits.end(), [](const Hit &h1, const Hit &h2) {
    return h1.dot > h2.dot;
  });

  std::cout << "Top hits for canyon point:\n";
  for (size_t i = 0; i < std::min((size_t)15, hits.size()); i++) {
    std::cout << "Axis " << hits[i].idx << ": dot=" << hits[i].dot
              << ", delta=" << hits[i].delta << "\n";
  }

  return 0;
}
