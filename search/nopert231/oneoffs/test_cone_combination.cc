#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

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
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (int m1 = 0; m1 <= 1000; m1 += 25) {
    for (int m2 = 0; m2 <= 1000; m2 += 25) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  for (const auto &ax : hull_axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }

  int chosen[4] = {4055, 157, 480, 0};
  vec3 v[4];
  for (int i = 0; i < 4; i++) {
    int a = chosen[i];
    double B = valid_axes[a].cert.B.ToDouble();
    v[i] = vec3{valid_axes[a].center.x.ToDouble() / B,
                valid_axes[a].center.y.ToDouble() / B,
                valid_axes[a].center.z.ToDouble() / B};
  }

  std::cout << "u0 = (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  for (int i = 0; i < 4; i++) {
    std::cout << "v[" << i << "] = (" << v[i].x << ", " << v[i].y << ", " << v[i].z << ")\n";
  }

  auto det3 = [](vec3 a, vec3 b, vec3 c) {
    return yocto::dot(a, yocto::cross(b, c));
  };

  for (int drop = 0; drop < 4; drop++) {
    int idx[3];
    int p = 0;
    for (int i = 0; i < 4; i++) if (i != drop) idx[p++] = i;
    vec3 c0 = v[idx[0]], c1 = v[idx[1]], c2 = v[idx[2]];
    double D = det3(c0, c1, c2);
    if (std::abs(D) > 1e-9) {
      double m0 = det3(u0, c1, c2) / D;
      double m1 = det3(c0, u0, c2) / D;
      double m2 = det3(c0, c1, u0) / D;
      std::cout << "Dropping " << drop << ": mu = (" << m0 << ", " << m1 << ", " << m2 << ")";
      if (m0 >= 0 && m1 >= 0 && m2 >= 0) {
        double sum_mu = m0 + m1 + m2;
        std::cout << " -> ALL POSITIVE! sum_mu = " << sum_mu
                  << ", c_cone / sum_mu = " << (0.017 / sum_mu) << "\n";
      } else {
        std::cout << " (has negative)\n";
      }
    }
  }

  return 0;
}
