#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::vector<std::string> leaves = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  std::vector<std::vector<int>> comp_indices = {
    {5, 9, 12},
    {7, 23, 26},
    {5, 12, 14},
    {5, 12, 14},
    {7, 23, 26},
    {7, 23, 26}
  };

  for (size_t l = 0; l < leaves.size(); l++) {
    std::string path = leaves[l];
    TriangleQ tri = TriangleFromPath(path);
    auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);

    ContactInfo c0[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, 200, 14}
    };
    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
    vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
               center0.y.ToDouble() / ax0.B.ToDouble(),
               center0.z.ToDouble() / ax0.B.ToDouble()};

    std::vector<vec3> comp_dirs;
    for (int k = 0; k < 3; k++) {
      int idx = comp_indices[l][k];
      ContactInfo triple[3] = {
        axes500[idx].cert.contacts[0],
        axes500[idx].cert.contacts[1],
        axes500[idx].cert.contacts[2]
      };
      AxisCertificate ax;
      BigVecQ3 center;
      BigRat delta;
      Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0));
      comp_dirs.push_back({center.x.ToDouble() / ax.B.ToDouble(),
                           center.y.ToDouble() / ax.B.ToDouble(),
                           center.z.ToDouble() / ax.B.ToDouble()});
    }

    double c_cage = 0.003;
    double c_cone = 0.035;

    // Sample points in the gap: c_cage <= dot(a, u0) <= c_cone
    int N = 1000000;
    int gap_pts = 0;
    double min_comp_in_gap = 1e9;
    for (int i = 0; i < N; i++) {
      double z = 1.0 - (2.0 * i + 1.0) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
      double d0 = yocto::dot(a, u0);
      if (d0 >= c_cage && d0 <= c_cone) {
        gap_pts++;
        double m = -1e9;
        for (const auto &cd : comp_dirs) {
          double d = yocto::dot(a, cd);
          if (d > m) m = d;
        }
        if (m < min_comp_in_gap) min_comp_in_gap = m;
      }
    }

    std::cout << "Leaf " << path << ": points in gap = " << gap_pts
              << ", min complement in gap = " << min_comp_in_gap << "\n";
  }

  return 0;
}
