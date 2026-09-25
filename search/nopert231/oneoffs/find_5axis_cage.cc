#include <iostream>
#include <vector>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  double delta = 0.000234013;
  double c = 0.001;
  double R = (7.0 / 4.0) * (c + delta);

  BigRat delta_q(234013, 1000000000);
  BigRat c_q(1, 1000);
  BigRat R_q = BigRat(7, 4) * (c_q + delta_q);

  BigVecQ3 oct[6] = {
    {R_q, BigRat(0), BigRat(0)}, {-R_q, BigRat(0), BigRat(0)},
    {BigRat(0), R_q, BigRat(0)}, {BigRat(0), -R_q, BigRat(0)},
    {BigRat(0), BigRat(0), R_q}, {BigRat(0), BigRat(0), -R_q}
  };

  std::vector<BigVecQ3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    all_v.push_back(axes[i].center);
  }

  // To contain all 6 octahedron vertices in the convex hull of a subset S of axes,
  // it is sufficient that each octahedron vertex oct[k] is contained in some tetrahedron
  // formed by 4 axes in S!
  //
  // Even better: let's pick 6 axes that strongly support the 6 coordinate directions!
  // For each of the 6 directions, pick the axis with the highest projection.
  vec3 dirs[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  std::vector<int> picked;
  for (int k = 0; k < 6; k++) {
    double max_d = -1e9;
    int best_i = -1;
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()};
      double d = yocto::dot(v, dirs[k]);
      if (d > max_d) {
        max_d = d;
        best_i = i;
      }
    }
    picked.push_back(best_i);
    std::cout << "Picked axis for dir " << k << ": " << best_i
              << " (vertex=" << axes[best_i].cert.contacts[0].vertex << ","
              << axes[best_i].cert.contacts[1].vertex << ","
              << axes[best_i].cert.contacts[2].vertex << ")\n";
  }

  // Now, for each of the 6 octahedron vertices, check if ANY 4 of the 6 picked axes
  // contain that vertex with positive barycentric coordinates!
  int combos[15][4];
  int ncombos = 0;
  for (int i = 0; i < 6; i++) {
    for (int j = i + 1; j < 6; j++) {
      for (int k = j + 1; k < 6; k++) {
        for (int l = k + 1; l < 6; l++) {
          combos[ncombos][0] = picked[i];
          combos[ncombos][1] = picked[j];
          combos[ncombos][2] = picked[k];
          combos[ncombos][3] = picked[l];
          ncombos++;
        }
      }
    }
  }

  std::cout << "Testing 15 tetrahedra from the 6 picked axes...\n";
  for (int o = 0; o < 6; o++) {
    bool found = false;
    BigRat best_min_l(-100);
    int best_combo = -1;
    for (int cb = 0; cb < ncombos; cb++) {
      BigVecQ3 v[4];
      for (int a = 0; a < 4; a++) v[a] = all_v[combos[cb][a]];
      BigVecQ3 d0 = v[0] - v[3];
      BigVecQ3 d1 = v[1] - v[3];
      BigVecQ3 d2 = v[2] - v[3];
      BigRat det = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, d2));
      if (det == BigRat(0)) continue;

      BigVecQ3 dp = oct[o] - v[3];
      BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(d1, d2)) / det;
      BigRat l1 = BigVecQ3::Dot(d0, BigVecQ3::Cross(dp, d2)) / det;
      BigRat l2 = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, dp)) / det;
      BigRat l3 = BigRat(1) - l0 - l1 - l2;

      BigRat min_l = l0;
      if (l1 < min_l) min_l = l1;
      if (l2 < min_l) min_l = l2;
      if (l3 < min_l) min_l = l3;

      if (min_l > best_min_l) {
        best_min_l = min_l;
        best_combo = cb;
      }
      if (min_l >= BigRat(0)) {
        found = true;
        std::cout << "Octahedron vertex " << o << " CONTAINED in combo " << cb << "! min_l = " << min_l.ToDouble() << "\n";
        break;
      }
    }
    if (!found) {
      std::cout << "Octahedron vertex " << o << " NOT contained in any of the 15 combos! Best min_l = "
                << best_min_l.ToDouble() << " in combo " << best_combo << "\n";
    }
  }

  return 0;
}
