#include <iostream>
#include <vector>
#include <iomanip>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // We want to see if 4 pure zero-defect axes contain the octahedron of radius:
  // R = (7/4) * c_core
  // with c_core = 3/10000 = 0.0003!
  BigRat c_core(3, 10000);
  BigRat R = BigRat(7, 4) * c_core; // 21 / 40000 = 0.000525
  std::cout << "R_core = " << R.ToDouble() << "\n";

  BigVecQ3 oct[6] = {
    {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
  };

  // The 4 axes from find_minimal_flock_c0: {3054, 22, 3066, 3063}
  // Let's check these 4 axes first!
  std::vector<int> quad = {3054, 22, 3066, 3063};
  BigVecQ3 v[4];
  for (int a = 0; a < 4; a++) {
    v[a] = axes[quad[a]].center; // note: center = (approxCenter / B) * B? No, axes[i].center is approxNormalizedCenter!
    // Let's check: in Tube229, axes[i].center is BigVecQ3.
    // What is toR3 (approxNormalizedCenter)? It's center / 1.
  }

  BigVecQ3 d0 = v[0] - v[3];
  BigVecQ3 d1 = v[1] - v[3];
  BigVecQ3 d2 = v[2] - v[3];
  BigRat det = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, d2));
  std::cout << "det = " << det.ToDouble() << "\n";

  BigRat min_l(100);
  for (int o = 0; o < 6; o++) {
    BigVecQ3 dp = oct[o] - v[3];
    BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(d1, d2)) / det;
    BigRat l1 = BigVecQ3::Dot(d0, BigVecQ3::Cross(dp, d2)) / det;
    BigRat l2 = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, dp)) / det;
    BigRat l3 = BigRat(1) - l0 - l1 - l2;
    std::cout << "Oct " << o << ": " << l0.ToDouble() << ", " << l1.ToDouble()
              << ", " << l2.ToDouble() << ", " << l3.ToDouble() << "\n";
    if (l0 < min_l) min_l = l0;
    if (l1 < min_l) min_l = l1;
    if (l2 < min_l) min_l = l2;
    if (l3 < min_l) min_l = l3;
  }
  std::cout << "min_l for {3054, 22, 3066, 3063}: " << min_l.ToDouble() << "\n";

  // If not this specific 4-tuple, search across the top zero-defect axes for a 4-tuple that contains oct!
  if (min_l < BigRat(0)) {
    std::cout << "Searching across zero-defect axes...\n";
    // Search top 100 zero-defect axes
    std::vector<int> zd_axes;
    for (size_t i = 0; i < axes.size() && zd_axes.size() < 80; i++) {
      zd_axes.push_back(i);
    }
    BigRat best_min_l(-100);
    int best_comb[4] = {-1, -1, -1, -1};

    for (size_t i0 = 0; i0 < zd_axes.size(); i0++) {
      for (size_t i1 = i0 + 1; i1 < zd_axes.size(); i1++) {
        for (size_t i2 = i1 + 1; i2 < zd_axes.size(); i2++) {
          for (size_t i3 = i2 + 1; i3 < zd_axes.size(); i3++) {
            BigVecQ3 cur_v[4] = {axes[zd_axes[i0]].center, axes[zd_axes[i1]].center,
                                 axes[zd_axes[i2]].center, axes[zd_axes[i3]].center};
            BigVecQ3 cur_d0 = cur_v[0] - cur_v[3];
            BigVecQ3 cur_d1 = cur_v[1] - cur_v[3];
            BigVecQ3 cur_d2 = cur_v[2] - cur_v[3];
            BigRat cur_det = BigVecQ3::Dot(cur_d0, BigVecQ3::Cross(cur_d1, cur_d2));
            if (cur_det == BigRat(0)) continue;

            BigRat cur_min(100);
            for (int o = 0; o < 6; o++) {
              BigVecQ3 dp = oct[o] - cur_v[3];
              BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(cur_d1, cur_d2)) / cur_det;
              BigRat l1 = BigVecQ3::Dot(cur_d0, BigVecQ3::Cross(dp, cur_d2)) / cur_det;
              BigRat l2 = BigVecQ3::Dot(cur_d0, BigVecQ3::Cross(cur_d1, dp)) / cur_det;
              BigRat l3 = BigRat(1) - l0 - l1 - l2;
              if (l0 < cur_min) cur_min = l0;
              if (l1 < cur_min) cur_min = l1;
              if (l2 < cur_min) cur_min = l2;
              if (l3 < cur_min) cur_min = l3;
            }
            if (cur_min > best_min_l) {
              best_min_l = cur_min;
              best_comb[0] = zd_axes[i0];
              best_comb[1] = zd_axes[i1];
              best_comb[2] = zd_axes[i2];
              best_comb[3] = zd_axes[i3];
              if (best_min_l >= BigRat(0)) {
                std::cout << "FOUND 4-TUPLE THAT CONTAINS OCTAHEDRON! min_l = " << best_min_l.ToDouble() << "\n";
                std::cout << "Axes: " << best_comb[0] << ", " << best_comb[1] << ", "
                          << best_comb[2] << ", " << best_comb[3] << "\n";
                goto done;
              }
            }
          }
        }
      }
    }
  done:
    std::cout << "Best min_l: " << best_min_l.ToDouble() << "\n";
  }

  return 0;
}
