#include <iostream>
#include <vector>
#include <cmath>
#include <bitset>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Pt2 { double x, y; };

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
  double norm_u0_sq = yocto::dot(u0, u0);

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double c_cone = 0.017;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  std::vector<std::pair<int, int>> params;

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
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({cert, ctr, del});
          params.push_back({m1, m2});
        }
      }
    }
  }

  // Also include the best axis from hull support
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  for (const auto &ax : hull_axes) {
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
      params.push_back({-1, -1});
    }
  }

  std::cout << "Total candidate axes: " << valid_axes.size() << "\n";

  // Sample points on disk
  std::vector<Pt2> test_pts;
  for (double r = 0; r <= R; r += 1.0) {
    int num_ang = (r == 0 ? 1 : std::max(6, (int)(2.0 * M_PI * r)));
    for (int k = 0; k < num_ang; k++) {
      double th = k * 2.0 * M_PI / num_ang;
      test_pts.push_back({r * std::cos(th), r * std::sin(th)});
    }
  }
  std::cout << "Total test points: " << test_pts.size() << "\n";

  auto check_pt = [&](Pt2 pt, int a) {
    vec3 p = P0 + pt.x * E1 + pt.y * E2;
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= c_core * yocto::length(p);
  };

  // Build coverage matrix
  std::vector<std::vector<int>> pt_covered_by(test_pts.size());
  for (size_t a = 0; a < valid_axes.size(); a++) {
    for (size_t p = 0; p < test_pts.size(); p++) {
      if (check_pt(test_pts[p], a)) {
        pt_covered_by[p].push_back(a);
      }
    }
  }

  // Check if any point is uncovered
  int uncovered = 0;
  for (size_t p = 0; p < test_pts.size(); p++) {
    if (pt_covered_by[p].empty()) uncovered++;
  }
  std::cout << "Uncovered test points by ALL axes: " << uncovered << "\n";

  // Greedy set cover
  std::vector<bool> covered(test_pts.size(), false);
  int num_covered = 0;
  std::vector<int> chosen_axes;

  while (num_covered < (int)test_pts.size()) {
    int best_axis = -1;
    int best_new = 0;
    for (size_t a = 0; a < valid_axes.size(); a++) {
      int new_cov = 0;
      for (size_t p = 0; p < test_pts.size(); p++) {
        if (!covered[p] && check_pt(test_pts[p], a)) new_cov++;
      }
      if (new_cov > best_new) {
        best_new = new_cov;
        best_axis = a;
      }
    }
    if (best_new == 0) break;
    chosen_axes.push_back(best_axis);
    for (size_t p = 0; p < test_pts.size(); p++) {
      if (!covered[p] && check_pt(test_pts[p], best_axis)) {
        covered[p] = true;
        num_covered++;
      }
    }
    std::cout << "Picked axis " << best_axis << " (params: " << params[best_axis].first << ", "
              << params[best_axis].second << "), newly covered: " << best_new
              << ", total: " << num_covered << " / " << test_pts.size()
              << " (" << (100.0 * num_covered / test_pts.size()) << "%)\n";
  }

  std::cout << "Total axes needed for 100% point cover: " << chosen_axes.size() << "\n";
  return 0;
}
