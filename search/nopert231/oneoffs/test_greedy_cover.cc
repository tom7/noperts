#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto all_axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Loaded " << all_axes.size() << " zero-defect axes.\n";

  std::vector<vec3> cand_u;
  for (const auto &ax : all_axes) {
    cand_u.push_back(vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                          ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                          ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  double c_cone = 0.024;
  double target_c = 0.001;

  // Sample sphere outside cone:
  int N = 50000;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) < c_cone) {
      pts.push_back(a);
    }
  }
  std::cout << "Sampled " << pts.size() << " points with a . u0 < " << c_cone << ".\n";

  // Greedy set cover
  std::vector<int> selected_axes;
  std::vector<bool> covered(pts.size(), false);
  int remaining = pts.size();

  while (remaining > 0) {
    int best_cand = -1;
    int best_cov = 0;

    for (size_t c = 0; c < cand_u.size(); c++) {
      int count = 0;
      for (size_t p = 0; p < pts.size(); p++) {
        if (!covered[p] && yocto::dot(pts[p], cand_u[c]) >= target_c) {
          count++;
        }
      }
      if (count > best_cov) {
        best_cov = count;
        best_cand = c;
      }
    }

    if (best_cand == -1 || best_cov == 0) {
      std::cout << "Failed to cover remaining " << remaining << " points!\n";
      break;
    }

    selected_axes.push_back(best_cand);
    for (size_t p = 0; p < pts.size(); p++) {
      if (!covered[p] && yocto::dot(pts[p], cand_u[best_cand]) >= target_c) {
        covered[p] = true;
        remaining--;
      }
    }

    std::cout << "Added axis " << best_cand << ", covered " << best_cov
              << " points, remaining = " << remaining << "\n";
  }

  std::cout << "Selected " << selected_axes.size() << " axes to cover entire complement!\n";
  return 0;
}
