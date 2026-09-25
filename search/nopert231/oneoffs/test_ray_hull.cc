#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int N = base_axes.size();

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.000255;
  double c_cone = 0.0278;
  vec3 v0 = u0 * ((box_c + delta) / c_cone);

  std::vector<vec3> rays(N);
  for (int i = 0; i < N; i++) {
    vec3 u = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
              base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
              base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
    rays[i] = yocto::normalize(u - v0);
  }

  // Find extremal rays by sampling 20,000 random directions
  std::vector<int> extremal;
  for (int step = 0; step < 20000; step++) {
    double z = -1.0 + 2.0 * step / 20000.0;
    double phi = 3.1415926535 * (1.0 + std::sqrt(5.0)) * step;
    double r = std::sqrt(std::max(0.0, 1.0 - z*z));
    vec3 dir = {r * std::cos(phi), r * std::sin(phi), z};
    double best_d = -1e9;
    int best_idx = -1;
    for (int i = 0; i < N; i++) {
      double d = yocto::dot(rays[i], dir);
      if (d > best_d) { best_d = d; best_idx = i; }
    }
    if (best_idx >= 0) extremal.push_back(best_idx);
  }
  std::sort(extremal.begin(), extremal.end());
  extremal.erase(std::unique(extremal.begin(), extremal.end()), extremal.end());
  std::cout << "Found " << extremal.size() << " extremal rays from v0 among " << N << " axes.\n";

  // Now test all triples among these extremal rays!
  int M = extremal.size();
  std::cout << "Testing " << (M * (M-1) * (M-2) / 6) << " triples...\n";

  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::vector<vec3> u(N);
  for (int i = 0; i < N; i++) {
    u[i] = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
  }

  double best_min_l = -1e9;
  int b1 = -1, b2 = -1, b3 = -1;
  for (int i = 0; i < M; i++) {
    int idx1 = extremal[i];
    vec3 d1 = u[idx1] - v0;
    for (int j = i + 1; j < M; j++) {
      int idx2 = extremal[j];
      vec3 d2 = u[idx2] - v0;
      vec3 c12 = yocto::cross(d1, d2);
      for (int k = j + 1; k < M; k++) {
        int idx3 = extremal[k];
        vec3 d3 = u[idx3] - v0;
        double det = yocto::dot(c12, d3);
        if (std::abs(det) < 1e-10) continue;

        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);

        double min_l = 1.0;
        for (int p = 0; p < 6; p++) {
          vec3 dp = oct[p] - v0;
          double l1 = yocto::dot(dp, c23) / det;
          if (l1 < 0) { min_l = std::min(min_l, l1); if (min_l < best_min_l) goto next_k; }
          double l2 = yocto::dot(dp, c31) / det;
          if (l2 < 0) { min_l = std::min(min_l, l2); if (min_l < best_min_l) goto next_k; }
          double l3 = yocto::dot(dp, c12) / det;
          if (l3 < 0) { min_l = std::min(min_l, l3); if (min_l < best_min_l) goto next_k; }
          double l0 = 1.0 - l1 - l2 - l3;
          if (l0 < 0) { min_l = std::min(min_l, l0); if (min_l < best_min_l) goto next_k; }
          min_l = std::min({min_l, l0, l1, l2, l3});
        }
        if (min_l > best_min_l) {
          best_min_l = min_l;
          b1 = idx1; b2 = idx2; b3 = idx3;
          std::cout << "New best_min_l = " << best_min_l << " with ("
                    << b1 << ", " << b2 << ", " << b3 << ")\n";
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Found positive cage without even tuning mixes!\n";
            return 0;
          }
        }
      next_k:;
      }
    }
  }

  std::cout << "Final best: " << best_min_l << " with (" << b1 << ", " << b2 << ", " << b3 << ")\n";
  return 0;
}
