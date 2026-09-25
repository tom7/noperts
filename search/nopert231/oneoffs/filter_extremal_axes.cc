#include <iostream>
#include <vector>
#include <algorithm>
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
  std::cout << "Total axes: " << N << "\n";

  std::vector<vec3> u(N);
  for (int i = 0; i < N; i++) {
    u[i] = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
  }

  // Find max along many directions to get extremal axes
  std::vector<bool> is_extreme(N, false);
  int extreme_count = 0;

  for (int x = -5; x <= 5; x++) {
    for (int y = -5; y <= 5; y++) {
      for (int z = -5; z <= 5; z++) {
        if (x == 0 && y == 0 && z == 0) continue;
        vec3 dir = yocto::normalize(vec3{(double)x, (double)y, (double)z});
        double max_dot = -1e9;
        int best_idx = -1;
        for (int i = 0; i < N; i++) {
          double d = yocto::dot(u[i], dir);
          if (d > max_dot) {
            max_dot = d;
            best_idx = i;
          }
        }
        if (best_idx >= 0 && !is_extreme[best_idx]) {
          is_extreme[best_idx] = true;
          extreme_count++;
        }
      }
    }
  }

  std::cout << "Found " << extreme_count << " extremal axes\n";

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
  double box_c = 0.001;
  double c_cone = 0.040;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::vector<int> extreme_indices;
  for (int i = 0; i < N; i++) {
    if (is_extreme[i]) extreme_indices.push_back(i);
  }

  std::cout << "Testing triples among " << extreme_indices.size() << " axes...\n";
  double best_min_l = -1e9;
  int M = extreme_indices.size();

  for (int i = 0; i < M; i++) {
    int idx1 = extreme_indices[i];
    vec3 v1 = u[idx1];
    vec3 d1 = v1 - v0;
    for (int j = i + 1; j < M; j++) {
      int idx2 = extreme_indices[j];
      vec3 v2 = u[idx2];
      vec3 d2 = v2 - v0;
      vec3 c12 = yocto::cross(d1, d2);
      for (int k = j + 1; k < M; k++) {
        int idx3 = extreme_indices[k];
        vec3 v3 = u[idx3];
        vec3 d3 = v3 - v0;
        double det = yocto::dot(c12, d3);
        if (std::abs(det) < 1e-9) continue;

        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);

        double min_l = 1.0;
        for (int p_idx = 0; p_idx < 6; p_idx++) {
          vec3 dp = oct[p_idx] - v0;
          double l1 = yocto::dot(dp, c23) / det;
          if (l1 < 0) { min_l = std::min(min_l, l1); if (min_l < best_min_l) goto next_triple; }
          double l2 = yocto::dot(dp, c31) / det;
          if (l2 < 0) { min_l = std::min(min_l, l2); if (min_l < best_min_l) goto next_triple; }
          double l3 = yocto::dot(dp, c12) / det;
          if (l3 < 0) { min_l = std::min(min_l, l3); if (min_l < best_min_l) goto next_triple; }
          double l0 = 1.0 - l1 - l2 - l3;
          if (l0 < 0) { min_l = std::min(min_l, l0); if (min_l < best_min_l) goto next_triple; }
          min_l = std::min({min_l, l0, l1, l2, l3});
        }
        if (min_l > best_min_l) {
          best_min_l = min_l;
          std::cout << "New best_min_l = " << best_min_l << " with ("
                    << idx1 << ", " << idx2 << ", " << idx3 << ")\n";
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Found enclosing cage!\n";
            std::cout << "Cage indices: " << idx1 << ", " << idx2 << ", " << idx3 << "\n";
            return 0;
          }
        }
      next_triple:;
      }
    }
  }

  std::cout << "Finished search. Best min_l = " << best_min_l << "\n";
  return 0;
}
