#include <iostream>
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  auto root = LoadTreeJson("ruperts/.artifacts/nopert229/tree_0.json", false, "ruperts/.artifacts/nopert229");
  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find_node = [&](auto &self, TreeNode *n) -> void {
    if (!n || n0) return;
    if (n->path == p0) { n0 = n; return; }
    if (p0.starts_with(n->path)) {
      for (auto &c : n->children) self(self, c.get());
    }
  };
  find_node(find_node, root.get());
  const auto &cert = *n0->direct_cert;

  Tube229::CandidateTriple cand[4];
  for (int a = 0; a < 4; a++) {
    Tube229::DoubleCheckAxis(tri1, cert.axes[a].contacts, &cand[a], 1e-8);
  }

  vec3 u0 = cand[0].normalized_a;
  vec3 u1 = cand[1].normalized_a;
  vec3 u2 = cand[2].normalized_a;
  vec3 u3 = cand[3].normalized_a;

  std::cout << std::setprecision(10);
  std::cout << "u0 = (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  std::cout << "u1 = (" << u1.x << ", " << u1.y << ", " << u1.z << ")\n";
  std::cout << "u2 = (" << u2.x << ", " << u2.y << ", " << u2.z << ")\n";
  std::cout << "u3 = (" << u3.x << ", " << u3.y << ", " << u3.z << ")\n";

  // Dense sphere sampling: find min_{||omega||=1, dot(omega, u0) <= c_cone} max_{j in {1,2,3}} dot(omega, u_j)
  for (double c_cone : {0.99, 0.95, 0.90, 0.80, 0.50, 0.0}) {
    double min_cover = 1.0;
    vec3 worst_w;
    int N = 2000;
    for (int i = 0; i < N; i++) {
      double z = -1.0 + 2.0 * (i + 0.5) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi_step = 2.0 * M_PI / (int(N * r) + 1);
      for (double phi = 0; phi < 2.0 * M_PI; phi += phi_step) {
        vec3 w = {r * std::cos(phi), r * std::sin(phi), z};
        w = yocto::normalize(w);
        if (yocto::dot(w, u0) > c_cone) continue;
        double max_dot = std::max({yocto::dot(w, u1), yocto::dot(w, u2), yocto::dot(w, u3)});
        if (max_dot < min_cover) {
          min_cover = max_dot;
          worst_w = w;
        }
      }
    }
    std::cout << "c_cone = " << c_cone << " => min cover of {u1, u2, u3} = " << min_cover
              << " at worst w = (" << worst_w.x << ", " << worst_w.y << ", " << worst_w.z << ")"
              << " dot(w, u0) = " << yocto::dot(worst_w, u0) << "\n";
  }

  return 0;
}
