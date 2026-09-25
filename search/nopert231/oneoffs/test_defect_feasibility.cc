#include <iostream>
#include <iomanip>
#include <vector>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string p0 = "031213002112122012120";
  std::string p1 = "031213002112122012121";

  TreeNode *n0 = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p0) { n0 = node; return; }
    if (p0.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find(find, root.get());
  if (!n0 || !n0->direct_cert) {
    std::cout << "Could not find s0 cert\n";
    return 1;
  }

  TriangleQ tri1 = TriangleFromPath(p1);
  vec3 tri_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()},
  };

  std::cout << "Testing sibling axes on uncertified leaf " << p1 << ":\n";

  for (int a = 0; a < 4; a++) {
    const auto &axis = n0->direct_cert->axes[a];
    std::cout << "\nAxis " << a << ":\n";

    vec3 c_edges[3];
    double max_axis_support_err = 0.0;
    int worst_vertex = -1;

    for (int m = 0; m < 3; m++) {
      const auto &c = axis.contacts[m];
      c_edges[m] = Tube229::GetDoubleEdge(c);
      int sel = c.vertex;
      for (int k = 0; k < NUM_VERTICES; k++) {
        bool tie = (k == sel) ||
                   (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                   (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
        if (tie) continue;
        vec3 delta = Vertex(k) - Vertex(sel);
        vec3 coeff = yocto::cross(c_edges[m], delta);
        double u = std::max({yocto::dot(tri_f[0], coeff), yocto::dot(tri_f[1], coeff), yocto::dot(tri_f[2], coeff)});
        if (u > max_axis_support_err) {
          max_axis_support_err = u;
          worst_vertex = k;
        }
      }
    }
    std::cout << "  Max support error: " << std::scientific << max_axis_support_err;
    if (max_axis_support_err > 0) {
      std::cout << " (violator: v" << worst_vertex << ")";
    }
    std::cout << "\n";

    vec3 weight_coeffs[3] = {
      yocto::cross(c_edges[1], c_edges[2]),
      yocto::cross(c_edges[2], c_edges[0]),
      yocto::cross(c_edges[0], c_edges[1])
    };
    bool weights_positive = true;
    for (int m = 0; m < 3; m++) {
      double w0 = yocto::dot(tri_f[0], weight_coeffs[m]);
      double w1 = yocto::dot(tri_f[1], weight_coeffs[m]);
      double w2 = yocto::dot(tri_f[2], weight_coeffs[m]);
      if (std::min({w0, w1, w2}) <= 0) weights_positive = false;
    }
    std::cout << "  Weights positive over entire triangle: " << (weights_positive ? "YES" : "NO") << "\n";
  }

  return 0;
}
