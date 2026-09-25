#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

static double SphericalArea(vec3 a, vec3 b, vec3 c) {
  a = a / yocto::length(a);
  b = b / yocto::length(b);
  c = c / yocto::length(c);
  double num = std::abs(yocto::dot(a, yocto::cross(b, c)));
  double den = 1.0 + yocto::dot(a, b) + yocto::dot(b, c) + yocto::dot(c, a);
  return 2.0 * std::atan2(num, den);
}

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree_0.json...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  TriangleQ root_tri = root->GetTriangle();
  vec3 r0 = vec3{root_tri.corners[0].x.ToDouble(), root_tri.corners[0].y.ToDouble(), root_tri.corners[0].z.ToDouble()};
  vec3 r1 = vec3{root_tri.corners[1].x.ToDouble(), root_tri.corners[1].y.ToDouble(), root_tri.corners[1].z.ToDouble()};
  vec3 r2 = vec3{root_tri.corners[2].x.ToDouble(), root_tri.corners[2].y.ToDouble(), root_tri.corners[2].z.ToDouble()};
  double total_area = SphericalArea(r0, r1, r2);

  double covered_area = 0.0;
  int covered_nodes = 0;
  int uncertified_leaves = 0;

  auto traverse = [&](auto &self, const TreeNode* n) -> bool {
    if (n->direct_cert.has_value() && BigRat::Sign(n->direct_cert->r) > 0) {
      TriangleQ tri = n->GetTriangle();
      vec3 v0 = vec3{tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()};
      vec3 v1 = vec3{tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()};
      vec3 v2 = vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()};
      covered_area += SphericalArea(v0, v1, v2);
      covered_nodes++;
      return true;
    }
    if (n->children.size() == 4) {
      bool all_covered = true;
      for (int i = 0; i < 4; i++) {
        if (!self(self, n->children[i].get())) {
          all_covered = false;
        }
      }
      return all_covered;
    }
    uncertified_leaves++;
    return false;
  };

  traverse(traverse, root.get());

  std::cout << "Coverage statistics for tree_0:\n"
            << "  Total spherical area: " << total_area << " steradians\n"
            << "  Covered spherical area: " << covered_area << " steradians\n"
            << "  Coverage percentage: " << std::fixed << std::setprecision(6) << (covered_area * 100.0 / total_area) << "%\n"
            << "  Uncovered area: " << (total_area - covered_area) << " steradians ("
            << ((total_area - covered_area) * 100.0 / total_area) << "%)\n"
            << "  Covered nodes: " << covered_nodes << "\n"
            << "  Uncertified leaves: " << uncertified_leaves << "\n";

  return 0;
}
