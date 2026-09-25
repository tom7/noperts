#include <iostream>
#include <vector>
#include <map>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string p1 = "031213002112122012121";
  TreeNode *n1 = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p1) { n1 = node; return; }
    if (p1.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find(find, root.get());

  TriangleQ tri1 = n1->GetTriangle();
  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  std::vector<int> fine_mixes = {0, 1, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 999, 1000};
  std::vector<ContactInfo> raw_contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);

  std::map<int, int> valid_v_counts;
  std::map<int, int> raw_v_counts;

  for (const auto &c : raw_contacts) {
    raw_v_counts[c.vertex]++;
    vec3 edge = Tube229::GetDoubleEdge(c);
    bool valid = true;
    for (int k = 0; k < 20; k++) {
      bool tie = (k == c.vertex) ||
                 (c.mix == 1000 && c.vertex == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && c.vertex == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 v_k = {Tube229::VertexQ(k).x.ToDouble(), Tube229::VertexQ(k).y.ToDouble(), Tube229::VertexQ(k).z.ToDouble()};
      vec3 v_sel = {Tube229::VertexQ(c.vertex).x.ToDouble(), Tube229::VertexQ(c.vertex).y.ToDouble(), Tube229::VertexQ(c.vertex).z.ToDouble()};
      vec3 delta = v_k - v_sel;
      vec3 coeff = yocto::cross(edge, delta);
      for (int corner = 0; corner < 3; corner++) {
        if (yocto::dot(tri1_f[corner], coeff) > 2e-14) {
          valid = false;
          break;
        }
      }
      if (!valid) break;
    }
    if (valid) valid_v_counts[c.vertex]++;
  }

  std::cout << "Raw vs Valid silhouette contacts by vertex on tri1:\n";
  for (int v = 0; v < 20; v++) {
    std::cout << "  Vertex " << v << ": raw=" << raw_v_counts[v] << ", valid=" << valid_v_counts[v] << "\n";
  }

  return 0;
}
