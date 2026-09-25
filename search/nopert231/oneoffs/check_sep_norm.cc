#include <iostream>
#include <vector>
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
  std::vector<int> fine_mixes;
  for (int m = 0; m <= 1000; m += 25) fine_mixes.push_back(m);
  std::vector<ContactInfo> raw_contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);

  std::vector<ContactInfo> valid_contacts;
  for (const auto &c : raw_contacts) {
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
    if (valid) valid_contacts.push_back(c);
  }

  vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
  std::cout << "Valid contacts count: " << valid_contacts.size() << "\n";

  int pos_dot = 0, neg_dot = 0;
  double min_dot = 1e30, max_dot = -1e30;
  for (const auto &c : valid_contacts) {
    vec3 edge = Tube229::GetDoubleEdge(c);
    vec3 v_sel = {Tube229::VertexQ(c.vertex).x.ToDouble(), Tube229::VertexQ(c.vertex).y.ToDouble(), Tube229::VertexQ(c.vertex).z.ToDouble()};
    vec3 lift = yocto::cross(centroid, edge);
    vec3 term = yocto::cross(v_sel, lift);
    double d = yocto::dot(term, sep_norm);
    if (d > 0) pos_dot++;
    else neg_dot++;
    min_dot = std::min(min_dot, d);
    max_dot = std::max(max_dot, d);
  }

  std::cout << "\nTop negative contacts (opposing sep_norm):\n";
  struct ScoredC {
    double d;
    ContactInfo c;
  };
  std::vector<ScoredC> scored_c;
  for (const auto &c : valid_contacts) {
    vec3 edge = Tube229::GetDoubleEdge(c);
    vec3 v_sel = {Tube229::VertexQ(c.vertex).x.ToDouble(), Tube229::VertexQ(c.vertex).y.ToDouble(), Tube229::VertexQ(c.vertex).z.ToDouble()};
    vec3 lift = yocto::cross(centroid, edge);
    vec3 term = yocto::cross(v_sel, lift);
    double d = yocto::dot(term, sep_norm);
    if (d < 0) scored_c.push_back({d, c});
  }
  std::sort(scored_c.begin(), scored_c.end(), [](const ScoredC &a, const ScoredC &b) {
    return a.d < b.d;
  });

  for (size_t i = 0; i < std::min((size_t)15, scored_c.size()); i++) {
    const auto &sc = scored_c[i];
    std::cout << "  d=" << sc.d << " vertex=" << sc.c.vertex
              << " edge=(" << sc.c.edge_start << "->" << sc.c.edge_finish
              << ", " << sc.c.edge_start2 << "->" << sc.c.edge_finish2
              << ") mix=" << sc.c.mix << "\n";
  }

  return 0;
}
