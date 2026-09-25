#include <iostream>
#include <iomanip>
#include <vector>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  BigVecQ3 c2 = tri1.corners[2];
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

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
  const auto &sib_cert = *n0->direct_cert;

  vec3 p1 = {0.0337938, 0.0283891, 0.0447476};
  vec3 p2 = {0.0704934, -0.00618611, 0.040156};
  vec3 p3 = {-0.0722811, -0.00727161, -0.0259227};

  vec3 n = {0.362954, 0.490466, -0.79228};
  double d = -0.00926315;

  std::vector<int> fine_mixes = {0, 1000};
  vec3 c2_f = {c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()};
  std::vector<ContactInfo> raw = Tube229::GenerateSilhouetteContacts(c2_f, fine_mixes);
  std::cout << "Raw contacts: " << raw.size() << "\n";

  std::vector<ContactInfo> valid;
  for (const auto &c : raw) {
    ContactInfo dummy[3] = {c, c, c};
    // Check if single contact is valid:
    vec3 edge = Tube229::GetDoubleEdge(c);
    bool ok = true;
    for (int k = 0; k < 20; k++) {
      if (k == c.vertex) continue;
      vec3 delta = {Tube229::VertexQ(k).x.ToDouble() - Tube229::VertexQ(c.vertex).x.ToDouble(),
                    Tube229::VertexQ(k).y.ToDouble() - Tube229::VertexQ(c.vertex).y.ToDouble(),
                    Tube229::VertexQ(k).z.ToDouble() - Tube229::VertexQ(c.vertex).z.ToDouble()};
      if (yocto::dot(c2_f, yocto::cross(edge, delta)) > 1e-12) {
        ok = false;
        break;
      }
    }
    if (ok) valid.push_back(c);
  }
  std::cout << "Valid contacts on Corner 2: " << valid.size() << "\n";

  for (size_t i = 0; i < valid.size(); i++) {
    for (size_t j = i + 1; j < valid.size(); j++) {
      for (size_t k = j + 1; k < valid.size(); k++) {
        ContactInfo triple[3] = {valid[i], valid[j], valid[k]};
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri_c2, triple, &cand, 1e-12)) {
          vec3 p0_v = cand.normalized_a;
          vec3 a = p0_v - p3;
          vec3 b = p1 - p3;
          vec3 c_v = p2 - p3;
          double det = yocto::dot(a, yocto::cross(b, c_v));
          vec3 rhs = -p3;
          double w0 = yocto::dot(rhs, yocto::cross(b, c_v)) / det;
          double w1 = yocto::dot(a, yocto::cross(rhs, c_v)) / det;
          double w2 = yocto::dot(a, yocto::cross(b, rhs)) / det;
          double w3 = 1.0 - w0 - w1 - w2;

          if (w0 > 0.01 && w1 > 0.01 && w2 > 0.01 && w3 > 0.01) {
            std::cout << "FOUND STRICT 4-AXIS ENCLOSING TRIPLE ON CORNER 2!\n"
                      << "  w0=" << w0 << " w1=" << w1 << " w2=" << w2 << " w3=" << w3 << "\n"
                      << "  Triple: (" << valid[i].edge_start << "->" << valid[i].edge_finish << " v=" << valid[i].vertex << "), "
                      << "(" << valid[j].edge_start << "->" << valid[j].edge_finish << " v=" << valid[j].vertex << "), "
                      << "(" << valid[k].edge_start << "->" << valid[k].edge_finish << " v=" << valid[k].vertex << ")\n";
            return 0;
          }
        }
      }
    }
  }
  std::cout << "No strictly enclosing triple among valid contacts on Corner 2.\n";
  return 0;
}
