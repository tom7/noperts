#include <iostream>
#include <iomanip>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

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
  const auto &sib_cert = *n0->direct_cert;

  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  std::vector<int> fine_mixes = {0, 1, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 999, 1000};
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
  std::cout << "Found " << valid_contacts.size() << " strictly valid contacts on tri1\n";

  vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});

  int found = 0;
  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri1, triple, &cand, 0.0)) {
          double d = yocto::dot(cand.normalized_a, uncov);
          if (d > 0.01) {
            found++;
            // Test 4-axis certificate with Axes 1, 2, 3!
            TubeCertificate test_c;
            test_c.symmetry_index = sib_cert.symmetry_index;
            test_c.axes[0] = sib_cert.axes[1];
            test_c.axes[1] = sib_cert.axes[2];
            test_c.axes[2] = sib_cert.axes[3];
            test_c.axes[3].contacts[0] = triple[0];
            test_c.axes[3].contacts[1] = triple[1];
            test_c.axes[3].contacts[2] = triple[2];

            TubeCertificate out_c;
            std::string f_msg;
            if (Tube229::AuditCertificateAdaptive(tri1, test_c, &out_c, &f_msg)) {
              std::cout << "!!! COMPLETE 4-AXIS SUCCESS !!!\n"
                        << "  r = " << out_c.r.ToString() << " (" << out_c.r.ToDouble() << ")\n"
                        << "  c = " << out_c.c.ToString() << " (" << out_c.c.ToDouble() << ")\n";
              return 0;
            }
          }
        }
      }
    }
  }
  std::cout << "Search complete. Tested promising triples, found " << found << " candidate triples.\n";
  return 0;
}
