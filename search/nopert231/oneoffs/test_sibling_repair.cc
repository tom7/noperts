#include <iostream>
#include <iomanip>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  // Find child 0 and child 1 of 03121300211212201212
  std::string p0 = "031213002112122012120";
  std::string p1 = "031213002112122012121";

  TreeNode *n0 = nullptr, *n1 = nullptr;
  auto find_nodes = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p0) n0 = node;
    if (node->path == p1) n1 = node;
    if (n0 && n1) return;
    if (p0.starts_with(node->path) || p1.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find_nodes(find_nodes, root.get());

  if (!n0 || !n1 || !n0->direct_cert.has_value()) {
    std::cout << "Nodes not found or n0 not certified\n";
    return 1;
  }

  std::cout << "Found n0 (certified) and n1 (uncertified leaf)!\n";
  TriangleQ tri1 = n1->GetTriangle();
  const TubeCertificate &sib_cert = *n0->direct_cert;

  // Check each axis of sib_cert on tri1
  std::vector<Tube229::CandidateTriple> valid_sibling_axes;
  std::vector<int> failing_axis_indices;

  for (int a = 0; a < 4; a++) {
    Tube229::CandidateTriple cand;
    if (Tube229::DoubleCheckAxis(tri1, sib_cert.axes[a].contacts, &cand)) {
      std::cout << "  Axis " << a << ": VALID on target!\n";
      valid_sibling_axes.push_back(cand);
    } else {
      std::cout << "  Axis " << a << ": FAILS on target!\n";
      failing_axis_indices.push_back(a);
    }
  }

  std::cout << "Valid sibling axes: " << valid_sibling_axes.size()
            << ", Failing axes: " << failing_axis_indices.size() << "\n";

  // Now generate silhouette contacts on tri1
  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  std::vector<int> fine_mixes = {0, 1, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 999, 1000};
  std::vector<ContactInfo> raw_contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  
  // Filter contacts valid on tri1
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
  std::cout << "Valid silhouette contacts on tri1: " << valid_contacts.size() << "\n";

  // For each failing axis, try replacing 1 contact
  std::vector<std::vector<Tube229::CandidateTriple>> replacement_axes(failing_axis_indices.size());
  for (size_t fi = 0; fi < failing_axis_indices.size(); fi++) {
    int a = failing_axis_indices[fi];
    for (int replace_pos = 0; replace_pos < 3; replace_pos++) {
      for (const auto &c : valid_contacts) {
        ContactInfo test_contacts[3] = {sib_cert.axes[a].contacts[0], sib_cert.axes[a].contacts[1], sib_cert.axes[a].contacts[2]};
        test_contacts[replace_pos] = c;
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri1, test_contacts, &cand)) {
          replacement_axes[fi].push_back(cand);
        }
      }
    }
    std::cout << "Failing axis " << a << " has " << replacement_axes[fi].size() << " valid replacements!\n";
  }

  std::cout << "\nTesting all 26 replacement candidates for 4-axis certificate:\n";
  for (size_t i = 0; i < replacement_axes[0].size(); i++) {
    TubeCertificate test_c;
    test_c.symmetry_index = sib_cert.symmetry_index;
    test_c.axes[0] = sib_cert.axes[1];
    test_c.axes[1] = sib_cert.axes[2];
    test_c.axes[2] = sib_cert.axes[3];
    test_c.axes[3].contacts[0] = replacement_axes[0][i].contacts[0];
    test_c.axes[3].contacts[1] = replacement_axes[0][i].contacts[1];
    test_c.axes[3].contacts[2] = replacement_axes[0][i].contacts[2];

    TubeCertificate out_c;
    std::string f_msg;
    bool ok = Tube229::AuditCertificateAdaptive(tri1, test_c, &out_c, &f_msg);
    if (ok) {
      std::cout << "SUCCESS at rep " << i << "!\n"
                << "  r = " << out_c.r.ToString() << " (" << out_c.r.ToDouble() << ")\n"
                << "  c = " << out_c.c.ToString() << " (" << out_c.c.ToDouble() << ")\n";
      break;
    } else {
      // Print failure reason
      if (i < 5 || i == 25) {
        std::cout << "rep " << i << " failed: " << f_msg << "\n";
      }
    }
  }

  return 0;
}
