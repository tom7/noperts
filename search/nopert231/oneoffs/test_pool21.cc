#include <iostream>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  if (!root) return 1;

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

  TriangleQ tri1 = n1->GetTriangle();
  const TubeCertificate &sib_cert = *n0->direct_cert;

  std::vector<Tube229::CandidateTriple> all_candidates;

  // 1. Sibling valid axes
  for (int a = 0; a < 4; a++) {
    Tube229::CandidateTriple cand;
    if (Tube229::DoubleCheckAxis(tri1, sib_cert.axes[a].contacts, &cand)) {
      all_candidates.push_back(cand);
    }
  }
  std::cout << "Valid sibling axes: " << all_candidates.size() << "\n";

  // 2. Multi-view candidates from tri1
  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  std::vector<vec3> sample_views = {centroid, tri1_f[0], tri1_f[1], tri1_f[2]};

  for (const auto &v : sample_views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri1, true, 6, true);
    for (const auto &c : cands) all_candidates.push_back(c);
  }
  std::cout << "Candidates after multi-view: " << all_candidates.size() << "\n";

  // 3. Opposing candidates in various directions
  std::vector<vec3> query_dirs = {
    vec3{-0.401, 0.483, 0.778},
    vec3{0.401, -0.483, -0.778},
    vec3{1, 0, 0}, vec3{-1, 0, 0},
    vec3{0, 1, 0}, vec3{0, -1, 0},
    vec3{0, 0, 1}, vec3{0, 0, -1}
  };
  for (const auto &qd : query_dirs) {
    auto opp = Tube229::FindOpposingCandidates(tri1, qd, 50, 1e-12);
    for (const auto &c : opp) all_candidates.push_back(c);
  }
  std::cout << "Total candidate pool: " << all_candidates.size() << "\n";

  // Deduplicate
  std::vector<Tube229::CandidateTriple> unique_cands;
  for (const auto &c : all_candidates) {
    bool dup = false;
    for (const auto &u : unique_cands) {
      if (yocto::length(u.normalized_a - c.normalized_a) < 1e-6) {
        dup = true; break;
      }
    }
    if (!dup) unique_cands.push_back(c);
  }
  std::cout << "Unique candidate pool: " << unique_cands.size() << "\n";

  // Run Wolfe / FindBalancedTetrahedron
  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool enclosed = Tube229::FindBalancedTetrahedron(unique_cands, &simplex, &sep_norm);
  std::cout << "FindBalancedTetrahedron on unique_cands: " << (enclosed ? "YES" : "NO") << "\n";
  if (enclosed) {
    TubeCertificate test_cert;
    test_cert.symmetry_index = sib_cert.symmetry_index;
    for (int a = 0; a < 4; a++) {
      test_cert.axes[a].contacts[0] = unique_cands[simplex[a]].contacts[0];
      test_cert.axes[a].contacts[1] = unique_cands[simplex[a]].contacts[1];
      test_cert.axes[a].contacts[2] = unique_cands[simplex[a]].contacts[2];
    }
    TubeCertificate out_cert;
    std::string fail_msg;
    if (Tube229::AuditCertificateAdaptive(tri1, test_cert, &out_cert, &fail_msg)) {
      std::cout << "SUCCESS! Leaf 031213002112122012121 certified!\n"
                << "  r = " << out_cert.r.ToString() << " (" << out_cert.r.ToDouble() << ")\n"
                << "  c = " << out_cert.c.ToString() << " (" << out_cert.c.ToDouble() << ")\n";
    } else {
      std::cout << "Audit failed: " << fail_msg << "\n";
    }
  } else {
    std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
  }

  return 0;
}
