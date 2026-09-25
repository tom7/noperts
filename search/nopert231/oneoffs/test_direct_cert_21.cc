#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  std::vector<Tube229::CandidateTriple> all_candidates;

  // Multi-view candidates from tri
  vec3 tri_f[3] = {
    vec3{tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()},
    vec3{tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()},
    vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  std::vector<vec3> sample_views = {centroid, tri_f[0], tri_f[1], tri_f[2]};

  for (const auto &v : sample_views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, true);
    for (const auto &c : cands) all_candidates.push_back(c);
  }
  std::cout << "Candidates after multi-view: " << all_candidates.size() << "\n";

  // Opposing candidates
  std::vector<vec3> query_dirs = {
    vec3{-0.401, 0.483, 0.778},
    vec3{0.401, -0.483, -0.778},
    vec3{1, 0, 0}, vec3{-1, 0, 0},
    vec3{0, 1, 0}, vec3{0, -1, 0},
    vec3{0, 0, 1}, vec3{0, 0, -1}
  };
  for (const auto &qd : query_dirs) {
    auto opp = Tube229::FindOpposingCandidates(tri, qd, 50, 1e-12);
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
  std::cout << "FindBalancedTetrahedron: " << (enclosed ? "YES" : "NO") << "\n";
  if (enclosed) {
    TubeCertificate test_cert;
    test_cert.symmetry_index = 0;
    for (int a = 0; a < 4; a++) {
      test_cert.axes[a].contacts[0] = unique_cands[simplex[a]].contacts[0];
      test_cert.axes[a].contacts[1] = unique_cands[simplex[a]].contacts[1];
      test_cert.axes[a].contacts[2] = unique_cands[simplex[a]].contacts[2];
    }
    TubeCertificate out_cert;
    std::string fail_msg;
    if (Tube229::AuditCertificateAdaptive(tri, test_cert, &out_cert, &fail_msg)) {
      std::cout << "SUCCESS! Leaf " << target << " DIRECTLY certified!\n"
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
