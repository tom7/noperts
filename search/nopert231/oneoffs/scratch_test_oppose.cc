#include <iostream>
#include <iomanip>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
using namespace tubetree229;


int main() {
  std::string path = "031213032003";
  tubetree229::TriangleQ tri = tubetree229::TriangleFromPath(path);
  vec3 tri_f[3] = {tri.corners[0].ToDouble(), tri.corners[1].ToDouble(), tri.corners[2].ToDouble()};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::cout << "Triangle corners:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  c[" << i << "] = " << tri_f[i].x << ", " << tri_f[i].y << ", " << tri_f[i].z << "\n";
  }

  std::vector<int> fine_mixes = {
    0, 1, 10, 25, 50, 75, 100, 150, 200, 250, 300, 350, 400, 450, 500,
    550, 600, 650, 700, 750, 800, 850, 900, 925, 950, 975, 990, 999, 1000
  };

  std::vector<ContactInfo> raw_contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  std::cout << "Raw silhouette contacts: " << raw_contacts.size() << "\n";

  std::vector<Tube229::CandidateTriple> all_cands = Tube229::GenerateCandidateTriples(tri, raw_contacts, 1e-12);
  std::cout << "Valid candidate triples over tri: " << all_cands.size() << "\n";

  std::array<int, 4> simplex;
  vec3 oppose_dir = {0, 0, 0};
  bool found = Tube229::FindBalancedTetrahedron(all_cands, &simplex, &oppose_dir);
  std::cout << "FindBalancedTetrahedron: " << (found ? "FOUND" : "NOT FOUND") << "\n";
  std::cout << "Oppose dir: " << oppose_dir.x << ", " << oppose_dir.y << ", " << oppose_dir.z
            << " len=" << yocto::length(oppose_dir) << "\n";

  if (!found && yocto::length(oppose_dir) > 1e-12) {
    vec3 unit_n = oppose_dir / yocto::length(oppose_dir);
    std::vector<vec3> views_to_test = {

    centroid,
    tri_f[0],
    tri_f[1],
    tri_f[2],
    yocto::normalize(centroid + unit_n * 1e-4),
    yocto::normalize(centroid - unit_n * 1e-4),
    yocto::normalize(centroid + unit_n * 1e-3),
    yocto::normalize(centroid - unit_n * 1e-3),
  };

  std::cout << "Testing views for opposing candidates...\n";
  for (size_t vi = 0; vi < views_to_test.size(); vi++) {
    std::vector<int> coarse_mixes = {0, 1, 143, 286, 429, 571, 714, 857, 999, 1000};
    std::vector<ContactInfo> v_contacts = Tube229::GenerateSilhouetteContacts(views_to_test[vi], coarse_mixes);
    std::vector<Tube229::CandidateTriple> v_cands = Tube229::GenerateCandidateTriples(tri, v_contacts, 1e-12);
    int opp = 0;
    double min_d = 1e30;
    for (const auto &c : v_cands) {
      double d = yocto::dot(c.normalized_a, unit_n);
      min_d = std::min(min_d, d);
      if (d < 0) opp++;
    }
    std::cout << "  View " << vi << ": valid=" << v_cands.size() << " min_dot=" << min_d << " opposing=" << opp << "\n";
  }


    // Load neighbor certificates from tree_0.json
    std::unique_ptr<tubetree229::TreeNode> root = tubetree229::LoadTreeJson(".artifacts/nopert229/tree_0.json", false);
    if (root) {
      std::cout << "Loaded tree_0.json successfully\n";
      int count_valid_neighbor_axes = 0;
      int count_opposing_axes = 0;
      std::vector<Tube229::CandidateTriple> valid_neighbor_candidates;

      std::function<void(const tubetree229::TreeNode*)> walk = [&](const tubetree229::TreeNode *node) {
        if (node->direct_cert.has_value() && node->path.rfind("03121303200", 0) == 0) {
          for (int a = 0; a < 4; a++) {
            Tube229::CandidateTriple cand;
            if (Tube229::DoubleCheckAxis(tri, node->direct_cert->axes[a].contacts, &cand)) {
              count_valid_neighbor_axes++;
              double dot = yocto::dot(cand.normalized_a, unit_n);
              if (dot < 0) {
                count_opposing_axes++;
                std::cout << "FOUND OPPOSING AXIS from path " << node->path << " axis " << a
                          << " dot=" << dot << " a=(" << cand.normalized_a.x << ", " << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
              }
              bool dup = false;
              for (const auto &ex : valid_neighbor_candidates) {
                if (yocto::length(ex.normalized_a - cand.normalized_a) < 1e-6) { dup = true; break; }
              }
              if (!dup) valid_neighbor_candidates.push_back(cand);
            }
          }
        }
        for (const auto &child : node->children) {
          if (child) walk(child.get());
        }
      };

      walk(root.get());
      std::cout << "Valid neighbor axes over tri: " << count_valid_neighbor_axes
                << " (opposing: " << count_opposing_axes << ") unique=" << valid_neighbor_candidates.size() << "\n";

      // Test combining local candidates + neighbor candidates
      std::vector<Tube229::CandidateTriple> combined = all_cands;
      combined.insert(combined.end(), valid_neighbor_candidates.begin(), valid_neighbor_candidates.end());
      std::array<int, 4> comb_simplex;
      vec3 comb_oppose;
      if (Tube229::FindBalancedTetrahedron(combined, &comb_simplex, &comb_oppose)) {
        std::cout << "SUCCESS! Combined local + neighbor candidates caged the origin!\n";
        for (int a = 0; a < 4; a++) {
          std::cout << "  Simplex axis " << a << ": a=("
                    << combined[comb_simplex[a]].normalized_a.x << ", "
                    << combined[comb_simplex[a]].normalized_a.y << ", "
                    << combined[comb_simplex[a]].normalized_a.z << ")\n";
        }
      } else {
        std::cout << "Combined still did not cage origin. Oppose len=" << yocto::length(comb_oppose) << "\n";
      }
    }
  }

  return 0;
}


