#include <iostream>
#include <iomanip>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 tri1_f[3] = {
    ToDouble(tri1.corners[0]),
    ToDouble(tri1.corners[1]),
    ToDouble(tri1.corners[2]),
  };

  // Find all strictly valid contacts across tri1 (slack > 0)
  std::vector<ContactInfo> strict_contacts;
  for (int v = 0; v < Tube229::NUM_VERTICES; v++) {
    for (int es = 0; es < Tube229::NUM_VERTICES; es++) {
      for (int ef = 0; ef < Tube229::NUM_VERTICES; ef++) {
        if (es == ef) continue;
        ContactInfo ci = {v, es, ef, es, ef, 1000};
        vec3 edge = Tube229::GetDoubleEdge(ci);
        bool ok = true;
        double min_slack = 1e30;
        for (int k = 0; k < Tube229::NUM_VERTICES; k++) {
          if (k == v) continue;
          if (v == ef && k == es) continue;
          vec3 delta = Tube229::Vertex(k) - Tube229::Vertex(v);
          vec3 coeff = yocto::cross(edge, delta);
          double u0 = yocto::dot(tri1_f[0], coeff);
          double u1 = yocto::dot(tri1_f[1], coeff);
          double u2 = yocto::dot(tri1_f[2], coeff);
          double max_u = std::max({u0, u1, u2});
          if (max_u > 0) { ok = false; break; }
          min_slack = std::min(min_slack, -max_u);
        }
        if (ok && min_slack > 1e-6) {
          strict_contacts.push_back(ci);
        }
      }
    }
  }

  std::cout << "Found " << strict_contacts.size() << " strictly valid contacts across tri1.\n";

  vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
  double best_dot = -2.0;
  Tube229::CandidateTriple best_cand;
  int C = strict_contacts.size();

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo test_c[3] = {strict_contacts[i], strict_contacts[j], strict_contacts[k]};
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri1, test_c, &cand, 0.0)) {
          double d = yocto::dot(cand.normalized_a, sep_norm);
          if (d > best_dot) {
            best_dot = d;
            best_cand = cand;
          }
        }
      }
    }
  }

  std::cout << "Best dot with sep_norm among all strictly valid triples: " << best_dot << "\n";
  if (best_dot > -2.0) {
    std::cout << "  norm_a = (" << best_cand.normalized_a.x << ", "
              << best_cand.normalized_a.y << ", " << best_cand.normalized_a.z << ")\n";
    std::cout << "  slack = " << best_cand.strict_slack << "\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "  m=" << m << ": v=" << best_cand.contacts[m].vertex
                << " edge=(" << best_cand.contacts[m].edge_start << "->" << best_cand.contacts[m].edge_finish << ")\n";
    }
  }

  return 0;
}
