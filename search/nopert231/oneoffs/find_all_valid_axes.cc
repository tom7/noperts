#include <iostream>
#include <vector>
#include <algorithm>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  vec3 omega_obs = {-0.400992, 0.483041, 0.778381};
  vec3 neg_omega = -omega_obs;

  for (const std::string &path : {"3121300", "3121303021"}) {
    TriangleQ tri = TriangleFromPath(path);
    std::cout << "\n============================================\n";
    std::cout << "Path: " << path << " (depth " << path.size() << ")\n";

    vec3 tri_f[3] = {
      ToDouble(tri.corners[0]),
      ToDouble(tri.corners[1]),
      ToDouble(tri.corners[2]),
    };

    // 1. Gather candidate contacts from the 9 hull vertices:
    // Vertices: 1, 2, 4, 8, 9, 10, 14, 15, 19
    int hull_v[9] = {1, 2, 4, 8, 9, 10, 14, 15, 19};
    std::vector<ContactInfo> candidate_contacts;
    for (int v : hull_v) {
      for (const auto &c : Tube229::GenerateContactsForVertex(v)) {
        candidate_contacts.push_back(c);
      }
    }
    auto ContactKey = [](const ContactInfo &c) {
      return std::make_tuple(c.vertex, c.edge_start, c.edge_finish, c.edge_start2, c.edge_finish2, c.mix);
    };
    std::sort(candidate_contacts.begin(), candidate_contacts.end(),
              [&](const ContactInfo &a, const ContactInfo &b) {
                return ContactKey(a) < ContactKey(b);
              });
    candidate_contacts.erase(
        std::unique(candidate_contacts.begin(), candidate_contacts.end(),
                    [&](const ContactInfo &a, const ContactInfo &b) {
                      return ContactKey(a) == ContactKey(b);
                    }),
        candidate_contacts.end());

    std::vector<ContactInfo> valid_contacts;
    for (const auto &c : candidate_contacts) {
      vec3 edge = Tube229::GetDoubleEdge(c);
      int sel = c.vertex;
      bool ok = true;
      for (int k = 0; k < NUM_VERTICES; k++) {
        bool tie = (k == sel) ||
                   (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                   (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
        if (tie) continue;
        vec3 delta_v = Tube229::Vertex(k) - Tube229::Vertex(sel);
        vec3 coeff = yocto::cross(edge, delta_v);
        double u0 = yocto::dot(tri_f[0], coeff);
        double u1 = yocto::dot(tri_f[1], coeff);
        double u2 = yocto::dot(tri_f[2], coeff);
        if (std::max({u0, u1, u2}) > 1e-12) {
          ok = false;
          break;
        }
      }
      if (ok) valid_contacts.push_back(c);
    }

    std::cout << "Valid zero-defect contacts: " << valid_contacts.size() << "\n";

    struct ValidAxis {
      ContactInfo contacts[3];
      vec3 center;
      vec3 normalized_center;
      double dot_neg_omega;
      double dot_pos_omega;
    };
    std::vector<ValidAxis> found_axes;

    for (size_t i = 0; i < valid_contacts.size(); i++) {
      for (size_t j = i + 1; j < valid_contacts.size(); j++) {
        for (size_t k = j + 1; k < valid_contacts.size(); k++) {
          ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
          Tube229::CandidateTriple cand;
          if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

          AxisCertificate exact_cert;
          BigVecQ3 center;
          BigRat delta;
          std::string fail;
          if (Tube229::AuditAxis(tri, triple, &exact_cert, &center, &delta, &fail)) {
            vec3 c = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
            vec3 u = yocto::normalize(c);
            found_axes.push_back({
              {triple[0], triple[1], triple[2]},
              c, u,
              yocto::dot(u, neg_omega),
              yocto::dot(u, omega_obs)
            });
          }
        }
      }
    }

    std::cout << "Found " << found_axes.size() << " valid audited axes.\n";
    // Sort by dot product with neg_omega descending:
    std::sort(found_axes.begin(), found_axes.end(), [](const ValidAxis &a, const ValidAxis &b) {
      return a.dot_neg_omega > b.dot_neg_omega;
    });

    for (size_t i = 0; i < std::min((size_t)10, found_axes.size()); i++) {
      const auto &fa = found_axes[i];
      std::cout << "  Axis " << i << ": dot(-omega) = " << fa.dot_neg_omega
                << ", dot(+omega) = " << fa.dot_pos_omega
                << ", u = (" << fa.normalized_center.x << ", "
                << fa.normalized_center.y << ", " << fa.normalized_center.z << ")\n";
      std::cout << "    contacts: ("
                << fa.contacts[0].vertex << ", " << fa.contacts[1].vertex << ", " << fa.contacts[2].vertex
                << ")\n";
    }
  }

  return 0;
}
