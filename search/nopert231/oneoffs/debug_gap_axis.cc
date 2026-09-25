#include <iostream>
#include <vector>
#include <cmath>
#include <random>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 Vert(int k) {
  BigVecQ3 v = Tube229::VertexQ(k);
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 tri_f[3] = {
    vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()},
    vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()},
    vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()}
  };

  std::vector<ContactInfo> valid_contacts;
  for (int v = 0; v < 22; v++) {
    for (int u = 0; u < 22; u++) {
      if (u == v) continue;
      for (int w = 0; w < 22; w++) {
        if (w == v || w == u) continue;

        for (int mix : {0, 500, 1000}) {
          ContactInfo c;
          c.vertex = v;
          c.edge_start = u; c.edge_finish = v;
          c.edge_start2 = v; c.edge_finish2 = w;
          c.mix = mix;

          vec3 edge = Tube229::GetDoubleEdge(c);
          bool ok = true;
          for (int k = 0; k < 22; k++) {
            bool tie = (k == v) ||
                       (mix == 1000 && v == c.edge_finish && k == c.edge_start) ||
                       (mix == 0 && v == c.edge_start2 && k == c.edge_finish2);
            if (tie) continue;
            vec3 delta_v = Vert(k) - Vert(v);
            vec3 coeff = yocto::cross(edge, delta_v);
            double u0_val = yocto::dot(tri_f[0], coeff);
            double u1_val = yocto::dot(tri_f[1], coeff);
            double u2_val = yocto::dot(tri_f[2], coeff);
            if (std::max({u0_val, u1_val, u2_val}) > 1e-12) {
              ok = false;
              break;
            }
          }
          if (ok) {
            valid_contacts.push_back(c);
          }
        }
      }
    }
  }
  std::cout << "Valid contacts: " << valid_contacts.size() << "\n";

  vec3 target_gap = yocto::normalize(vec3{0.427937, -0.388053, -0.816263});

  int doublecheck_ok = 0;
  int audit_ok = 0;
  std::string err;

  std::mt19937_64 rng(999);
  std::uniform_int_distribution<size_t> dist(0, valid_contacts.size() - 1);

  double max_cand_dot = -1.0;
  double max_audited_dot = -1.0;

  for (int iter = 0; iter < 50000; iter++) {
    size_t i = dist(rng), j = dist(rng), k = dist(rng);
    if (i == j || j == k || i == k) continue;
    ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
    Tube229::CandidateTriple cand;
    if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;
    doublecheck_ok++;

    double d1 = yocto::dot(cand.normalized_a, target_gap);
    double d2 = yocto::dot(-cand.normalized_a, target_gap);
    double d = std::max(d1, d2);
    if (d > max_cand_dot) max_cand_dot = d;

    if (d > 0.05) {
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &err, BigRat(0))) {
        audit_ok++;
        vec3 a = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
        double da = yocto::dot(a, target_gap);
        if (da > max_audited_dot) {
          max_audited_dot = da;
          std::cout << "New max audited dot: " << max_audited_dot << "\n";
        }
      }
    }
  }

  std::cout << "Doublecheck count: " << doublecheck_ok << "\n";
  std::cout << "Max candidate dot: " << max_cand_dot << "\n";
  std::cout << "Max audited dot: " << max_audited_dot << "\n";
  return 0;
}
