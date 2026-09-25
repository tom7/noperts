#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);
  double norm_u0 = std::sqrt(norm_u0_sq);
  vec3 u0_hat = u0 / norm_u0;

  vec3 arbitrary = (std::abs(u0_hat.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 k1 = yocto::normalize(yocto::cross(u0_hat, arbitrary));
  vec3 k2 = yocto::cross(u0_hat, k1);

  vec3 P0 = u0 / norm_u0_sq;
  double x = 24.5, y = -19.0791;
  vec3 p = P0 + x * k1 + y * k2;
  vec3 a = yocto::normalize(p);

  std::cout << "Target direction a: (" << a.x << ", " << a.y << ", " << a.z << ")\n";

  // Get ALL valid hull contacts
  std::vector<ContactInfo> valid_contacts;
  for (int e = 0; e < 24; e++) {
    for (int t = 0; t < 24; t++) {
      if (e == t) continue;
      for (int m = 0; m <= 1000; m += 200) {
        ContactInfo c = {e, t, t, (t + 1) % 24, m, t};
        if (Tube229::IsStrictHullContact(tri, c)) {
          valid_contacts.push_back(c);
        }
      }
    }
  }
  std::cout << "Found " << valid_contacts.size() << " valid contacts\n";

  double box_delta = 234013.0 / 1000000000.0;
  double best_dot = -1.0;
  ContactInfo best_triple[3];
  AxisCertificate best_cert;

  int count = 0;
  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        if (Tube229::AuditAxis(tri, triple, &cert, &ctr, &del, &err, BigRat(0))) {
          if (del.ToDouble() <= box_delta) {
            vec3 v = vec3{ctr.x.ToDouble() / cert.B.ToDouble(),
                          ctr.y.ToDouble() / cert.B.ToDouble(),
                          ctr.z.ToDouble() / cert.B.ToDouble()};
            double d = yocto::dot(a, v);
            if (d > best_dot) {
              best_dot = d;
              best_triple[0] = triple[0];
              best_triple[1] = triple[1];
              best_triple[2] = triple[2];
              best_cert = cert;
              std::cout << "New best dot: " << best_dot << " (delta " << del.ToDouble() << ")\n";
            }
          }
        }
      }
    }
  }

  std::cout << "Overall best dot: " << best_dot << "\n";
  return 0;
}
