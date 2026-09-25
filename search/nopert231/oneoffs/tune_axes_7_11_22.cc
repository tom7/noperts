#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  // Base contacts for Axis 7, 11, 22:
  // Axis 7: v=19 (mix0), v=3 (mix1), v=8 (mix2)
  // Axis 11: v=19 (mix0), v=8 (mix1), v=19 (mix2)
  // Axis 22: v=19 (mix0), v=8 (mix1), v=19 (mix2)
  // Wait, let's first check all 75*74*73 / 6 triples of the 75 audited axes!
  vec3 v = {0.0205096, 0.931624, 0.362843};
  auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, true);

  std::vector<Tube229::AuditedAxis> audited;
  for (const auto &cand : cands) {
    ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      audited.push_back({cert, center, delta});
    }
  }

  int M = audited.size();
  std::cout << "Testing all triples of the " << M << " audited axes for ray piercing -u0...\n";
  std::vector<vec3> u(M);
  for (int i = 0; i < M; i++) {
    u[i] = {audited[i].center.x.ToDouble() / audited[i].cert.B.ToDouble(),
            audited[i].center.y.ToDouble() / audited[i].cert.B.ToDouble(),
            audited[i].center.z.ToDouble() / audited[i].cert.B.ToDouble()};
  }

  vec3 target_ray = -u0;
  double best_cone_margin = -1e9;
  int bi = -1, bj = -1, bk = -1;

  for (int i = 0; i < M; i++) {
    for (int j = i + 1; j < M; j++) {
      vec3 c_ij = yocto::cross(u[i], u[j]);
      for (int k = j + 1; k < M; k++) {
        double det = yocto::dot(c_ij, u[k]);
        if (std::abs(det) < 1e-8) continue;

        vec3 c_jk = yocto::cross(u[j], u[k]);
        vec3 c_ki = yocto::cross(u[k], u[i]);

        double a = yocto::dot(target_ray, c_jk) / det;
        double b = yocto::dot(target_ray, c_ki) / det;
        double c = yocto::dot(target_ray, c_ij) / det;

        double m = std::min({a, b, c});
        if (m > best_cone_margin) {
          best_cone_margin = m;
          bi = i; bj = j; bk = k;
          if (m > 0) {
            std::cout << "SUCCESS! Cone contains -u0! (" << bi << ", " << bj << ", " << bk << ")\n";
            std::cout << "margin = " << m << " (a=" << a << ", b=" << b << ", c=" << c << ")\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Best cone margin among all triples: " << best_cone_margin << " with ("
            << bi << ", " << bj << ", " << bk << ")\n";
  return 0;
}
