#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

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

  vec3 axis = yocto::normalize(-u0);
  vec3 perp1 = yocto::normalize(yocto::cross(axis, vec3{1, 0, 0}));
  if (yocto::length(yocto::cross(axis, vec3{1, 0, 0})) < 0.1) {
    perp1 = yocto::normalize(yocto::cross(axis, vec3{0, 1, 0}));
  }
  vec3 perp2 = yocto::cross(axis, perp1);

  double rad = 84.0 * M_PI / 180.0;
  double ca = std::cos(rad);
  double sa = std::sin(rad);

  vec3 ideal1 = yocto::normalize(axis * ca + perp1 * sa);
  vec3 ideal2 = yocto::normalize(axis * ca + (perp1 * (-0.5) + perp2 * (std::sqrt(3.0)/2.0)) * sa);
  vec3 ideal3 = yocto::normalize(axis * ca + (perp1 * (-0.5) - perp2 * (std::sqrt(3.0)/2.0)) * sa);

  std::vector<vec3> sample_views = {ideal1, ideal2, ideal3, axis, -u0};

  std::vector<Tube229::CandidateTriple> all_cands;
  for (const auto &v : sample_views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, true);
    std::cout << "View (" << v.x << ", " << v.y << ", " << v.z << ") produced "
              << cands.size() << " candidates\n";
    for (const auto &c : cands) {
      all_cands.push_back(c);
    }
  }

  std::cout << "Total deduplicated candidates: " << all_cands.size() << "\n";

  // Audit zero-defect axes from these candidates:
  std::vector<Tube229::AuditedAxis> audited;
  for (const auto &cand : all_cands) {
    ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      audited.push_back({cert, center, delta});
    }
  }

  std::cout << "Successfully audited " << audited.size() << " zero-defect axes!\n";

  // Now test triples of these audited axes with u0 and c_cone = 0.028!
  double delta = 3.33e-7;
  double c_cone = 0.028;
  double box_c = 1e-7;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  int M = audited.size();
  std::vector<vec3> u(M);
  for (int i = 0; i < M; i++) {
    u[i] = {audited[i].center.x.ToDouble() / audited[i].cert.B.ToDouble(),
            audited[i].center.y.ToDouble() / audited[i].cert.B.ToDouble(),
            audited[i].center.z.ToDouble() / audited[i].cert.B.ToDouble()};
  }

  std::vector<vec3> oct = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  for (double c_cone = 0.0273; c_cone <= 0.0292; c_cone += 0.0002) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    double best_min_l = -1;
    int bi = -1, bj = -1, bk = -1;

    for (int i = 0; i < M; i++) {
      vec3 d1 = u[i] - v0;
      for (int j = i + 1; j < M; j++) {
        vec3 d2 = u[j] - v0;
        vec3 c12 = yocto::cross(d1, d2);
        if (yocto::length(c12) < 1e-6) continue;

        for (int k = j + 1; k < M; k++) {
          vec3 d3 = u[k] - v0;
          double det = yocto::dot(c12, d3);
          if (std::abs(det) < 1e-8) continue;

          vec3 c23 = yocto::cross(d2, d3);
          vec3 c31 = yocto::cross(d3, d1);

          double min_l = 1e9;
          for (const auto &p_dir : oct) {
            vec3 p = p_dir * R;
            vec3 dp = p - v0;
            double l1 = yocto::dot(dp, c23) / det;
            double l2 = yocto::dot(dp, c31) / det;
            double l3 = yocto::dot(dp, c12) / det;
            double l0 = 1.0 - l1 - l2 - l3;
            double m = std::min({l0, l1, l2, l3});
            if (m < min_l) min_l = m;
            if (min_l <= best_min_l) break;
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            bi = i; bj = j; bk = k;
          }
        }
      }
    }
    std::cout << "c_cone = " << c_cone << ": best_min_l = " << best_min_l
              << " with (" << bi << ", " << bj << ", " << bk << ")\n";
  }
  return 0;
}
