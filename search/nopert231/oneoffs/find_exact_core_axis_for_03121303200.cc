#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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

struct CandResult {
  double angle;
  double lam;
  double w_len;
  double min_c_cone_for_hineq;
  ContactInfo contacts[3];
  AxisCertificate cert;
};

int main() {
  std::string target = "03121303200";
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
  vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  vec3 perp1 = yocto::normalize(yocto::cross(dir_u0, vec3{1, 0, 0}));
  vec3 perp2 = yocto::normalize(yocto::cross(dir_u0, perp1));

  double c_core = 0.0003;
  double u0_sq = yocto::dot(u0, u0);

  std::vector<CandResult> top_cands;

  for (double phi = 0; phi < 2 * M_PI; phi += 0.05) {
    vec3 v = perp1 * std::cos(phi) + perp2 * std::sin(phi);
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, false);
    for (const auto &cand : cands) {
      ContactInfo c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
        vec3 v0 = {ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()};
        double lam = yocto::dot(v0, u0) / u0_sq;
        if (lam <= 0) continue;
        vec3 w = v0 - u0 * lam;
        double w_sq = yocto::dot(w, w);
        double w_len = std::sqrt(w_sq);
        double d = yocto::dot(yocto::normalize(v0), dir_u0);
        double angle = std::acos(std::max(-1.0, std::min(1.0, d))) * 180.0 / M_PI;

        // find smallest c_cone in [0.005, 0.050] where hineq holds
        double min_c_cone = 1.0;
        for (double cc = 0.005; cc <= 0.050; cc += 0.001) {
          if (lam * cc >= c_core) {
            double lhs = w_sq * (u0_sq - cc * cc);
            double rhs = u0_sq * std::pow(lam * cc - c_core, 2);
            if (lhs <= rhs) {
              min_c_cone = cc;
              break;
            }
          }
        }

        CandResult r;
        r.angle = angle;
        r.lam = lam;
        r.w_len = w_len;
        r.min_c_cone_for_hineq = min_c_cone;
        for (int i = 0; i < 3; i++) r.contacts[i] = cand.contacts[i];
        r.cert = cert;

        top_cands.push_back(r);
      }
    }
  }

  std::sort(top_cands.begin(), top_cands.end(), [](const CandResult &a, const CandResult &b) {
    return a.min_c_cone_for_hineq < b.min_c_cone_for_hineq;
  });

  std::cout << "Top 10 candidates by min_c_cone_for_hineq:\n";
  for (size_t i = 0; i < std::min((size_t)10, top_cands.size()); i++) {
    const auto &r = top_cands[i];
    std::cout << "#" << i << ": min_c_cone=" << r.min_c_cone_for_hineq 
              << ", angle=" << r.angle << " deg, lam=" << r.lam << ", ||w||=" << r.w_len << "\n";
    std::cout << "  B=" << r.cert.B.ToString() << "\n";
    for (int k = 0; k < 3; k++) {
      std::cout << "  c[" << k << "]: (" << r.contacts[k].edge_start << "->" << r.contacts[k].edge_finish
                << ", " << r.contacts[k].mix << ", v=" << r.contacts[k].vertex << ")\n";
    }
  }

  return 0;
}
