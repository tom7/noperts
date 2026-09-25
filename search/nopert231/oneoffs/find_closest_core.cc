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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Axis 0 (annular, with v14)
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  BigVecQ3 u = center0;
  BigRat u_sq = BigVecQ3::Dot(u, u);

  std::vector<Tube229::AuditedAxis> candidates = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Testing " << candidates.size() << " candidates for core axis...\n";

  double best_cos = -1.0;
  int best_idx = -1;
  BigRat best_w_sq(1000);

  for (size_t i = 0; i < candidates.size(); i++) {
    BigVecQ3 v = candidates[i].center;
    BigRat v_sq = BigVecQ3::Dot(v, v);
    BigRat uv = BigVecQ3::Dot(u, v);
    if (uv <= 0) continue;
    BigRat lambda = uv / u_sq;
    BigVecQ3 w = v - u * lambda;
    BigRat w_sq = BigVecQ3::Dot(w, w);
    double cos_val = uv.ToDouble() / (std::sqrt(u_sq.ToDouble()) * std::sqrt(v_sq.ToDouble()));

    if (cos_val > best_cos) {
      best_cos = cos_val;
      best_idx = i;
      best_w_sq = w_sq;
      std::cout << "New best candidate " << i << ": cos=" << cos_val
                << " w_len=" << std::sqrt(w_sq.ToDouble())
                << " lambda=" << lambda.ToDouble()
                << " v_len=" << std::sqrt(v_sq.ToDouble()) << "\n";
    }
  }

  if (best_idx >= 0) {
    std::cout << "\nBest Core Axis Contacts:\n";
    for (int m = 0; m < 3; m++) {
      auto c = candidates[best_idx].cert.contacts[m];
      std::cout << "  {" << c.edge_start << "," << c.edge_finish << "," << c.edge_start2 << "," << c.edge_finish2 << "," << c.mix << "," << c.vertex << "}\n";
    }
  }

  return 0;
}
