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

  // Axis 0
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

  std::cout << "Searching for zero-defect core axis with Contacts 0 and 1 fixed...\n";

  double best_cos = -1.0;
  ContactInfo best_c2;
  BigVecQ3 best_v;
  BigRat best_lambda;

  for (int v2 = 0; v2 < 20; v2++) {
    for (int v1 = 0; v1 < 20; v1++) {
      if (v1 == v2) continue;
      for (int v3 = 0; v3 < 20; v3++) {
        if (v3 == v2 || v3 == v1) continue;

        for (int mix : {0, 200, 400, 600, 800, 1000}) {
          ContactInfo test_c[3] = {
            c0[0], c0[1],
            MakeContact(v1, v2, v2, v3, mix, v2)
          };

          AxisCertificate test_ax;
          BigVecQ3 test_center;
          BigRat test_delta;
          if (Tube229::AuditAxis(tri, test_c, &test_ax, &test_center, &test_delta, &err, BigRat(0))) {
            BigVecQ3 v = test_center;
            BigRat uv = BigVecQ3::Dot(u, v);
            if (uv <= 0) continue;
            BigRat lambda = uv / u_sq;
            BigVecQ3 w = v - u * lambda;
            BigRat w_sq = BigVecQ3::Dot(w, w);
            double w_val = w_sq.ToDouble();
            double cos_val = uv.ToDouble() / (std::sqrt(u_sq.ToDouble()) * std::sqrt(BigVecQ3::Dot(v, v).ToDouble()));
            if (cos_val > best_cos) {
              best_cos = cos_val;
              best_c2 = test_c[2];
              best_v = v;
              best_lambda = lambda;
              std::cout << "Found better zero-defect core axis: cos=" << cos_val
                        << " w_len=" << std::sqrt(w_val)
                        << " lambda=" << lambda.ToDouble()
                        << " Contact 2: {" << best_c2.edge_start << "," << best_c2.edge_finish
                        << "," << best_c2.edge_start2 << "," << best_c2.edge_finish2
                        << "," << best_c2.mix << "," << best_c2.vertex << "}\n";
            }
          }
        }
      }
    }
  }

  std::cout << "\nBest cos: " << best_cos << "\n";
  return 0;
}
