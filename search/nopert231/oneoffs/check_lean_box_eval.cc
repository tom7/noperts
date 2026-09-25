#include <iostream>
#include <vector>
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
  std::vector<std::string> leaves = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  ContactInfo contacts[4][3] = {
    // Axis 0 (annular, with v14)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)},
    // Axis 1 (zero-defect complement)
    {MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9)},
    // Axis 2 (zero-defect complement)
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15)},
    // Axis 3 (zero-defect complement)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(10, 15, 15, 19, 800, 15)}
  };

  BigVecQ3 octa[6] = {
    BigVecQ3(BigRat(1), BigRat(0), BigRat(0)),
    BigVecQ3(BigRat(-1), BigRat(0), BigRat(0)),
    BigVecQ3(BigRat(0), BigRat(1), BigRat(0)),
    BigVecQ3(BigRat(0), BigRat(-1), BigRat(0)),
    BigVecQ3(BigRat(0), BigRat(0), BigRat(1)),
    BigVecQ3(BigRat(0), BigRat(0), BigRat(-1))
  };

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Leaf " << path << ":\n";
    TriangleQ tri = TriangleFromPath(path);

    BigVecQ3 centers[4];
    BigRat deltas[4];
    AxisCertificate axes[4];
    for (int a = 0; a < 4; a++) {
      std::string err;
      BigRat max_def = (a == 0) ? BigRat(5, 1000) : BigRat(0);
      Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def);
    }

    BigVecQ3 norm_centers[4];
    for (int a = 0; a < 4; a++) {
      norm_centers[a] = centers[a];
      std::cout << "  u" << a << " len = " << std::sqrt(BigVecQ3::Dot(norm_centers[a], norm_centers[a]).ToDouble()) << "\n";
    }

    BigRat norm_inradius = Tube229::ExactTetrahedronAxisRadius(norm_centers);
    std::cout << "  Normalized inradius = " << norm_inradius.ToDouble() << "\n";

    // Test octahedron containment for various c
    for (double c_try : {0.05, 0.04, 0.03, 0.02, 0.01, 0.005, 0.002}) {
      BigRat c_rat = BigRat::FromDouble(c_try);
      BigRat scale = BigRat(7, 4) * (c_rat + deltas[0]);
      bool all_in = true;
      for (int k = 0; k < 6; k++) {
        BigVecQ3 target = octa[k] * scale;
        BigRat lam[4];
        BigVecQ3 v0 = norm_centers[0] - norm_centers[3];
        BigVecQ3 v1 = norm_centers[1] - norm_centers[3];
        BigVecQ3 v2 = norm_centers[2] - norm_centers[3];
        BigVecQ3 w = target - norm_centers[3];
        BigRat den = BigVecQ3::Det(v0, v1, v2);
        lam[0] = BigVecQ3::Det(w, v1, v2) / den;
        lam[1] = BigVecQ3::Det(v0, w, v2) / den;
        lam[2] = BigVecQ3::Det(v0, v1, w) / den;
        lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
        for (int j = 0; j < 4; j++) {
          if (lam[j] < 0) { all_in = false; break; }
        }
        if (!all_in) break;
      }
      if (all_in) {
        std::cout << "  Barycentric valid at c = " << c_try << "\n";
        break;
      }
    }
  }
  return 0;
}
