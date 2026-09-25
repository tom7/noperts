#include <iostream>
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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  BigVecQ3 edges[3] = {Tube229::GetExactEdge(c0[0]), Tube229::GetExactEdge(c0[1]), Tube229::GetExactEdge(c0[2])};
  BigVecQ3 coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
  BigVecQ3 coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
  BigVecQ3 coeff2 = BigVecQ3::Cross(edges[0], edges[1]);

  BigRat p0 = BigVecQ3::Dot(tri.corners[0], coeff0);
  BigRat p1 = BigVecQ3::Dot(tri.corners[0], coeff1);
  BigRat p2 = BigVecQ3::Dot(tri.corners[0], coeff2);
  if (p0 < 0 && p1 < 0 && p2 < 0) {
    std::swap(c0[1], c0[2]);
    std::swap(edges[1], edges[2]);
    coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
    coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
    coeff2 = BigVecQ3::Cross(edges[0], edges[1]);
  }

  BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};
  BigRat support_error(6, 1000000000000000LL);

  BigRat weight_upper[3];
  for (int m = 0; m < 3; m++) {
    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
    for (int c = 1; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
      if (val > w_max) w_max = val;
    }
    weight_upper[m] = w_max + support_error;
  }

  BigRat defect0[3] = {BigRat(0), BigRat(0), BigRat(0)};
  for (int m = 0; m < 3; m++) {
    int sel = c0[m].vertex;
    BigVecQ3 v_sel = Tube229::VertexQ(sel);
    for (int k = 0; k < 20; k++) {
      bool tie = (k == sel) ||
                 (c0[m].mix == 1000 && sel == c0[m].edge_finish && k == c0[m].edge_start) ||
                 (c0[m].mix == 0 && sel == c0[m].edge_start2 && k == c0[m].edge_finish2);
      if (!tie) {
        BigVecQ3 v_k = Tube229::VertexQ(k);
        BigVecQ3 delta = v_k - v_sel;
        BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta);
        BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
          if (val > max_s) max_s = val;
        }
        BigRat s_upper = max_s + support_error;
        if (s_upper > defect0[m]) {
          defect0[m] = s_upper;
        }
      }
    }
  }

  std::cout << "defect0[0] = " << defect0[0].ToString() << " (" << defect0[0].ToDouble() << ")\n";
  std::cout << "defect0[1] = " << defect0[1].ToString() << " (" << defect0[1].ToDouble() << ")\n";
  std::cout << "defect0[2] = " << defect0[2].ToString() << " (" << defect0[2].ToDouble() << ")\n";

  BigRat D0 = weight_upper[0] * defect0[0] + weight_upper[1] * defect0[1] + weight_upper[2] * defect0[2];
  std::cout << "D0 = " << D0.ToString() << " (" << D0.ToDouble() << ")\n";

  return 0;
}
