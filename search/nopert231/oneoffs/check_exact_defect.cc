#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  // Compute exact defect D0 on tri:
  BigVecQ3 edges[3] = {
    Tube229::GetExactEdge(c0[0]),
    Tube229::GetExactEdge(c0[1]),
    Tube229::GetExactEdge(c0[2])
  };
  BigVecQ3 w_coeffs[3] = {
    BigVecQ3::Cross(edges[1], edges[2]),
    BigVecQ3::Cross(edges[2], edges[0]),
    BigVecQ3::Cross(edges[0], edges[1])
  };

  BigRat w_upper[3];
  for (int m = 0; m < 3; m++) {
    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
    for (int c = 1; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
      if (val > w_max) w_max = val;
    }
    w_upper[m] = w_max;
    std::cout << "w_upper[" << m << "] = " << w_upper[m].ToDouble() << "\n";
  }

  // Defect on each contact:
  // For each contact m, max over corners c of (supp(tri.corners[c], edge_m) - dot(vertex_m, edge_m))
  BigRat defect0[3] = {BigRat(0), BigRat(0), BigRat(0)};
  for (int m = 0; m < 3; m++) {
    BigVecQ3 e = edges[m];
    BigRat max_def(0);
    for (int c = 0; c < 3; c++) {
      BigVecQ3 normal = BigVecQ3::Cross(tri.corners[c], e);
      // Find true support on 20 vertices
      BigRat max_dot = BigVecQ3::Dot(Tube229::VertexQ(0), normal);
      for (int v = 1; v < 20; v++) {
        BigRat d = BigVecQ3::Dot(Tube229::VertexQ(v), normal);
        if (d > max_dot) max_dot = d;
      }
      BigRat v_dot = BigVecQ3::Dot(Tube229::VertexQ(c0[m].vertex), normal);
      BigRat def = max_dot - v_dot;
      if (def > max_def) max_def = def;
    }
    defect0[m] = max_def;
    std::cout << "contact " << m << " (vertex " << c0[m].vertex << "): defect = " << defect0[m].ToDouble() << "\n";
  }

  BigRat D0 = w_upper[0] * defect0[0] + w_upper[1] * defect0[1] + w_upper[2] * defect0[2];
  std::cout << "Total D0 = " << D0.ToString() << " (" << D0.ToDouble() << ")\n";

  return 0;
}
