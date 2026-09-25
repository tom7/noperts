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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  ContactInfo comp0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(14, 15, 15, 19, 600, 15)
  };
  ContactInfo comp1[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 600, 8),
    MakeContact(14, 15, 15, 19, 200, 15)
  };
  ContactInfo comp2[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 600, 15),
    MakeContact(14, 15, 15, 19, 400, 15)
  };

  AxisCertificate ax[4];
  BigVecQ3 ctr[4];
  BigRat del[4];
  Tube229::AuditAxis(tri, c_ann, &ax[0], &ctr[0], &del[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp0, &ax[1], &ctr[1], &del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp1, &ax[2], &ctr[2], &del[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp2, &ax[3], &ctr[3], &del[3], &err, BigRat(0));

  std::cout << "Axes audited. Checking weightLower:\n";
  for (int j = 0; j < 4; j++) {
    for (int i = 0; i < 3; i++) {
      // In Lean, weightLower j i is computed via Dot(tri.corners[c], w_coeff)
      // Let's compute min dot over corners
      BigVecQ3 edges[3] = {
        Tube229::GetExactEdge(ax[j].contacts[0]),
        Tube229::GetExactEdge(ax[j].contacts[1]),
        Tube229::GetExactEdge(ax[j].contacts[2])
      };
      BigVecQ3 w_coeff;
      if (i == 0) w_coeff = BigVecQ3::Cross(edges[1], edges[2]);
      else if (i == 1) w_coeff = BigVecQ3::Cross(edges[2], edges[0]);
      else w_coeff = BigVecQ3::Cross(edges[0], edges[1]);

      BigRat min_w = BigVecQ3::Dot(tri.corners[0], w_coeff);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeff);
        if (val < min_w) min_w = val;
      }
      std::cout << "ax[" << j << "] weightLower[" << i << "] = " << min_w.ToDouble() << "\n";
    }
  }

  // Check nonzero_witness for core axis
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 0, 2),
    MakeContact(4, 8, 8, 9, 666, 8),
    MakeContact(15, 19, 19, 3, 1000, 19)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  std::cout << "\nCore axis nonzero witnesses:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "witness[" << i << "] = " << ax_core.nonzero_witness[i] << "\n";
    // Check supportUpper at witness
    BigRat max_supp(-1000);
    int wit = ax_core.nonzero_witness[i];
    BigVecQ3 edge = Tube229::GetExactEdge(ax_core.contacts[i]);
    BigVecQ3 delta_v = Tube229::VertexQ(wit) - Tube229::VertexQ(ax_core.contacts[i].vertex);
    BigVecQ3 s_coeff = BigVecQ3::Cross(edge, delta_v);
    for (int c = 0; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
      if (c == 0 || val > max_supp) max_supp = val;
    }
    std::cout << "supportUpper[" << i << "][" << wit << "] = " << max_supp.ToDouble() << "\n";
  }

  return 0;
}
