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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo win_comp[3][3] = {
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(3, 2, 2, 1, 0, 2), MakeContact(10, 15, 15, 19, 333, 15) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(3, 2, 2, 1, 0, 2), MakeContact(10, 15, 15, 19, 666, 15) },
    { MakeContact(3, 2, 2, 1, 0, 2), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(1, 4, 4, 8, 1000, 4) }
  };
  ContactInfo win_core[3] = {
    MakeContact(19, 3, 3, 2, 0, 3),
    MakeContact(14, 15, 15, 19, 400, 15),
    MakeContact(1, 4, 4, 8, 1000, 4)
  };

  std::string err;
  AxisCertificate ax0, ax_comp[3], ax_core;
  BigVecQ3 u0, comp_c[3], v;
  BigRat del0, comp_del[3], del_core;

  Tube229::AuditAxis(tri, c0, &ax0, &u0, &del0, &err, BigRat(1, 100000000));
  for (int a = 0; a < 3; a++) {
    Tube229::AuditAxis(tri, win_comp[a], &ax_comp[a], &comp_c[a], &comp_del[a], &err, BigRat(0));
  }
  Tube229::AuditAxis(tri, win_core, &ax_core, &v, &del_core, &err, BigRat(0));

  BigRat c_cone(9, 200);   // 0.045
  BigRat box_c(1, 5000);   // 0.0002
  BigRat box_delta = comp_del[0];
  if (comp_del[1] > box_delta) box_delta = comp_del[1];
  if (comp_del[2] > box_delta) box_delta = comp_del[2];
  if (del0 > box_delta) box_delta = del0;
  if (del_core > box_delta) box_delta = del_core;

  BigRat s = (box_c + box_delta) / c_cone;
  BigVecQ3 v0 = {s * u0.x, s * u0.y, s * u0.z};

  BigVecQ3 verts[4] = {v0, comp_c[0], comp_c[1], comp_c[2]};

  // Check tetrahedron determinant:
  BigRat d0 = -(verts[1].x * (verts[2].y * verts[3].z - verts[2].z * verts[3].y)
              - verts[1].y * (verts[2].x * verts[3].z - verts[2].z * verts[3].x)
              + verts[1].z * (verts[2].x * verts[3].y - verts[2].y * verts[3].x));
  BigRat d1 =  (verts[0].x * (verts[2].y * verts[3].z - verts[2].z * verts[3].y)
              - verts[0].y * (verts[2].x * verts[3].z - verts[2].z * verts[3].x)
              + verts[0].z * (verts[2].x * verts[3].y - verts[2].y * verts[3].x));
  BigRat d2 = -(verts[0].x * (verts[1].y * verts[3].z - verts[1].z * verts[3].y)
              - verts[0].y * (verts[1].x * verts[3].z - verts[1].z * verts[3].x)
              + verts[0].z * (verts[1].x * verts[3].y - verts[1].y * verts[3].x));
  BigRat d3 =  (verts[0].x * (verts[1].y * verts[2].z - verts[1].z * verts[2].y)
              - verts[0].y * (verts[1].x * verts[2].z - verts[1].z * verts[2].x)
              + verts[0].z * (verts[1].x * verts[2].y - verts[1].y * verts[2].x));
  BigRat det = d0 + d1 + d2 + d3;

  std::cout << "Tetrahedron det = " << det.ToString() << "\n";
  std::cout << "Barycentric origin = ("
            << (d0/det).ToDouble() << ", " << (d1/det).ToDouble() << ", "
            << (d2/det).ToDouble() << ", " << (d3/det).ToDouble() << ")\n";

  // Check 6 octahedron targets:
  BigRat R = BigRat(7, 4) * (box_c + box_delta);
  BigVecQ3 targets[6] = {
    {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
  };

  bool all_valid = true;
  for (int k = 0; k < 6; k++) {
    const BigVecQ3 &tgt = targets[k];
    // Solve barycentric coords for tgt:
    // M = [verts[j].x, verts[j].y, verts[j].z, 1]
    // Replace column j with tgt
    for (int j = 0; j < 4; j++) {
      BigVecQ3 cverts[4];
      for (int m = 0; m < 4; m++) cverts[m] = (m == j) ? tgt : verts[m];
      BigRat cd0 = -(cverts[1].x * (cverts[2].y * cverts[3].z - cverts[2].z * cverts[3].y)
                   - cverts[1].y * (cverts[2].x * cverts[3].z - cverts[2].z * cverts[3].x)
                   + cverts[1].z * (cverts[2].x * cverts[3].y - cverts[2].y * cverts[3].x));
      BigRat cd1 =  (cverts[0].x * (cverts[2].y * cverts[3].z - cverts[2].z * cverts[3].y)
                   - cverts[0].y * (cverts[2].x * cverts[3].z - cverts[2].z * cverts[3].x)
                   + cverts[0].z * (cverts[2].x * cverts[3].y - cverts[2].y * cverts[3].x));
      BigRat cd2 = -(cverts[0].x * (cverts[1].y * cverts[3].z - cverts[1].z * cverts[3].y)
                   - cverts[0].y * (cverts[1].x * cverts[3].z - cverts[1].z * cverts[3].x)
                   + cverts[0].z * (cverts[1].x * cverts[3].y - cverts[1].y * cverts[3].x));
      BigRat cd3 =  (cverts[0].x * (cverts[1].y * cverts[2].z - cverts[1].z * cverts[2].y)
                   - cverts[0].y * (cverts[1].x * cverts[2].z - cverts[1].z * cverts[2].x)
                   + cverts[0].z * (cverts[1].x * cverts[2].y - cverts[1].y * cverts[2].x));
      BigRat cdet = cd0 + cd1 + cd2 + cd3;
      BigRat b = cdet / det;
      if (b < 0) {
        all_valid = false;
        std::cout << "Target " << k << ", coord " << j << " is NEGATIVE: " << b.ToDouble() << "\n";
      }
    }
  }

  if (all_valid) {
    std::cout << "ALL 6 OCTAHEDRON TARGETS ARE STRICTLY INSIDE THE TETRAHEDRON!\n";
  } else {
    std::cout << "Some target is outside.\n";
  }

  return 0;
}
