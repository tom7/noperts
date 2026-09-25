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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

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
  BigVecQ3 u0 = {center0.x / ax0.B, center0.y / ax0.B, center0.z / ax0.B};

  // 3 complement axes from test_annulus_coverage:
  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  BigVecQ3 u[4];
  u[0] = u0;
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, comp[i], &ax, &ctr, &del, &err, BigRat(0));
    u[i + 1] = {ctr.x / ax.B, ctr.y / ax.B, ctr.z / ax.B};
  }

  std::cout << "Testing 4-axis cage inradius...\n";
  BigRat inrad = Tube229::ExactTetrahedronAxisRadius(u);
  std::cout << "Exact inradius of 4 axes: " << inrad.ToDouble() << "\n";

  // Check octahedron targets with margin c = 0.005:
  BigRat c(5, 1000);
  BigRat target_scale = c * BigRat(7, 4);
  std::cout << "Target scale (7/4 * c): " << target_scale.ToDouble() << "\n";
  if (inrad >= target_scale) {
    std::cout << "SUCCESS! 4 axes ALREADY contain the octahedron of radius c = 0.005!\n";
  } else {
    std::cout << "Inradius " << inrad.ToDouble() << " < " << target_scale.ToDouble() << "\n";
  }

  return 0;
}
