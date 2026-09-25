#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));

  std::vector<int> flock = {3063, 389, 3449, 213, 25};
  std::vector<BigVecQ3> v(5);
  for (int m = 0; m < 5; m++) {
    const auto &ax = axes[flock[m]];
    v[m].x = ax.center.x / ax.cert.B;
    v[m].y = ax.center.y / ax.cert.B;
    v[m].z = ax.center.z / ax.cert.B;
  }

  // u0_hat, k1, k2 in exact rational or approx:
  // Let's compute origin (0, 0, 0) first: does convex hull contain the origin?
  BigVecQ3 origin{BigRat(0), BigRat(0), BigRat(0)};

  // Check all subsets of 4 vectors
  int combos[5][4] = {
    {0, 1, 2, 3},
    {0, 1, 2, 4},
    {0, 1, 3, 4},
    {0, 2, 3, 4},
    {1, 2, 3, 4}
  };

  for (int c = 0; c < 5; c++) {
    BigRat w[4];
    bool ok = Tube229::SolveTetraBarycentricQ(v[combos[c][0]], v[combos[c][1]], v[combos[c][2]], v[combos[c][3]], origin, w);
    std::cout << "Combo " << c << ": ok=" << ok << ", weights: "
              << w[0].ToDouble() << ", " << w[1].ToDouble() << ", "
              << w[2].ToDouble() << ", " << w[3].ToDouble() << "\n";
  }

  return 0;
}
