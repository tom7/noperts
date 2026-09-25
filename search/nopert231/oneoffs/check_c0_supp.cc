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
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };

  std::string err;
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat del0;

  bool ok = Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(5, 1000));
  std::cout << "AuditAxis ok: " << ok << ", err: " << err << "\n";
  std::cout << "B0 = " << ax0.B.ToString() << " (" << ax0.B.ToDouble() << ")\n";

  // Check support upper over all 24 vertices for each contact
  BigRat max_supp[3] = {0, 0, 0};
  for (int m = 0; m < 3; m++) {
    for (int k = 0; k < 24; k++) {
      BigRat s = Tube229::SupportUpper(tri, c0[m], k);
      if (s > max_supp[m]) max_supp[m] = s;
    }
    std::cout << "Contact " << m << " max s_upper = " << max_supp[m].ToString() << " (" << max_supp[m].ToDouble() << ")\n";
  }

  // Weight upper for each contact:
  // WeightUpper = dot(cnt0, n_m) / ...
  // Or in Lean: box.weightUpper 0 m
  return 0;
}
