#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  for (int mix : {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000}) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, mix, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    bool ok = Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000));
    std::cout << "mix " << mix << ": ok=" << ok << ", delta=" << del.ToDouble() << ", B=" << ax.B.ToDouble() << "\n";
  }
  return 0;
}
