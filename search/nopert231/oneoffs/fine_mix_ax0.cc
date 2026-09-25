#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  double min_max_defect = 1e9;
  int best_mix = -1;

  for (int mix = 0; mix <= 1000; mix += 10) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, mix, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (!Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) continue;

    // Check defect on all 24 vertices
    // We can evaluate supportUpper in C++ using the formula:
    // supportUpper i k = max dot product over interval + error
    // Let's print del
    if (mix >= 150 && mix <= 250) {
      std::cout << "mix = " << mix << ", del = " << del.ToDouble() << ", B = " << ax.B.ToDouble() << "\n";
    }
  }
  return 0;
}
