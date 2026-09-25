#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::vector<std::pair<std::string, BigRat>> nodes = {
    {"03121300", BigRat(219, 1000000)},     // 2.19e-4
    {"03121303021", BigRat(597, 10000000)}, // 5.97e-5
    {"03121303022", BigRat(771, 100000000)},// 7.71e-6
    {"03121303023", BigRat(771, 100000000)},// 7.71e-6
    {"03121303200", BigRat(735, 10000000)}, // 7.35e-5
    {"0312130332", BigRat(192, 1000000)}    // 1.92e-4
  };

  ContactInfo cont0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  for (const auto &item : nodes) {
    std::string target = item.first;
    BigRat D0 = item.second;
    TriangleQ tri = TriangleFromPath(target);

    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    Tube229::AuditAxis(tri, cont0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
    BigRat B0 = ax0.B;

    bool found = false;
    for (int c_cone_num : {4, 5, 6, 7, 8}) {
      BigRat c_cone(c_cone_num, 1000);
      for (int r_denom = 50; r_denom <= 1000; r_denom += 25) {
        BigRat r(1, r_denom);
        for (int r_min_denom = r_denom + 10; r_min_denom <= 2000; r_min_denom += 25) {
          BigRat r_min(1, r_min_denom);

          BigRat lhs_term = BigRat(1, 2) * r * r * B0 + D0;
          BigRat lhs = lhs_term * lhs_term;
          BigRat rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) *
                       (c_cone - delta0) * (c_cone - delta0) * B0 * B0;

          if (lhs <= rhs) {
            std::cout << "Node " << target << ": FOUND! c_cone = " << c_cone.ToString()
                      << " r = 1/" << r_denom << " r_min = 1/" << r_min_denom
                      << " margin = " << (rhs - lhs).ToDouble() << "\n";
            found = true;
            break;
          }
        }
        if (found) break;
      }
      if (found) break;
    }
    if (!found) {
      std::cout << "Node " << target << ": No solution found with c_cone <= 0.008 (D0 = "
                << D0.ToDouble() << ", delta0 = " << delta0.ToDouble() << ")\n";
    }
  }

  return 0;
}
