#include <iostream>
#include <cmath>

int main() {
  double B0 = 1.3966; // 279323947 / 200000000
  double D0 = 2.02e-7;
  double r = 1.0 / 2000.0; // 0.0005
  double delta = 3.33e-7;

  for (double c_cone : {0.015, 0.020, 0.025, 0.030, 0.035, 0.040}) {
    double num = 0.5 * r * r * B0 + D0;
    double den = (c_cone - delta) * B0 * std::sqrt(1.0 - 0.25 * r * r);
    double r_min = num / den;
    double c_core_req = delta + r_min / std::sqrt(4.0 - r_min * r_min);
    std::cout << "c_cone = " << c_cone << ": r_min = " << r_min
              << ", req c_core = " << c_core_req << "\n";
  }
  return 0;
}
