#include <iostream>
#include <cmath>

int main() {
  double B0 = 0.1397; // from B0 = 349290553/2500000000 approx
  double D0 = 7.67e-6;
  double delta = 0.00016;

  std::cout << "Testing c_cone thresholds:\n";
  for (double r : {1.0/50, 1.0/80, 1.0/100, 1.0/120, 1.0/150, 1.0/180, 1.0/200, 1.0/250, 1.0/300}) {
    for (double r_min_ratio : {0.8, 0.85, 0.9, 0.95}) {
      double r_min = r * r_min_ratio;
      double geom = std::sqrt(1.0 - 0.25 * r * r);
      double min_c_cone = delta + (0.5 * r * r * B0 + D0) / (r_min * geom * B0);
      std::cout << "r = 1/" << (int)(1.0/r) << ", r_min = r*" << r_min_ratio << " -> min_c_cone = " << min_c_cone << "\n";
    }
  }
  return 0;
}
