#include <iostream>
#include <iomanip>
#include <cmath>

int main() {
  // From test_full_box_03121303200
  double lam = 2.291864986; // lam = 1733... / 7562...
  // Let's compute exact values:
  // lam * c_cone - c_core
  std::cout << std::setprecision(10);
  for (double c_cone = 0.015; c_cone <= 0.045; c_cone += 0.005) {
    double c_core = 0.0003;
    double margin = lam * c_cone - c_core;
    std::cout << "c_cone=" << c_cone << " margin=" << margin << "\n";
  }
  return 0;
}
