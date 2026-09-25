#include <iostream>
#include <iomanip>
#include <cmath>

int main() {
  double A = 0.002611042836;
  double B_w = 0.0002947480404;
  double lam = 0.5235565382;
  double c_core = 0.00005;

  std::cout << std::setprecision(10);
  for (double c = 0.0270; c <= 0.0290; c += 0.0002) {
    double lhs = B_w * (A - c * c);
    double term = lam * c - c_core;
    double rhs = A * term * term;
    std::cout << "c_cone = " << c << " -> diff = " << (rhs - lhs) << "\n";
  }
  return 0;
}
