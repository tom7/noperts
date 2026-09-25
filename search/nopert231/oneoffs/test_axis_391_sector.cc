#include <iostream>
#include <cmath>

double MinCos(double ph0, double ph1, double psi) {
  double a0 = ph0 - psi;
  double a1 = ph1 - psi;
  if (a1 - a0 >= 2 * M_PI) return -1.0;
  double k0 = std::ceil((a0 - M_PI) / (2 * M_PI));
  double k1 = std::floor((a1 - M_PI) / (2 * M_PI));
  if (k0 <= k1) return -1.0;
  return std::min(std::cos(a0), std::cos(a1));
}

double MinTrigCombo(double th0, double th1, double lam, double C) {
  double min_val = std::min(lam * std::cos(th0) + C * std::sin(th0),
                            lam * std::cos(th1) + C * std::sin(th1));
  double th_crit = std::atan2(C, lam);
  double th_crit_min = th_crit + M_PI;
  while (th_crit_min > th1) th_crit_min -= 2 * M_PI;
  while (th_crit_min < th0) th_crit_min += 2 * M_PI;
  if (th_crit_min >= th0 && th_crit_min <= th1) {
    min_val = std::min(min_val, lam * std::cos(th_crit_min) + C * std::sin(th_crit_min));
  }
  return min_val;
}

int main() {
  double th0 = 48.6725 * M_PI / 180.0;
  double th1 = 58.407 * M_PI / 180.0;
  double ph0 = 315.0 * M_PI / 180.0;
  double ph1 = 326.25 * M_PI / 180.0;

  double lam = -0.656366;
  double mu = 0.754442;
  double psi = -94.3879 * M_PI / 180.0;

  double min_c = MinCos(ph0, ph1, psi);
  std::cout << "min_cos = " << min_c << "\n";
  double min_v = MinTrigCombo(th0, th1, lam, mu * min_c);
  std::cout << "MinTrigCombo = " << min_v << "\n";

  // Check the 4 corners directly:
  auto f = [&](double th, double ph) {
    return lam * std::cos(th) + mu * std::sin(th) * std::cos(ph - psi);
  };
  std::cout << "Corner (th0, ph0): " << f(th0, ph0) << "\n";
  std::cout << "Corner (th0, ph1): " << f(th0, ph1) << "\n";
  std::cout << "Corner (th1, ph0): " << f(th1, ph0) << "\n";
  std::cout << "Corner (th1, ph1): " << f(th1, ph1) << "\n";

  return 0;
}
