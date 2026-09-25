#include <iostream>
#include <vector>
#include <cmath>
#include "yocto-math.h"

using namespace yocto;
using vec3 = yocto::vec<double, 3>;

int main() {
  vec3 u0 = vec3{
    -0.014005246023101735, 0.01856363064827298, -0.06749935440408464
  };
  double norm_u0 = length(u0);
  vec3 u0_hat = normalize(u0);
  vec3 k1 = normalize(cross(u0_hat, std::abs(u0_hat.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = cross(u0_hat, k1);

  vec3 v[4] = {
    vec3{-0.00764242, 0.0131556, -0.0121004},  // flockAx0
    vec3{-0.061778, -0.006180, -0.028006},    // flockAx1
    vec3{0.070451, -0.006189, 0.040142},      // flockAx2
    vec3{-0.022222, -0.015979, -0.001545}     // flockAx3
  };

  std::cout << "Basis:" << "\n";
  std::cout << "u0_hat = (" << u0_hat.x << ", " << u0_hat.y << ", " << u0_hat.z << ")\n";
  std::cout << "k1 = (" << k1.x << ", " << k1.y << ", " << k1.z << ")\n";
  std::cout << "k2 = (" << k2.x << ", " << k2.y << ", " << k2.z << ")\n";

  for (int m = 0; m < 4; m++) {
    double c1 = dot(v[m], k1);
    double c2 = dot(v[m], k2);
    double c0 = dot(v[m], u0_hat);
    std::cout << "v" << m << ": c1(k1) = " << c1 << ", c2(k2) = " << c2 << ", c0(u0_hat) = " << c0 << "\n";
  }

  return 0;
}
