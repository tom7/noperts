#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static void PrintBary(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 &p, int k) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  vec3 dp = p - v3;
  double b0 = Det3(dp, d1, d2) / d;
  double b1 = Det3(d0, dp, d2) / d;
  double b2 = Det3(d0, d1, dp) / d;
  double b3 = 1.0 - b0 - b1 - b2;
  double min_b = std::min(std::min(b0, b1), std::min(b2, b3));
  std::cout << "Target " << k << ": min_b = " << min_b
            << " (b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << ")\n";
}

int main() {
  vec3 u0 = {-0.01389, 0.01857, -0.06689};
  double c_cone = 0.038;
  double c = 0.00001;
  double delta = 4e-7;
  double scale = (c + delta) / c_cone;
  vec3 v0 = scale * u0;

  // Let's test the original pack complement axes from row 3253:
  vec3 v1 = {0.03366, 0.02832, 0.00448};
  vec3 v2 = {0.07003, -0.000639, 0.04024};
  vec3 v3 = {-0.07204, -0.000736, -0.02562};

  double R_target = 1.75 * (c + delta);
  vec3 targets[6] = {
    {+R_target, 0, 0},
    {-R_target, 0, 0},
    {0, +R_target, 0},
    {0, -R_target, 0},
    {0, 0, +R_target},
    {0, 0, -R_target}
  };

  std::cout << "v0 = (" << v0.x << ", " << v0.y << ", " << v0.z << "), norm=" << yocto::length(v0) << "\n";
  std::cout << "R_target = " << R_target << "\n";

  for (int k = 0; k < 6; k++) {
    PrintBary(v0, v1, v2, v3, targets[k], k);
  }
  return 0;
}
