#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  vec3 a1 = {0.03379381279, 0.02838907328, 0.04474757206};
  vec3 a2 = {0.07049333531, -0.00618616607, 0.04015607051};
  vec3 a3 = {-0.07228104753, -0.007271631005, -0.02592266906};

  vec3 n = yocto::cross(a2 - a1, a3 - a1);
  n = yocto::normalize(n);
  double d = yocto::dot(n, a1);
  std::cout << "Face (1,2,3): n = (" << n.x << ", " << n.y << ", " << n.z << "), d = " << d << "\n";

  vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});
  std::cout << "dot(n, uncov) = " << yocto::dot(n, uncov) << "\n";

  return 0;
}
