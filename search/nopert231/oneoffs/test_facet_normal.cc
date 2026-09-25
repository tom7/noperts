#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  vec3 a1 = {-0.0223153528, 0.01633519888, 0.02078657685};
  vec3 a2 = {-0.007629584745, -0.01429285093, 0.01570535306};
  vec3 a3 = {0.008923452355, 0.02328151249, 0.004312773062};

  vec3 n = yocto::cross(a2 - a1, a3 - a1);
  n = yocto::normalize(n);

  double d = yocto::dot(n, a1);
  std::cout << "Normal to face (1,2,3): (" << n.x << ", " << n.y << ", " << n.z << ")\n";
  std::cout << "Distance of plane from origin: d = " << d << "\n";

  vec3 uncov = {0.401011, -0.483067, -0.778355};
  uncov = yocto::normalize(uncov);
  std::cout << "dot(n, uncov) = " << yocto::dot(n, uncov) << "\n";

  return 0;
}
