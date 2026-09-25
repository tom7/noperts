#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  // Exact corner 2
  BigVecQ3 u_star = {
    BigQ(53756867, 85983232),
    BigQ(373023, 2686976),
    BigQ(494869, 2097152)
  };

  vec3 u_f = {u_star.x.ToDouble(), u_star.y.ToDouble(), u_star.z.ToDouble()};

  // Axis 0 contact 2:
  // edge 10->15, sel=10
  ContactInfo c2 = {10, 15, 15, 19, 800, 15};
  vec3 edge = Tube229::GetDoubleEdge(c2);
  int sel = c2.vertex;

  std::cout << std::setprecision(15);
  std::cout << "Testing all vertices k against contact 2 at u_star:\n";
  for (int k = 0; k < 20; k++) {
    if (k == sel) continue;
    vec3 delta = {
      (Tube229::VertexQ(k).x - Tube229::VertexQ(sel).x).ToDouble(),
      (Tube229::VertexQ(k).y - Tube229::VertexQ(sel).y).ToDouble(),
      (Tube229::VertexQ(k).z - Tube229::VertexQ(sel).z).ToDouble()
    };
    vec3 coeff = yocto::cross(edge, delta);
    double d = yocto::dot(u_f, coeff);
    if (d > -1e-5) {
      std::cout << "  k=" << k << ": dot = " << d << "\n";
    }
  }

  return 0;
}
