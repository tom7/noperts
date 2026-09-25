#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  // Original Axis 0 contacts:
  // c[0]: (3, 2, 2, 1, 800, 2)
  // c[1]: (1, 4, 4, 8, 800, 4)
  // c[2]: was (13, 14, 14, 15, 200, 14)

  // Now test c[2] using true hull edges at v10, v15:
  // Edge (10 -> 15) and (15 -> 19) at vertex 15!
  // Or edge (9 -> 10) and (10 -> 15) at vertex 10!
  std::vector<ContactInfo> c2_candidates = {
    MakeContact(10, 15, 15, 19, 1000, 15),
    MakeContact(10, 15, 15, 19, 800, 15),
    MakeContact(10, 15, 15, 19, 500, 15),
    MakeContact(10, 15, 15, 19, 200, 15),
    MakeContact(10, 15, 15, 19, 0, 15),
    MakeContact(9, 10, 10, 15, 1000, 10),
    MakeContact(9, 10, 10, 15, 800, 10),
    MakeContact(9, 10, 10, 15, 500, 10),
    MakeContact(9, 10, 10, 15, 200, 10),
    MakeContact(9, 10, 10, 15, 0, 10)
  };

  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);

  vec3 u0 = {-0.01389, 0.01857, -0.06689};

  for (size_t i = 0; i < c2_candidates.size(); i++) {
    ContactInfo contacts[3] = {c0, c1, c2_candidates[i]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      vec3 v = ToDouble(center);
      double dot = yocto::dot(yocto::normalize(v), yocto::normalize(u0));
      double angle = acos(std::min(1.0, std::max(-1.0, dot))) * 180.0 / M_PI;
      std::cout << "Candidate " << i << ": SUCCESS! Angle to u0 = " << angle
                << " deg, dot = " << dot
                << ", center = (" << v.x << ", " << v.y << ", " << v.z << ")\n";
    } else {
      std::cout << "Candidate " << i << ": failed: " << err << "\n";
    }
  }

  return 0;
}
