#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::cout << "Testing mixes on contact 2:\n";
  for (int mix = 0; mix <= 1000; mix += 50) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, mix, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
      std::cout << "mix = " << mix << " PASSED ZERO DEFECT! delta = " << del.ToDouble() << "\n";
    }
  }

  std::cout << "\nNow testing all contacts from silhouette for contact 2 with BigRat(0):\n";
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});
  for (size_t ci = 0; ci < contacts.size(); ci++) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      contacts[ci]
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
      std::cout << "Contact " << ci << " (" << (int)contacts[ci].vertex << ", mix=" << contacts[ci].mix
                << ") PASSED ZERO DEFECT! delta = " << del.ToDouble() << "\n";
    }
  }

  return 0;
}
