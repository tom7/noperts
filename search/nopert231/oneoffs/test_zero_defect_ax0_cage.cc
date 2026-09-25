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

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  // Current cage axes 1, 2, 3:
  // ax1:
  ContactInfo c1[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 500, 15}, {3, 2, 2, 1, 0, 2} };
  // ax2:
  ContactInfo c2[3] = { {19, 3, 3, 2, 800, 3}, {15, 19, 19, 3, 800, 19}, {1, 4, 4, 8, 333, 4} };
  // ax3:
  ContactInfo c3[3] = { {2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 333, 4}, {15, 19, 19, 3, 1000, 19} };

  AxisCertificate ax1, ax2, ax3; BigVecQ3 ctr1, ctr2, ctr3; BigRat del1, del2, del3; std::string err;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  std::vector<int> candidates = {36, 37, 43, 44, 45, 46, 47};
  for (int ci : candidates) {
    ContactInfo c0[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      contacts[ci]
    };
    AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
    if (Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
      double c_cone = 0.017;
      // Test if cage (ax0, ax1, ax2, ax3) is barycentric valid at c_cone
      // We check if the octahedron is enclosed by the convex hull of the 4 centers
      // decomposedCenter 0 = u0_raw / B0
      // decomposedCenter j = (ctr_j / Bj - c_cone * u0) / (1 - c_cone)
      vec3 u0_raw = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
      vec3 u0 = yocto::normalize(u0_raw);
      vec3 v0 = u0_raw;
      vec3 v1 = (vec3{ctr1.x.ToDouble() / ax1.B.ToDouble(), ctr1.y.ToDouble() / ax1.B.ToDouble(), ctr1.z.ToDouble() / ax1.B.ToDouble()} - (float)c_cone * u0) / (1.0f - (float)c_cone);
      vec3 v2 = (vec3{ctr2.x.ToDouble() / ax2.B.ToDouble(), ctr2.y.ToDouble() / ax2.B.ToDouble(), ctr2.z.ToDouble() / ax2.B.ToDouble()} - (float)c_cone * u0) / (1.0f - (float)c_cone);
      vec3 v3 = (vec3{ctr3.x.ToDouble() / ax3.B.ToDouble(), ctr3.y.ToDouble() / ax3.B.ToDouble(), ctr3.z.ToDouble() / ax3.B.ToDouble()} - (float)c_cone * u0) / (1.0f - (float)c_cone);

      // Check determinant of tetrahedron (v1-v0, v2-v0, v3-v0)
      vec3 d1 = v1 - v0;
      vec3 d2 = v2 - v0;
      vec3 d3 = v3 - v0;
      double det = yocto::dot(d1, yocto::cross(d2, d3));
      std::cout << "Candidate " << ci << " (vertex " << (int)contacts[ci].vertex << ", mix=" << contacts[ci].mix
                << "): det = " << det << ", del0 = " << del0.ToDouble() << "\n";
    }
  }

  return 0;
}
