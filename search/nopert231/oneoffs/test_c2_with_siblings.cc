#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  // Sibling axes 1, 2, 3:
  AxisCertificate axes[4];
  ContactInfo c1[3] = {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}};
  ContactInfo c2[3] = {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}};
  ContactInfo c3[3] = {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}};
  // Candidate 2:
  ContactInfo c0[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {10, 15, 15, 19, 500, 15}};

  BigVecQ3 centers[4];
  BigRat deltas[4];
  std::string err;

  Tube229::AuditAxis(tri, c0, &axes[0], &centers[0], &deltas[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, c1, &axes[1], &centers[1], &deltas[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &axes[2], &centers[2], &deltas[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &axes[3], &centers[3], &deltas[3], &err, BigRat(0));

  vec3 pts[4];
  for (int a = 0; a < 4; a++) {
    pts[a] = {centers[a].x.ToDouble() / axes[a].B.ToDouble(),
              centers[a].y.ToDouble() / axes[a].B.ToDouble(),
              centers[a].z.ToDouble() / axes[a].B.ToDouble()};
    std::cout << "Axis " << a << ": (" << pts[a].x << ", " << pts[a].y << ", " << pts[a].z << ")\n";
  }

  // Check orientation / barycentric coordinates of origin:
  double V0 = yocto::dot(pts[1], yocto::cross(pts[2], pts[3]));
  double V1 = -yocto::dot(pts[0], yocto::cross(pts[2], pts[3]));
  double V2 = yocto::dot(pts[0], yocto::cross(pts[1], pts[3]));
  double V3 = -yocto::dot(pts[0], yocto::cross(pts[1], pts[2]));
  double total = V0 + V1 + V2 + V3;

  double l0 = V0 / total;
  double l1 = V1 / total;
  double l2 = V2 / total;
  double l3 = V3 / total;

  std::cout << "Barycentric coords of origin: "
            << l0 << ", " << l1 << ", " << l2 << ", " << l3 << "\n";

  if (l0 > 0 && l1 > 0 && l2 > 0 && l3 > 0) {
    std::cout << "SUCCESS! Encloses the origin with positive barycentric coordinates!\n";
    TubeCertificate test_cert;
    test_cert.symmetry_index = 0;
    test_cert.delta = BigRat(1, 1000000);
    for (int a = 0; a < 4; a++) test_cert.axes[a] = axes[a];

    TubeCertificate verified;
    if (Tube229::AuditCertificateAdaptive(tri, test_cert, &verified, &err)) {
      std::cout << "EXACT AUDIT SUCCESS! c = " << verified.c.ToString() << " (" << verified.c.ToDouble()
                << "), r = " << verified.r.ToString() << " (" << verified.r.ToDouble() << ")\n";
    } else {
      std::cout << "Exact audit failed: " << err << "\n";
    }
  } else {
    std::cout << "Does not enclose origin.\n";
  }

  return 0;
}
