#include <iostream>
#include <vector>
#include <array>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Loaded " << hull_axes.size() << " zero-defect hull support axes.\n";

  std::vector<vec3> pts;
  for (const auto &ax : hull_axes) {
    pts.push_back({
      ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
      ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
      ax.center.z.ToDouble() / ax.cert.B.ToDouble()
    });
  }

  std::array<int, 4> simplex;
  if (Tube229::FindExtremalTetrahedron(pts, &simplex)) {
    std::cout << "SUCCESS! FindExtremalTetrahedron found enclosing simplex: ["
              << simplex[0] << ", " << simplex[1] << ", " << simplex[2] << ", " << simplex[3]
              << "]!\n";

    TubeCertificate cert;
    cert.symmetry_index = 0;
    cert.delta = BigRat(1, 10000000);
    for (int a = 0; a < 4; a++) cert.axes[a] = hull_axes[simplex[a]].cert;

    TubeCertificate out_cert;
    std::string fail;
    if (Tube229::AuditCertificateAdaptive(tri, cert, &out_cert, &fail)) {
      std::cout << "EXACT AUDIT SUCCESS!\n";
      std::cout << "  c = " << out_cert.c.ToString() << " (" << out_cert.c.ToDouble() << ")\n";
      std::cout << "  r = " << out_cert.r.ToString() << " (" << out_cert.r.ToDouble() << ")\n";
    } else {
      std::cout << "Exact audit failed: " << fail << "\n";
    }
  } else {
    std::cout << "FindExtremalTetrahedron failed to enclose origin.\n";
  }

  return 0;
}
