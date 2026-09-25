#include <iostream>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  vec3 omega_obs = {-0.400992, 0.483041, 0.778381};
  vec3 neg_omega = -omega_obs;

  // Idea 3 cert_hull:
  // Contact 0: edge (3->2)/(2->1), mix=800, vertex=2
  // Contact 1: edge (1->4)/(4->8), mix=800, vertex=4
  // Contact 2: edge (10->15)/(15->19), mix=800, vertex=15
  ContactInfo triple[3] = {
    {.edge_start = 3, .edge_finish = 2, .edge_start2 = 2, .edge_finish2 = 1, .mix = 800, .vertex = 2},
    {.edge_start = 1, .edge_finish = 4, .edge_start2 = 4, .edge_finish2 = 8, .mix = 800, .vertex = 4},
    {.edge_start = 10, .edge_finish = 15, .edge_start2 = 15, .edge_finish2 = 19, .mix = 800, .vertex = 15}
  };

  for (const std::string &path : {"3121300"}) {
    TriangleQ tri = TriangleFromPath(path);
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    bool ok = Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &fail);
    std::cout << "Path " << path << ":\n";
    std::cout << "  AuditAxis ok: " << (ok ? "YES" : "NO") << " (fail: " << fail << ")\n";
    if (ok) {
      vec3 c = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
      vec3 u = yocto::normalize(c);
      std::cout << "  Center: (" << c.x << ", " << c.y << ", " << c.z << ")\n";
      std::cout << "  Normalized: (" << u.x << ", " << u.y << ", " << u.z << ")\n";
      std::cout << "  dot(u, -omega): " << yocto::dot(u, neg_omega) << "\n";
      std::cout << "  dot(u,  omega): " << yocto::dot(u, omega_obs) << "\n";
      std::cout << "  B: " << cert.B.ToString() << " (" << cert.B.ToDouble() << ")\n";
      std::cout << "  delta: " << delta.ToString() << " (" << delta.ToDouble() << ")\n";
    }
  }

  return 0;
}
