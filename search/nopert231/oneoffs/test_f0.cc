#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "tubecert229.h"

int main() {
  TubeCertManager mgr;
  mgr.target_c = BigRat(6, 100000);
  mgr.tube_radius = BigRat(1, 10000);
  mgr.max_depth = 28;

  TriangleQ tri;
  tri.corners[0] = Vec3Q("6719481/10747904", "1491999/10747904", "7733/32768");
  tri.corners[1] = Vec3Q("3440374267/5502926848", "1527806945/11005853696", "63348737/268435456");
  tri.corners[2] = Vec3Q("6880748575/11005853696", "1527806945/11005853696", "7733/32768");

  ProjectiveLocalCert cert;
  bool ok = mgr.SynthesizeCertificate(tri, 28, &cert);
  std::cout << "SynthesizeCertificate on f0: " << (ok ? "SUCCESS" : "FAIL") << "\n";
  if (ok) {
    std::cout << "c = " << cert.c.ToString() << " (" << (double)cert.c.num / cert.c.den << ")\n";
  }
  return 0;
}
