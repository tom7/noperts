#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213002112122012121";

  for (int depth = 21; depth <= 35; depth++) {
    TriangleQ tri = TriangleFromPath(path);
    TubeCertificate cert;

    bool ok = Tube229::SynthesizeCertificateFast(tri, depth, &cert) ||
              Tube229::SynthesizeCertificateIterative(tri, depth, &cert);
    std::cout << "Depth " << depth << " (" << path << "): StandardCert = " << (ok ? "YES!" : "no") << "\n";
    if (ok) {
      std::cout << "FOUND FULL STANDARD CERTIFICATION AT DEPTH " << depth << "!\n";
      break;
    }
    path += "2";
  }
  return 0;
}
