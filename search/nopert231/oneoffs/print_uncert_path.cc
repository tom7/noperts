#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string p = "031213002112122012121";
  for (int d = 22; d <= 26; d++) {
    std::string next_p = "";
    for (char c : {'0', '1', '2', '3'}) {
      std::string child = p + c;
      TriangleQ tri = TriangleFromPath(child);
      TubeCertificate cert;
      if (!Tube229::SynthesizeCertificateFast(tri, d, &cert) &&
          !Tube229::SynthesizeCertificateIterative(tri, d, &cert)) {
        std::cout << "Depth " << d << " uncertified child: " << child << "\n";
        next_p = child;
      }
    }
    if (next_p == "") {
      std::cout << "All certified at depth " << d << "!\n";
      break;
    }
    p = next_p;
  }
  return 0;
}
