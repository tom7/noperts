#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string parent = "03121303200";
  for (int c = 0; c < 4; c++) {
    std::string child = parent + std::to_string(c);
    TriangleQ tri = TriangleFromPath(child);
    std::cout << "Testing child " << child << "...\n";

    // 1. Standard certificate
    TubeCertificate cert;
    if (Tube229::SynthesizeCertificate(tri, child.size(), &cert)) {
      std::cout << "  Child " << child << ": STANDARD CAGE SUCCESS!\n";
      continue;
    }

    // 2. Decomposed certificate
    DecomposedCertificate dcert;
    if (Tube229::SynthesizeDecomposedCertificate(tri, child.size(), &dcert)) {
      std::cout << "  Child " << child << ": DECOMPOSED CAGE SUCCESS!\n";
      continue;
    }

    std::cout << "  Child " << child << ": Neither standard nor decomposed found by default synthesizer.\n";
  }
  return 0;
}
