#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::vector<std::string> canyon = {
    "0312130332"
  };

  for (const auto &path : canyon) {
    std::cout << "\n================ Checking children of " << path << " ================\n";
    for (int c = 0; c < 4; c++) {
      std::string child = path + std::to_string(c);
      TriangleQ tri = TriangleFromPath(child);
      tubetree229::TubeCertificate cert;
      if (Tube229::SynthesizeCertificate(tri, child.size() - 1, &cert)) {
        std::cout << "Child " << child << ": CERTIFIED! (c=" << cert.c.ToDouble()
                  << ", r=" << cert.r.ToDouble() << ")\n";
      } else {
        std::cout << "Child " << child << ": failed standard synthesis.\n";
      }


    }
  }
  return 0;
}
