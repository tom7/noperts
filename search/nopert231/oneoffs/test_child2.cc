#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string parent = "031213002";
  for (int c = 0; c < 4; c++) {
    std::string path = parent + std::to_string(c);
    TriangleQ tri = TriangleFromPath(path);
    TubeCertificate cert;
    bool ok = Tube229::SynthesizeCertificate(tri, path.size(), &cert);
    std::cout << "Path " << path << ": " << (ok ? "SUCCESS" : "FAILED") << "\n";
  }
  return 0;
}
