#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213030221";
  std::cout << "Testing iterative synthesis on " << path << "...\n";
  TriangleQ tri = TriangleFromPath(path);
  TubeCertificate cert;
  bool ok = Tube229::SynthesizeCertificate(tri, path.size(), &cert, {}, {}, /*fast_only=*/false);
  std::cout << "Result: " << (ok ? "SUCCESS!" : "FAILED") << "\n";
  if (ok) {
    std::cout << "  c = " << cert.c.ToString() << "\n";
    std::cout << "  r = " << cert.r.ToString() << "\n";
  }
  return 0;
}
