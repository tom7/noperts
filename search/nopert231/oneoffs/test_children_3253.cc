#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void TestPath(const std::string &path, int max_depth) {
  TriangleQ tri = TriangleFromPath(path);
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificateFast(tri, path.size(), &cert)) {
    std::cout << path << " (depth " << path.size() << "): FAST SUCCESS!\n";
    return;
  }
  if (Tube229::SynthesizeCertificateIterative(tri, path.size(), &cert, {}, {}, 5)) {
    std::cout << path << " (depth " << path.size() << "): ITERATIVE SUCCESS!\n";
    return;
  }

  if ((int)path.size() >= max_depth) {
    std::cout << path << " (depth " << path.size() << "): UNCERTIFIED AT MAX DEPTH\n";
    return;
  }

  // Subdivide
  for (int c = 0; c < 4; c++) {
    TestPath(path + std::to_string(c), max_depth);
  }
}

int main() {
  std::cout << "Testing subtree of 03121300 to depth 12...\n";
  TestPath("03121300", 12);
  return 0;
}
