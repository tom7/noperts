#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::vector<std::string> paths = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  for (const auto &p : paths) {
    TriangleQ tri = TriangleFromPath(p);
    TubeCertificate cert;
    std::cout << "Testing path " << p << " (depth " << p.size() << ")...\n";
    if (Tube229::SynthesizeCertificateIterative(tri, p.size(), &cert, {}, {}, 10)) {
      std::cout << "  SUCCESS! c = " << cert.c.ToString() << " (" << cert.c.ToDouble()
                << "), r = " << cert.r.ToString() << " (" << cert.r.ToDouble() << ")\n";
    } else {
      std::cout << "  FAILED at root depth " << p.size() << "\n";
    }
  }
  return 0;
}
