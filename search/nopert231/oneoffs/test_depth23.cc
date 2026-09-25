#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string p = "0312130021121220121212";
  TriangleQ parent = TriangleFromPath(p);
  TriangleQ children[4];
  parent.Subdivide(children);

  std::cout << "Testing 4 children of leaf " << p << " at depth 23:\n";
  for (int c = 0; c < 4; c++) {
    std::string child_p = p + std::to_string(c);
    TubeCertificate cert;
    bool ok = Tube229::SynthesizeCertificate(children[c], 23, &cert);
    if (!ok) {
      ok = Tube229::SynthesizeCertificateIterative(children[c], 23, &cert);
    }
    std::cout << "Child " << c << " (" << child_p << "): "
              << (ok ? "CERTIFIED!" : "FAILED") << "\n";
    if (ok) {
      std::cout << "  r = " << cert.r.ToString() << " (" << cert.r.ToDouble() << ")\n";
      std::cout << "  c = " << cert.c.ToString() << " (" << cert.c.ToDouble() << ")\n";
    }
  }

  return 0;
}
