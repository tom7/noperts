#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string p = "031213002112122012121";
  for (int depth = 21; depth <= 30; depth++) {
    TriangleQ parent = TriangleFromPath(p);
    TriangleQ children[4];
    parent.Subdivide(children);
    int uncert = -1;
    int uncert_count = 0;
    for (int c = 0; c < 4; c++) {
      TubeCertificate cert;
      bool ok = Tube229::SynthesizeCertificate(children[c], depth + 1, &cert);
      if (!ok) {
        ok = Tube229::SynthesizeCertificateIterative(children[c], depth + 1, &cert);
      }
      if (!ok) {
        uncert = c;
        uncert_count++;
      }
    }
    std::cout << "Depth " << depth << " -> " << (depth + 1) << ": "
              << (4 - uncert_count) << "/4 children certified. ";
    if (uncert_count == 0) {
      std::cout << "ENTIRE BRANCH FULLY CERTIFIED!\n";
      break;
    } else if (uncert_count == 1) {
      std::cout << "Only child " << uncert << " uncertified.\n";
      p += std::to_string(uncert);
    } else {
      std::cout << uncert_count << " children uncertified. Stopping.\n";
      break;
    }
  }

  return 0;
}
