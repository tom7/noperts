#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string root_path = "031213002112122012121";
  std::cout << "Testing children of " << root_path << "...\n";

  // Check depths 22, 23
  std::vector<std::string> current = {root_path};

  for (int d = 22; d <= 24; d++) {
    std::vector<std::string> next;
    int cert_count = 0;
    int uncert_count = 0;
    std::vector<std::string> uncert;

    for (const auto &p : current) {
      for (char c : {'0', '1', '2', '3'}) {
        std::string child = p + c;
        TriangleQ tri = TriangleFromPath(child);
        TubeCertificate cert;
        if (Tube229::SynthesizeCertificateFast(tri, d, &cert) ||
            Tube229::SynthesizeCertificateIterative(tri, d, &cert)) {
          cert_count++;
        } else {
          uncert_count++;
          uncert.push_back(child);
        }
      }
    }
    std::cout << "Depth " << d << ": certified " << cert_count << ", uncertified " << uncert_count << "\n";
    if (uncert.empty()) {
      std::cout << "ALL CELLS FULLY CERTIFIED AT DEPTH " << d << "!\n";
      break;
    }
    current = uncert;
  }
  return 0;
}
