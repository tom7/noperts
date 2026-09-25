#include <iostream>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  // Sibling axes with cert_hull as Axis 3
  TubeCertificate base_sib;
  base_sib.symmetry_index = 0;
  base_sib.delta = BigRat(333, 1000000000);
  base_sib.axes[0].contacts[0] = {3, 2, 2, 1, 800, 2};
  base_sib.axes[0].contacts[1] = {1, 4, 4, 8, 800, 4};
  base_sib.axes[0].contacts[2] = {13, 14, 14, 15, 200, 14};
  base_sib.axes[0].B = BigRat(176, 100);

  base_sib.axes[1].contacts[0] = {15, 19, 19, 3, 200, 19};
  base_sib.axes[1].contacts[1] = {2, 1, 1, 4, 200, 1};
  base_sib.axes[1].contacts[2] = {8, 9, 9, 10, 200, 9};

  base_sib.axes[2].contacts[0] = {2, 1, 1, 4, 0, 1};
  base_sib.axes[2].contacts[1] = {10, 15, 15, 19, 333, 15};
  base_sib.axes[2].contacts[2] = {10, 15, 15, 19, 0, 15};

  base_sib.axes[3].contacts[0] = {3, 2, 2, 1, 800, 2};
  base_sib.axes[3].contacts[1] = {1, 4, 4, 8, 800, 4};
  base_sib.axes[3].contacts[2] = {10, 15, 15, 19, 800, 15};

  // Test all 4 children of 03121303:
  for (int c = 0; c < 4; c++) {
    std::string path = "03121303" + std::to_string(c);
    TriangleQ tri = TriangleFromPath(path);
    DecomposedCertificate dc;
    std::string fail;
    bool ok = Tube229::SynthesizeDecomposedCertificate(tri, path.size(), &dc, &base_sib, &fail);
    std::cout << "Path " << path << ": " << (ok ? "SUCCESS" : ("FAIL: " + fail)) << "\n";
    if (ok) {
      std::cout << "  r_min=" << dc.r_min.ToString() << " r=" << dc.r.ToString()
                << " c_cone=" << dc.c_cone.ToString() << " c_comp=" << dc.c_comp.ToString()
                << " delta=" << dc.delta.ToString() << "\n";
    }
  }

  // Also test all 4 children of 03121300, 03121301, 03121302:
  for (int p_prefix = 0; p_prefix < 4; p_prefix++) {
    std::string prefix = "0312130" + std::to_string(p_prefix);
    std::cout << "\nPrefix " << prefix << ":\n";
    for (int c = 0; c < 4; c++) {
      std::string path = prefix + std::to_string(c);
      TriangleQ tri = TriangleFromPath(path);
      DecomposedCertificate dc;
      std::string fail;
      bool ok = Tube229::SynthesizeDecomposedCertificate(tri, path.size(), &dc, &base_sib, &fail);
      std::cout << "  " << path << ": " << (ok ? "SUCCESS" : ("FAIL: " + fail)) << "\n";
    }
  }

  return 0;
}
