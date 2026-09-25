#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <memory>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  // Base verified sibling axes with cert_hull as Axis 3
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

  // Replace Axis 3 with cert_hull (contacts 2, 4, 15)
  base_sib.axes[3].contacts[0] = {3, 2, 2, 1, 800, 2};
  base_sib.axes[3].contacts[1] = {1, 4, 4, 8, 800, 4};
  base_sib.axes[3].contacts[2] = {10, 15, 15, 19, 800, 15};

  std::string canyon_path = "03121303021";
  std::cout << "\n=== Testing canyon ancestor chain from depth 11 down to 7 ===\n";

  for (int len = 11; len >= 7; len--) {
    std::string p = canyon_path.substr(0, len);
    TriangleQ tri = TriangleFromPath(p);
    std::cout << "Depth " << len << " (" << p << "):\n";
    // Test with base_sib
    {
      DecomposedCertificate dc;
      std::string fail;
      bool ok = Tube229::SynthesizeDecomposedCertificate(tri, len, &dc, &base_sib, &fail);
      std::cout << "  With base_sib: " << (ok ? "SUCCESS!" : ("FAIL: " + fail)) << "\n";
      if (ok) {
        std::cout << "    r_min  = " << dc.r_min.ToString() << " (" << dc.r_min.ToDouble() << ")\n"
                  << "    r      = " << dc.r.ToString() << " (" << dc.r.ToDouble() << ")\n"
                  << "    c_cone = " << dc.c_cone.ToString() << " (" << dc.c_cone.ToDouble() << ")\n"
                  << "    c_comp = " << dc.c_comp.ToString() << " (" << dc.c_comp.ToDouble() << ")\n"
                  << "    delta  = " << dc.delta.ToString() << "\n";
      }
    }
  }

  return 0;
}
