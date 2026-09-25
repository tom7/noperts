#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  // Corner 2
  BigVecQ3 c2 = {
    BigRat(53756867, 85983232),
    BigRat(373023, 2686976),
    BigRat(494869, 2097152)
  };
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  // Axis 1, 2, 3 from sibling n0:
  // Axis 0 replacement using edge 10->15
  TubeCertificate cert;
  cert.symmetry_index = 0;
  cert.axes[0].contacts[0] = {19, 3, 19, 3, 0, 19};
  cert.axes[0].contacts[1] = {4, 8, 4, 8, 0, 4};
  cert.axes[0].contacts[2] = {10, 15, 10, 15, 0, 10};

  // Sibling axes 1, 2, 3:
  cert.axes[1].contacts[0] = {3, 19, 3, 19, 3, 1000};
  cert.axes[1].contacts[1] = {1, 2, 1, 2, 1, 1000};
  cert.axes[1].contacts[2] = {8, 4, 8, 4, 8, 1000};

  cert.axes[2].contacts[0] = {19, 15, 19, 15, 19, 1000};
  cert.axes[2].contacts[1] = {1, 1, 4, 1, 4, 1000};
  cert.axes[2].contacts[2] = {10, 9, 10, 9, 10, 1000};

  cert.axes[3].contacts[0] = {19, 19, 3, 19, 3, 1000};
  cert.axes[3].contacts[1] = {2, 2, 1, 2, 1, 1000};
  cert.axes[3].contacts[2] = {9, 8, 9, 8, 9, 1000};

  TubeCertificate out_c;
  std::string f_msg;
  bool ok = Tube229::AuditCertificateAdaptive(tri_c2, cert, &out_c, &f_msg);
  std::cout << "Audit on Corner 2: " << (ok ? "SUCCESS!" : ("FAIL: " + f_msg)) << "\n";
  if (ok) {
    std::cout << "  r = " << out_c.r.ToString() << " (" << out_c.r.ToDouble() << ")\n";
    std::cout << "  c = " << out_c.c.ToString() << " (" << out_c.c.ToDouble() << ")\n";
  }

  return 0;
}
