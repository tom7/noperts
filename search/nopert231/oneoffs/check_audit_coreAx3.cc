#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c_100300[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 300, 14}
  };
  AxisCertificate ax_sib; BigVecQ3 ctr_sib; BigRat del_sib; std::string err;
  bool ok = Tube229::AuditAxis(tri, c_100300, &ax_sib, &ctr_sib, &del_sib, &err, BigRat(1, 1000));
  std::cout << "AuditAxis ok = " << ok << ", err = " << err << "\n";
  std::cout << "delta = " << del_sib.ToDouble() << "\n";
  std::cout << "contacts vertex = " << c_100300[0].vertex << ", "
            << c_100300[1].vertex << ", " << c_100300[2].vertex << "\n";

  // Let us inspect the support values for this axis:
  // AuditAxis computed nonzero_witness:
  std::cout << "nonzero_witness = " << (int)ax_sib.nonzero_witness[0] << ", "
            << (int)ax_sib.nonzero_witness[1] << ", "
            << (int)ax_sib.nonzero_witness[2] << "\n";
  return 0;
}
