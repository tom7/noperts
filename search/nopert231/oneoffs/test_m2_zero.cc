#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 0, 14}
  };
  AxisCertificate cert;
  BigVecQ3 ctr;
  BigRat del;
  std::string err;
  bool ok = Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(1, 1000));
  std::cout << "Audit ok: " << ok << ", err: " << err << "\n";
  std::cout << "B: " << cert.B.ToString() << " (" << cert.B.ToDouble() << ")\n";
  std::cout << "delta: " << del.ToString() << " (" << del.ToDouble() << ")\n";
  std::cout << "center: (" << ctr.x.ToString() << ", " << ctr.y.ToString() << ", " << ctr.z.ToString() << ")\n";
  std::cout << "nonzero_witness: (" << cert.nonzero_witness[0] << ", " << cert.nonzero_witness[1] << ", " << cert.nonzero_witness[2] << ")\n";
  return 0;
}
