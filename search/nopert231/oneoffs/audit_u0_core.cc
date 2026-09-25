#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);
  ContactInfo c2 = MakeContact(14, 15, 15, 19, 400, 15);
  ContactInfo cts[3] = {c0, c1, c2};

  AxisCertificate ax;
  BigVecQ3 ctr;
  BigRat del;
  std::string err;
  bool ok = Tube229::AuditAxis(tri, cts, &ax, &ctr, &del, &err, BigRat(0));
  std::cout << "Audit with defect 0: " << (ok ? "SUCCESS" : "FAILED") << "\n";
  if (!ok) {
    std::cout << "Error: " << err << "\n";
    // try with small margin
    ok = Tube229::AuditAxis(tri, cts, &ax, &ctr, &del, &err, BigRat(1, 1000));
    std::cout << "Audit with defect 1/1000: " << (ok ? "SUCCESS" : "FAILED") << "\n";
    if (!ok) std::cout << "Error: " << err << "\n";
  }

  std::cout << "ax.B = " << ax.B.ToString() << "\n";
  std::cout << "center = (" << ctr.x.ToString() << ", " << ctr.y.ToString() << ", " << ctr.z.ToString() << ")\n";
  std::cout << "delta = " << del.ToString() << " (" << del.ToDouble() << ")\n";
  std::cout << "nonzero_witness = (" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << ")\n";

  return 0;
}
