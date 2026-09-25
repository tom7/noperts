#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::cout << "Testing Table 0 canyon node: " << target << "\n";

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  bool ok = Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(5, 1000));
  if (!ok) {
    std::cout << "AuditAxis for annular axis failed on " << target << ": " << err << "\n";
    return 1;
  }
  std::cout << "Annular axis audited successfully! delta = " << ann_del.ToString() << "\n";

  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";

  auto cands = Tube229::GenerateCandidatesForView(u0, tri, true, 4, false, 1e-12);
  std::cout << "Found " << cands.size() << " candidates for view u0 over " << target << "\n";

  int zero_defect_count = 0;
  for (const auto &c : cands) {
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    ContactInfo contacts[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      zero_defect_count++;
    }
  }
  std::cout << "Found " << zero_defect_count << " audited zero-defect axes for " << target << "\n";

  return 0;
}
