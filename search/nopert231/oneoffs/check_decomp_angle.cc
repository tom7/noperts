#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string leaf_path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(leaf_path);

  TubeCertificate sib_cert;
  sib_cert.symmetry_index = 0;
  sib_cert.delta = BigRat(333, 1000000000);
  sib_cert.axes[0].contacts[0] = {3, 2, 2, 1, 800, 2};
  sib_cert.axes[0].contacts[1] = {1, 4, 4, 8, 800, 4};
  sib_cert.axes[0].contacts[2] = {13, 14, 14, 15, 200, 14};
  sib_cert.axes[0].B = BigRat(176, 100);

  sib_cert.axes[1].contacts[0] = {15, 19, 19, 3, 200, 19};
  sib_cert.axes[1].contacts[1] = {2, 1, 1, 4, 200, 1};
  sib_cert.axes[1].contacts[2] = {8, 9, 9, 10, 200, 9};

  sib_cert.axes[2].contacts[0] = {2, 1, 1, 4, 0, 1};
  sib_cert.axes[2].contacts[1] = {10, 15, 15, 19, 333, 15};
  sib_cert.axes[2].contacts[2] = {10, 15, 15, 19, 0, 15};

  sib_cert.axes[3].contacts[0] = {3, 2, 2, 1, 800, 2};
  sib_cert.axes[3].contacts[1] = {4, 8, 8, 9, 800, 8};
  sib_cert.axes[3].contacts[2] = {14, 15, 15, 19, 800, 15};

  DecomposedCertificate decomp;
  std::string fail;
  if (!Tube229::SynthesizeDecomposedCertificate(tri, leaf_path.size(), &decomp, &sib_cert, &fail)) {
    std::cout << "Failed: " << fail << "\n";
    return 1;
  }

  // Get centers
  BigVecQ3 core_ctr;
  BigRat core_del;
  bool ok_core = Tube229::AuditAxis(tri, decomp.inner_core_axis.contacts, &decomp.inner_core_axis, &core_ctr, &core_del, &fail);
  std::cout << "Audit core axis: " << (ok_core ? "ok" : "fail: " + fail) << "\n";
  std::cout << "core_ctr: (" << core_ctr.x.ToDouble() << ", " << core_ctr.y.ToDouble() << ", " << core_ctr.z.ToDouble() << ")\n";

  BigVecQ3 ann_ctr;
  BigRat ann_del;
  bool ok_ann = Tube229::AuditAxis(tri, decomp.annular_axis.contacts, &decomp.annular_axis, &ann_ctr, &ann_del, &fail, BigRat(1, 1000));
  std::cout << "Audit ann axis: " << (ok_ann ? "ok" : "fail: " + fail) << "\n";
  std::cout << "ann_ctr: (" << ann_ctr.x.ToDouble() << ", " << ann_ctr.y.ToDouble() << ", " << ann_ctr.z.ToDouble() << ")\n";

  return 0;
}
