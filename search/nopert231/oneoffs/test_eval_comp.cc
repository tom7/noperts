#include <iostream>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  std::unique_ptr<TreeNode> root = LoadTreeJson(".artifacts/nopert229/tree_0.json", true, ".artifacts/nopert229");
  const TreeNode *n = root.get();
  for (char ch : std::string("3121300")) {
    n = n->children[ch - '0'].get();
  }
  const auto &dec = *n->decomposed_cert;
  TriangleQ tri = n->GetTriangle();

  std::cout << "Path 3121300:\n";
  std::cout << "dec.complement_axes.size(): " << dec.complement_axes.size() << "\n";
  std::cout << "dec.c_cone: " << dec.c_cone.ToString() << " (" << dec.c_cone.ToDouble() << ")\n";
  std::cout << "dec.c_comp: " << dec.c_comp.ToString() << " (" << dec.c_comp.ToDouble() << ")\n";

  // Re-run EvaluateComplementConeCoverage with the exact parameters
  vec3 exc_dir;
  {
    ContactInfo triple[3] = {dec.inner_core_axis.contacts[0], dec.inner_core_axis.contacts[1], dec.inner_core_axis.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &fail);
    exc_dir = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
  }

  BigRat out_c;
  bool ok = Tube229::EvaluateComplementConeCoverage(tri, dec.complement_axes, exc_dir, dec.c_cone.ToDouble(), &out_c, 50000);
  std::cout << "EvaluateComplementConeCoverage result: " << (ok ? "OK" : "FAIL")
            << ", out_c = " << out_c.ToString() << " (" << out_c.ToDouble() << ")\n";

  return 0;
}
