#include <iostream>
#include <string>
#include "tubetree229.h"
#include "tube229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false);
  if (!root) return 1;

  auto inspect_node = [](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->decomposed_cert.has_value()) {
      const auto &dc = *node->decomposed_cert;
      std::cout << "Node " << node->path << " (depth " << node->depth() << "): ";
      TriangleQ tri = node->GetTriangle();
      std::string err;

      ContactInfo c0[3] = {
        dc.annular_axis.contacts[0],
        dc.annular_axis.contacts[1],
        dc.annular_axis.contacts[2]
      };
      AxisCertificate ax0;
      BigVecQ3 ctr0;
      BigRat del0;
      Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
      BigVecQ3 u0 = ctr0 / ax0.B;

      BigVecQ3 tet[4];
      tet[0] = u0;
      bool ok = true;
      for (int a = 0; a < 3; a++) {
        const auto &ax = dc.complement_axes[a];
        ContactInfo ca[3] = {ax.contacts[0], ax.contacts[1], ax.contacts[2]};
        AxisCertificate axa;
        BigVecQ3 ctra;
        BigRat dela;
        if (!Tube229::AuditAxis(tri, ca, &axa, &ctra, &dela, &err, BigRat(0))) {
          ok = false;
          break;
        }
        tet[a + 1] = ctra / axa.B;
      }

      if (ok) {
        BigRat inrad = Tube229::ExactTetrahedronAxisRadius(tet);
        std::cout << "inradius = " << inrad.ToDouble()
                  << ", c_comp = " << dc.c_comp.ToDouble()
                  << ", c_cone = " << dc.c_cone.ToDouble()
                  << ", r = " << dc.r.ToDouble()
                  << ", r_min = " << dc.r_min.ToDouble() << "\n";
      } else {
        std::cout << "AuditAxis failed on complement axes: " << err << "\n";
      }
    }
    for (auto &c : node->children) self(self, c.get());
  };


  inspect_node(inspect_node, root.get());
  return 0;
}
