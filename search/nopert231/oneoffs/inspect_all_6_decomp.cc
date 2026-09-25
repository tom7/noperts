#include <iostream>
#include <vector>
#include <string>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  std::vector<std::string> paths = {
    "03121300",
    "0312130332",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200"
  };

  for (const auto &p : paths) {
    TreeNode *node = nullptr;
    auto find = [&](auto &self, TreeNode *n) -> void {
      if (n->path == p) { node = n; return; }
      for (auto &c : n->children) self(self, c.get());
    };
    find(find, root.get());
    std::cout << "========================================\n";
    std::cout << "Path " << p << ":\n";
    if (!node || !node->decomposed_cert.has_value()) {
      std::cout << "  NO DECOMPOSED CERT!\n";
      continue;
    }
    const auto &dec = *node->decomposed_cert;
    TriangleQ tri = TriangleFromPath(p);
    std::cout << "  r: " << dec.r.ToString() << "\n";
    std::cout << "  r_min: " << dec.r_min.ToString() << "\n";
    std::cout << "  delta: " << dec.delta.ToString() << "\n";
    std::cout << "  c_cone: " << dec.c_cone.ToString() << "\n";
    std::cout << "  c_core: " << dec.c_core.ToString() << "\n";
    std::cout << "  c_comp: " << dec.c_comp.ToString() << "\n";
    std::cout << "  lam: " << dec.lam.ToString() << "\n";
    std::cout << "  w: " << dec.w[0].ToString() << ", " << dec.w[1].ToString() << ", " << dec.w[2].ToString() << "\n";
    std::cout << "  coreAxis B: " << dec.inner_core_axis.B.ToString() << "\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = dec.inner_core_axis.contacts[m];
      std::cout << "  core contact " << m << ": start=" << c.edge_start << ", finish=" << c.edge_finish
                << ", start2=" << c.edge_start2 << ", finish2=" << c.edge_finish2
                << ", mix=" << c.mix << ", v=" << c.vertex << "\n";
    }
    std::cout << "  defect0: " << dec.defect0[0].ToString() << ", " << dec.defect0[1].ToString() << ", " << dec.defect0[2].ToString() << "\n";
    std::cout << "  defect_D: " << dec.defect_D.ToString() << "\n";
    std::cout << "  complement axes count: " << dec.complement_axes.size() << "\n";
    std::cout << "  children count: " << node->children.size() << "\n";

    ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
    AxisCertificate ax_ann;
    BigVecQ3 ctr_ann;
    BigRat del_ann;
    std::string err;
    Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));

    ContactInfo c_core[3] = {dec.inner_core_axis.contacts[0], dec.inner_core_axis.contacts[1], dec.inner_core_axis.contacts[2]};
    AxisCertificate ax_core;
    BigVecQ3 ctr_core;
    BigRat del_core;
    bool core_ok = Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

    std::cout << "  core_ok: " << core_ok << ", del_core: " << (core_ok ? del_core.ToDouble() : -1.0) << "\n";
    if (core_ok) {
      vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
                 ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
                 ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
      vec3 uc = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.z.ToDouble() / ax_core.B.ToDouble()};
      double dot = yocto::dot(u0, uc);
      double dot_unit = yocto::dot(yocto::normalize(u0), yocto::normalize(uc));
      std::cout << "  |u0| = " << yocto::length(u0) << ", |uc| = " << yocto::length(uc) << "\n";
      std::cout << "  dot(u0, uc) = " << dot << ", unit dot = " << dot_unit << "\n";
    }
  }

  return 0;
}
