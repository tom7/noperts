#include <iostream>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p0) { n0 = node; return; }
    if (p0.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find(find, root.get());

  if (!n0 || !n0->direct_cert.has_value()) return 1;

  TriangleQ tri0 = n0->GetTriangle();
  const TubeCertificate &c0 = *n0->direct_cert;

  std::cout << "Sibling n0 certificate details:\n";
  std::cout << "  r = " << c0.r.ToString() << " (" << c0.r.ToDouble() << ")\n";
  std::cout << "  c = " << c0.c.ToString() << " (" << c0.c.ToDouble() << ")\n";

  vec3 sep_norm = {-0.401011, 0.483067, 0.778355};

  for (int a = 0; a < 4; a++) {
    Tube229::CandidateTriple cand;
    Tube229::DoubleCheckAxis(tri0, c0.axes[a].contacts, &cand);
    double dot_sep = yocto::dot(cand.normalized_a, sep_norm);
    std::cout << "  Axis " << a << ": norm_a = ("
              << cand.normalized_a.x << ", " << cand.normalized_a.y << ", " << cand.normalized_a.z
              << ") | dot(sep_norm) = " << dot_sep << "\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "    m=" << m << ": v=" << c0.axes[a].contacts[m].vertex
                << " edge=(" << c0.axes[a].contacts[m].edge_start << "->" << c0.axes[a].contacts[m].edge_finish
                << ", " << c0.axes[a].contacts[m].edge_start2 << "->" << c0.axes[a].contacts[m].edge_finish2
                << ") mix=" << c0.axes[a].contacts[m].mix << "\n";
    }
  }

  return 0;
}
