#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) {
    std::cerr << "Failed to load root\n";
    return 1;
  }
  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find_node = [&](auto &self, TreeNode *n) -> void {
    if (!n || n0) return;
    if (n->path == p0) { n0 = n; return; }
    if (p0.starts_with(n->path)) {
      for (auto &c : n->children) self(self, c.get());
    }
  };
  find_node(find_node, root.get());
  if (!n0 || !n0->direct_cert.has_value()) {
    std::cerr << "n0 not found or no cert\n";
    return 1;
  }

  const TubeCertificate &cert = *n0->direct_cert;
  std::cout << "-- Certificate for node " << p0 << "\n";
  std::cout << "def sib_r : ℚ := " << cert.r.ToString() << "\n";
  std::cout << "def sib_c : ℚ := " << cert.c.ToString() << "\n";
  std::cout << "def sib_delta : ℚ := " << cert.delta.ToString() << "\n";

  for (int a = 0; a < 4; a++) {
    const auto &ax = cert.axes[a];
    std::cout << "def cert" << a << " : AxisCertificate := {\n";
    std::cout << "  edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "]\n";
    std::cout << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "]\n";
    std::cout << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "]\n";
    std::cout << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "]\n";
    std::cout << "  mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "]\n";
    std::cout << "  index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "]\n";
    std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "]\n";
    std::cout << "  B := " << ax.B.ToString() << "\n";
    std::cout << "}\n\n";
  }

  return 0;
}
