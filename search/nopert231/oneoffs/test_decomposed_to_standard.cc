#include <iostream>
#include <string>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

static bool TryStandardCert(const TriangleQ &tri, int depth, int max_depth) {
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificateIterative(tri, depth, &cert, {}, {}, 8)) {
    std::cout << "SUCCESS at depth " << depth << " (r=" << cert.r.ToString() << ")\n";
    return true;
  }
  if (depth >= max_depth) return false;
  // Subdivide
  TriangleQ children[4];
  tri.Subdivide(children);
  for (int c = 0; c < 4; c++) {
    if (!TryStandardCert(children[c], depth + 1, max_depth)) return false;
  }
  return true;
}

int main() {
  std::unique_ptr<TreeNode> root = LoadTreeJson(".artifacts/nopert229/tree_0.json", true, ".artifacts/nopert229");
  if (!root) {
    std::cerr << "Failed to load tree_0.json\n";
    return 1;
  }
  std::vector<std::string> target_paths = {
    "3121300",
    "3121303021",
    "3121303022",
    "3121303023",
    "3121303200",
    "312130332"
  };

  for (const auto &p : target_paths) {
    std::cout << "\nTesting path " << p << "...\n";
    const TreeNode *n = root.get();
    for (char ch : p) {
      int idx = ch - '0';
      if (idx < 0 || idx >= (int)n->children.size() || !n->children[idx]) {
        std::cerr << "Path not found: " << p << "\n";
        n = nullptr;
        break;
      }
      n = n->children[idx].get();
    }
    if (!n) continue;
    int base_depth = p.size();
    bool ok = TryStandardCert(n->GetTriangle(), base_depth, base_depth + 3);
    std::cout << "Path " << p << " standard cert result: " << (ok ? "CAN BE SOLVED WITH STANDARD CAGES" : "STUCK") << "\n";
  }
  return 0;
}
