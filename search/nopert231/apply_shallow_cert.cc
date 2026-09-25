#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static bool CertifyAndPruneNode(TreeNode *curr,
                                const std::string &target_path,
                                TreeNode *root,
                                const TubeCertificate &base_sib,
                                bool apply,
                                int *leaves_eliminated,
                                int *incomplete_eliminated) {
  int total_leaves = 0;
  int incomplete_leaves = 0;
  auto count_fn = [&](auto &self, const TreeNode &node) -> void {
    if (node.children.empty()) {
      total_leaves++;
      if (!node.direct_cert.has_value() && !node.decomposed_cert.has_value()) {
        incomplete_leaves++;
      }
      return;
    }
    for (const auto &child : node.children) {
      if (child) self(self, *child);
    }
  };
  count_fn(count_fn, *curr);

  TriangleQ tri = TriangleFromPath(target_path);
  vec3 c0 = {tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()};
  vec3 c1 = {tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()};
  vec3 c2 = {tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()};
  vec3 center = yocto::normalize(c0 + c1 + c2);

  auto nearest = FindNearestCertifiedNode(*root, center);
  const TubeCertificate *sib = nullptr;
  if (nearest.has_value()) {
    const TreeNode *nnode = root;
    for (size_t i = 1; i < nearest->path.size(); i++) {
      int idx = nearest->path[i] - '0';
      if (idx >= 0 && idx < (int)nnode->children.size() && nnode->children[idx]) {
        nnode = nnode->children[idx].get();
      } else {
        nnode = nullptr;
        break;
      }
    }
    if (nnode && nnode->direct_cert.has_value()) {
      sib = &nnode->direct_cert.value();
    }
  }

  DecomposedCertificate dc;
  std::string fail;
  bool ok = Tube229::SynthesizeDecomposedCertificate(tri, target_path.size(), &dc, sib ? sib : &base_sib, &fail);
  if (!ok && sib != nullptr) {
    ok = Tube229::SynthesizeDecomposedCertificate(tri, target_path.size(), &dc, &base_sib, &fail);
  }

  if (!ok) {
    std::cout << "Node " << target_path << " (depth " << target_path.size() << "): FAILED synthesis: " << fail << "\n";
    return false;
  }

  std::cout << "Node " << target_path << " (depth " << target_path.size()
            << "): SUCCESS! Eliminated " << incomplete_leaves << " incomp leaves (" << total_leaves << " total)\n"
            << "  r=" << dc.r.ToString() << " r_min=" << dc.r_min.ToString()
            << " c_cone=" << dc.c_cone.ToString() << " c_comp=" << dc.c_comp.ToString()
            << " (" << dc.c_comp.ToDouble() << ")\n";

  if (leaves_eliminated) *leaves_eliminated = total_leaves;
  if (incomplete_eliminated) *incomplete_eliminated = incomplete_leaves;

  if (apply) {
    curr->decomposed_cert = dc;
    curr->direct_bounds.direct_r_lower = dc.r;
    curr->direct_bounds.direct_c_lower = dc.c_comp;
    curr->children.clear();
  }
  return true;
}

static void AutoSweep(TreeNode *node,
                      TreeNode *root,
                      const TubeCertificate &base_sib,
                      int min_depth,
                      int max_depth,
                      bool apply,
                      int &nodes_certified,
                      int &total_incomplete_eliminated) {
  if (node->children.empty()) {
    if (!node->direct_cert.has_value() && !node->decomposed_cert.has_value()) {
      int elim_leaves = 0, elim_incomp = 0;
      if (CertifyAndPruneNode(node, node->path, root, base_sib, apply, &elim_leaves, &elim_incomp)) {
        nodes_certified++;
        total_incomplete_eliminated += elim_incomp;
      }
    }
    return;
  }

  int incomp = 0;
  auto count_incomp = [&](auto &self, const TreeNode &n) -> void {
    if (n.children.empty()) {
      if (!n.direct_cert.has_value() && !n.decomposed_cert.has_value()) {
        incomp++;
      }
      return;
    }
    for (const auto &ch : n.children) {
      if (ch) self(self, *ch);
    }
  };
  count_incomp(count_incomp, *node);
  if (incomp == 0) return;

  int depth = (int)node->path.size();
  if (depth >= min_depth && depth <= max_depth) {
    int elim_leaves = 0, elim_incomp = 0;
    if (CertifyAndPruneNode(node, node->path, root, base_sib, apply, &elim_leaves, &elim_incomp)) {
      nodes_certified++;
      total_incomplete_eliminated += elim_incomp;
      return;
    }
  }

  for (auto &ch : node->children) {
    if (ch) {
      AutoSweep(ch.get(), root, base_sib, min_depth, max_depth, apply, nodes_certified, total_incomplete_eliminated);
    }
  }
}

int main(int argc, char **argv) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <tree_json_path> [target_path1 target_path2 ...] [--apply] [--auto_sweep] [--min_depth <int>]\n";
    return 1;
  }

  std::string tree_path = argv[1];
  bool apply = false;
  bool auto_sweep = false;
  int min_depth = 8;
  int max_depth = 15;
  std::vector<std::string> target_paths;

  for (int i = 2; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--apply") {
      apply = true;
    } else if (arg == "--auto_sweep") {
      auto_sweep = true;
    } else if (arg == "--min_depth" && i + 1 < argc) {
      min_depth = std::atoi(argv[++i]);
    } else if (arg == "--max_depth" && i + 1 < argc) {
      max_depth = std::atoi(argv[++i]);
    } else if (arg.rfind("--", 0) != 0) {
      target_paths.push_back(arg);
    }
  }

  std::cout << "Loading tree from " << tree_path << "...\n";
  auto root = LoadTreeJson(tree_path);
  if (!root) {
    std::cerr << "Failed to load tree.\n";
    return 1;
  }

  // Base fallback sibling
  TubeCertificate base_sib;
  ContactInfo cont0[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  ContactInfo cont1[3] = {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}};
  ContactInfo cont2[3] = {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}};
  ContactInfo cont3[3] = {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}};
  for (int m = 0; m < 3; m++) {
    base_sib.axes[0].contacts[m] = cont0[m];
    base_sib.axes[1].contacts[m] = cont1[m];
    base_sib.axes[2].contacts[m] = cont2[m];
    base_sib.axes[3].contacts[m] = cont3[m];
  }
  base_sib.axes[0].B = BigRat(139673967, 100000000);
  base_sib.axes[1].B = BigRat(176, 100);
  base_sib.axes[2].B = BigRat(176, 100);
  base_sib.axes[3].B = BigRat(176, 100);
  base_sib.delta = BigRat(333, 1000000000);
  base_sib.symmetry_index = 0;

  int total_incomplete_eliminated = 0;
  int nodes_certified = 0;

  if (auto_sweep) {
    std::cout << "Starting auto-sweep (depth range " << min_depth << ".." << max_depth << ")...\n";
    AutoSweep(root.get(), root.get(), base_sib, min_depth, max_depth, apply, nodes_certified, total_incomplete_eliminated);
  } else {
    if (target_paths.empty()) {
      target_paths.push_back("03121303021201");
    }
    for (const auto &path : target_paths) {
      TreeNode *curr = root.get();
      bool found = true;
      for (size_t i = 1; i < path.size(); i++) {
        int idx = path[i] - '0';
        if (idx >= 0 && idx < (int)curr->children.size() && curr->children[idx]) {
          curr = curr->children[idx].get();
        } else {
          std::cerr << "Target path not found in tree: " << path << "\n";
          found = false;
          break;
        }
      }
      if (!found) continue;

      int elim_leaves = 0, elim_incomp = 0;
      if (CertifyAndPruneNode(curr, path, root.get(), base_sib, apply, &elim_leaves, &elim_incomp)) {
        nodes_certified++;
        total_incomplete_eliminated += elim_incomp;
      }
    }
  }

  std::cout << "\n=== Sweep Summary ===\n";
  std::cout << "Nodes certified: " << nodes_certified << "\n";
  std::cout << "Incomplete leaves eliminated: " << total_incomplete_eliminated << "\n";

  // Count remaining leaves in tree
  int rem_total = 0, rem_cert = 0, rem_decomp = 0, rem_incomp = 0;
  auto audit_fn = [&](auto &self, const TreeNode &n) -> void {
    if (n.children.empty()) {
      rem_total++;
      if (n.decomposed_cert.has_value()) rem_decomp++;
      else if (n.direct_cert.has_value() || BigRat::Sign(n.direct_bounds.direct_c_lower) > 0) rem_cert++;
      else rem_incomp++;
      return;
    }
    for (const auto &ch : n.children) {
      if (ch) self(self, *ch);
    }
  };
  audit_fn(audit_fn, *root);
  std::cout << "Current tree stats:\n";
  std::cout << "  Total leaves: " << rem_total << "\n";
  std::cout << "  Direct certified leaves: " << rem_cert << "\n";
  std::cout << "  Decomposed certified leaves: " << rem_decomp << "\n";
  std::cout << "  Incomplete leaves remaining: " << rem_incomp << "\n";

  if (apply) {
    std::cout << "\nSaving updated tree to " << tree_path << "...\n";
    if (SaveTreeJson(*root, tree_path, false)) {
      std::cout << "Tree successfully saved!\n";
    } else {
      std::cerr << "Failed to save tree!\n";
      return 1;
    }
  } else {
    std::cout << "\n(Dry run mode. Pass --apply to write changes to tree json.)\n";
  }

  return 0;
}
