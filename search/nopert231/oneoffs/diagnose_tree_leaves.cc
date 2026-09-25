#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <string>
#include "tubetree229.h"

using namespace tubetree229;

int main(int argc, char **argv) {
  std::string file = ".artifacts/nopert229/tree_0.json";
  if (argc > 1) file = argv[1];

  std::cout << "Loading tree from " << file << "...\n" << std::flush;
  auto root = LoadTreeJson(file, false);
  if (!root) {
    std::cerr << "Failed to load " << file << "\n";
    return 1;
  }

  std::map<int, int> uncert_by_depth;
  std::map<std::string, int> uncert_by_prefix;
  int total_leaves = 0;
  int total_cert = 0;
  int total_decomp = 0;
  int total_uncert = 0;
  std::vector<TreeNode*> sample_uncert;

  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->children.empty()) {
      total_leaves++;
      if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) {
        total_cert++;
      } else if (node->decomposed_cert.has_value() && BigRat::Sign(node->decomposed_cert->r) > 0) {
        total_decomp++;
        std::cout << "Decomposed leaf: path=" << node->path << ", depth=" << node->depth() << "\n";
      } else {
        total_uncert++;
        uncert_by_depth[node->depth()]++;
        std::string pref = node->path.substr(0, std::min((size_t)8, node->path.size()));
        uncert_by_prefix[pref]++;
        if (sample_uncert.size() < 1000) sample_uncert.push_back(node);
      }
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Total leaves: " << total_leaves << "\n";
  std::cout << "Direct certified leaves: " << total_cert << "\n";
  std::cout << "Decomposed certified leaves: " << total_decomp << "\n";
  std::cout << "Uncertified leaves: " << total_uncert << "\n\n";

  std::cout << "Depth distribution of uncertified leaves:\n";
  for (const auto &[depth, count] : uncert_by_depth) {
    std::cout << "  Depth " << depth << ": " << count << " leaves\n";
  }

  std::cout << "\nPrefix (len 8) distribution of uncertified leaves (top 20):\n";
  std::vector<std::pair<int, std::string>> sorted_prefs;
  for (const auto &[p, c] : uncert_by_prefix) sorted_prefs.push_back({c, p});
  std::sort(sorted_prefs.rbegin(), sorted_prefs.rend());
  for (size_t i = 0; i < std::min((size_t)20, sorted_prefs.size()); i++) {
    std::cout << "  Prefix " << sorted_prefs[i].second << ": " << sorted_prefs[i].first << " leaves\n";
  }

  return 0;
}
