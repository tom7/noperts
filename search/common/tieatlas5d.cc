#include "tieatlas5d.h"

#include <format>
#include <fstream>
#include <functional>
#include <sstream>

#include "base/logging.h"

namespace tieatlas5d {

TieAtlas TieAtlas::Load(const std::string &dir, int num_normals, int num_triangles) {
  TieAtlas a;
  a.num_normals_ = num_normals;
  a.num_triangles_ = num_triangles;
  a.trees_.resize(num_normals * num_triangles);
  for (int n = 0; n < num_normals; n++) {
    for (int t = 0; t < num_triangles; t++) {
      std::ifstream in(std::format("{}/n{}_t{}.txt", dir, n, t));
      if (!in.good()) continue;
      Tree &tree = a.trees_[n * num_triangles + t];
      std::string line;
      while (std::getline(in, line)) {
        std::istringstream ss(line);
        std::string path, v;
        if (!(ss >> path >> v)) continue;
        if (path == ".") path = "";
        Node node;
        if (v == "S") node.split = true;
        else if (v == "N" || v == "0" || v == "C" || v == "F") node.rho = BigRat(0);
        else node.rho = BigRat(std::string_view(v));
        tree[path] = node;
      }
      // Subtree minima (children of a split node: path + digit).
      std::function<BigRat(const std::string &)> fill = [&](const std::string &p) -> BigRat {
        auto it = tree.find(p);
        if (it == tree.end()) return BigRat(0);
        if (!it->second.split) return it->second.min_rho = it->second.rho;
        BigRat m = fill(p + '0');
        for (char c : {'1', '2', '3'}) m = BigRat::Min(m, fill(p + c));
        tree[p].min_rho = m;
        return m;
      };
      if (!tree.empty()) fill("");
    }
  }
  return a;
}

BigRat TieAtlas::Radius(int n, int t, std::string_view view_path) const {
  const Tree &tree = trees_[n * num_triangles_ + t];
  if (tree.empty()) return BigRat(0);
  std::string p;
  for (size_t k = 0;; k++) {
    auto it = tree.find(p);
    if (it == tree.end()) return BigRat(0);
    if (!it->second.split || k == view_path.size()) return it->second.min_rho;
    p += view_path[k];
  }
}

}  // namespace tieatlas5d
