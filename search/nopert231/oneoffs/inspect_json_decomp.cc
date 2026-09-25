#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "tubetree229.h"

using namespace tubetree229;

void FindDecomp(const TreeNode &node, std::vector<std::string> *paths) {
  if (node.decomposed_cert.has_value()) {
    paths->push_back(node.path);
  }
  for (int c = 0; c < 4; c++) {
    if (node.children[c]) {
      FindDecomp(*node.children[c], paths);
    }
  }
}

int main() {
  std::string json_path = "/home/tom/nopert-project/Noperthedron/.artifacts/nopert229/local-view-child0.json";
  std::cout << "Loading " << json_path << "...\n";
  auto tree = LoadTreeJson(json_path);
  std::vector<std::string> paths;
  if (tree) {
    FindDecomp(*tree, &paths);
  }
  std::cout << "Found " << paths.size() << " decomposed nodes:\n";
  for (size_t i = 0; i < paths.size(); i++) {
    std::cout << "  [" << i << "] path = " << paths[i] << "\n";
  }
  return 0;
}
