#include <iostream>
#include <fstream>
#include "json.hpp"

using json = nlohmann::json;

int main() {
  std::ifstream f("/home/tom/nopert-project/ruperts/tree_0.json");
  if (!f) {
    std::cerr << "Could not open tree_0.json\n";
    return 1;
  }
  json j;
  f >> j;
  for (const auto &node : j) {
    if (node.value("path", "") == "03121300") {
      std::cout << node.dump(2) << "\n";
      return 0;
    }
  }
  std::cout << "Node 03121300 not found\n";
  return 0;
}
