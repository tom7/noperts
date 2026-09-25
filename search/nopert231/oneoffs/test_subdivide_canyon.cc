#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int closed_nodes = 0;
int open_nodes = 0;

void Explore(const std::string &path, int max_depth) {
  TriangleQ tri = TriangleFromPath(path);
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificate(tri, path.size(), &cert)) {
    closed_nodes++;
    return;
  }
  if ((int)path.size() >= max_depth) {
    open_nodes++;
    std::cout << "Open leaf at depth " << max_depth << ": " << path << "\n";
    return;
  }
  for (int c = 0; c < 4; c++) {
    Explore(path + std::to_string(c), max_depth);
  }
}

int main() {
  std::cout << "Exploring 03121303200 up to depth 16...\n";
  Explore("03121303200", 16);
  std::cout << "Done! Closed: " << closed_nodes << ", Open: " << open_nodes << "\n";
  return 0;
}
