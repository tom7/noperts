#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct DFSStats {
  int certified_leaves = 0;
  int uncertified_leaves = 0;
  int max_depth_reached = 0;
};

void SubdivideDFS(const std::string &path, int max_depth, DFSStats *stats) {
  TriangleQ tri = TriangleFromPath(path);
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificate(tri, path.size(), &cert, {}, {}, /*fast_only=*/true)) {
    stats->certified_leaves++;
    if ((int)path.size() > stats->max_depth_reached) stats->max_depth_reached = path.size();
    return;
  }
  if ((int)path.size() >= max_depth) {
    stats->uncertified_leaves++;
    return;
  }
  for (int c = 0; c < 4; c++) {
    SubdivideDFS(path + std::to_string(c), max_depth, stats);
  }
}

int main() {
  std::vector<std::string> leaves = {
    "03121300",
    "0312130332",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200"
  };

  for (const auto &path : leaves) {
    std::cout << "\nTesting leaf " << path << " (depth " << path.size() << "):\n";
    for (int max_d = path.size() + 1; max_d <= (int)path.size() + 5; max_d++) {
      DFSStats stats;
      SubdivideDFS(path, max_d, &stats);
      std::cout << "  max_depth=" << max_d
                << " -> certified=" << stats.certified_leaves
                << ", uncertified=" << stats.uncertified_leaves << "\n";
      if (stats.uncertified_leaves == 0) {
        std::cout << "  ===> FULLY CERTIFIED at depth " << max_d << "!\n";
        break;
      }
    }
  }

  return 0;
}
