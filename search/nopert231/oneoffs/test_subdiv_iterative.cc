#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int SubdivideAndCertify(const std::string &path, int max_depth) {
  TriangleQ tri = TriangleFromPath(path);
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificateIterative(tri, path.size(), &cert)) {
    return 1; // 1 leaf certified
  }
  if ((int)path.size() >= max_depth) {
    return -1; // failed at max_depth
  }

  int total_leaves = 0;
  for (int c = 0; c < 4; c++) {
    std::string child_path = path + std::to_string(c);
    int res = SubdivideAndCertify(child_path, max_depth);
    if (res < 0) return -1;
    total_leaves += res;
  }
  return total_leaves;
}

int main() {
  std::string p = "03121303022";
  std::cout << "Testing iterative synthesis with subdivision on " << p << ":\n";
  for (int max_d = p.size(); max_d <= p.size() + 4; max_d++) {
    int res = SubdivideAndCertify(p, max_d);
    if (res > 0) {
      std::cout << "  FULLY CERTIFIED at max_depth=" << max_d
                << " with " << res << " standard leaves!" << std::endl;
      break;
    } else {
      std::cout << "  max_depth=" << max_d << " incomplete\n";
    }
  }
  return 0;
}
