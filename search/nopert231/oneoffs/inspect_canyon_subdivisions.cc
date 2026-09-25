#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start; c.edge_finish2 = finish;
  c.mix = mix; c.vertex = v;
  return c;
}

void TestSubtree(std::string path, int current_depth, int max_depth) {
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo triple0[3] = {
    MakeContact(19, 3, 1000, 3),
    MakeContact(3, 2, 1000, 2),
    MakeContact(2, 1, 1000, 1)
  };

  AxisCertificate ax0;
  BigVecQ3 cQ0;
  BigRat delta0;
  std::string err;

  // Audit with zero defect first:
  bool zero_defect = Tube229::AuditAxis(tri, triple0, &ax0, &cQ0, &delta0, &err, BigRat(0));
  if (zero_defect) {
    std::cout << "Path " << path << " (depth " << current_depth << ") HAS ZERO DEFECT! delta = " << delta0.ToDouble() << "\n";
    return;
  }

  // Find actual defect:
  BigRat min_D(0);
  for (int num = 1; num <= 1000; num++) {
    BigRat test_D(num, 100000000); // steps of 1e-8
    if (Tube229::AuditAxis(tri, triple0, &ax0, &cQ0, &delta0, &err, test_D)) {
      min_D = test_D;
      break;
    }
  }

  std::cout << "Path " << path << " (depth " << current_depth << "): min_D = " << min_D.ToDouble() << "\n";

  if (current_depth < max_depth) {
    for (int child = 0; child < 4; child++) {
      TestSubtree(path + std::to_string(child), current_depth + 1, max_depth);
    }
  }
}

int main() {
  std::string root_path = "031213002112122012121";
  std::cout << "Testing canyon cell " << root_path << " and its descendants:\n";
  TestSubtree(root_path, 21, 23);
  return 0;
}
