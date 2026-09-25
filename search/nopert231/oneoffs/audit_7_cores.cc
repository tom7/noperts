#include <iostream>
#include <iomanip>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  BigRat box_delta(234013, 1000000000);

  // 7 axes
  ContactInfo cores[7][3] = {
    // 0: Axis 25
    {{2, 10, 1, 15, 0, 15}, {3, 15, 15, 19, 800, 1}, {2, 19, 19, 1, 0, 10}}, // Wait, let's use exact from print_leaf_details!
  };
  return 0;
}
