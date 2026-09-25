#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Let's get the annular axis from tree_0.json
  // Actually, what was the annular axis u0 in check_hineq_03121300.cc?
  // In check_hineq_03121300.cc, u0 was:
  // {-0.196185, 0.262378, -0.944812}
  // Let's verify what contacts produced that u0 in tree_0.json!
  return 0;
}
