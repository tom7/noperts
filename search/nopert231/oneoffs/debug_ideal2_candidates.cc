#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  vec3 ideal2 = {-0.82403, -0.551492, 0.129735};
  std::cout << "Calling GenerateCandidatesForView with evaluate_over_triangle = false...\n";
  auto cands_false = Tube229::GenerateCandidatesForView(ideal2, tri, false, 8, true);
  std::cout << "Without eval over tri: " << cands_false.size() << " candidates\n";

  auto cands_true = Tube229::GenerateCandidatesForView(ideal2, tri, true, 8, true, 1e-4);
  std::cout << "With eval over tri (slack 1e-4): " << cands_true.size() << " candidates\n";

  auto cands_large = Tube229::GenerateCandidatesForView(ideal2, tri, true, 8, true, 1e-1);
  std::cout << "With eval over tri (slack 1e-1): " << cands_large.size() << " candidates\n";
  return 0;
}
