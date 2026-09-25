#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

// Lean's exact supportError:
// tightVertexErrorQ is ~4.33e-7, supportError = 10 * tightVertexErrorQ ~= 4.33e-6.
const double SUPPORT_ERROR = 5e-6;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  // We want to find axes that:
  // 1. delta <= 0.000165
  // 2. In Lean, supportUpper <= 0 everywhere!
  // In C++, this means for each contact i and each vertex k:
  // if k is exactSupportTie, max_disp = 0;
  // else max_disp + SUPPORT_ERROR <= 0!

  std::vector<int> zero_defect_axes;

  for (size_t ax_idx = 0; ax_idx < axes.size(); ax_idx++) {
    if (axes[ax_idx].delta.ToDouble() > 0.000165) continue;
    const auto &ax = axes[ax_idx].cert;

    bool valid = true;
    for (int i = 0; i < 3; i++) {
      int v_support = ax.contacts[i].vertex;
      int e_start = ax.contacts[i].edge_start;
      int e_finish = ax.contacts[i].edge_finish;
      int e_start2 = ax.contacts[i].edge_start2;
      int e_finish2 = ax.contacts[i].edge_finish2;
      int mix = ax.contacts[i].mix;

      // Contact edge direction
      // We check all 24 vertices
      for (int k = 0; k < 24; k++) {
        // Is k an exactSupportTie?
        bool is_tie = (k == v_support) ||
                      (mix == 1000 && v_support == e_finish && k == e_start) ||
                      (mix == 0 && v_support == e_start2 && k == e_finish2);
        if (is_tie) continue;

        // Otherwise, the displacement at all 3 corners of tri plus SUPPORT_ERROR must be <= 0.
        // Let's compute displacement at tri center:
        // If the displacement at tri center is > -2 * SUPPORT_ERROR, it might fail.
        // We know AuditAxis passed, so true displacement <= 0.
        // But if true displacement is > -SUPPORT_ERROR, Lean will say > 0!
      }
    }
  }

  // Let's test which axes from candidate_v actually pass Lean's supportUpper <= 0!
  return 0;
}
