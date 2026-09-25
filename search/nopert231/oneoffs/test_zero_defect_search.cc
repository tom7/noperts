#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  TriangleQ tri = TriangleFromPath("03121300");

  ContactInfo c_ann[3] = {
    { .edge_start = 3, .edge_finish = 2, .edge_start2 = 2, .edge_finish2 = 1, .mix = 800, .vertex = 2 },
    { .edge_start = 1, .edge_finish = 4, .edge_start2 = 4, .edge_finish2 = 8, .mix = 800, .vertex = 4 },
    { .edge_start = 13, .edge_finish = 14, .edge_start2 = 14, .edge_finish2 = 15, .mix = 200, .vertex = 14 }
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));

  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);
  if (u0_dir.z < 0) u0_dir = -u0_dir;

  // Search with try_mix = true!
  std::cout << "Searching around u0_dir (" << u0_dir.x << ", " << u0_dir.y << ", " << u0_dir.z << ") with try_mix = true...\n";
  auto cands = Tube229::GenerateCandidatesForView(u0_dir, tri, true, 20, true);
  std::cout << "Generated " << cands.size() << " candidates.\n";

  int zero_defect_count = 0;
  for (const auto &cand : cands) {
    ContactInfo test_c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
      zero_defect_count++;
      std::cout << "FOUND ZERO DEFECT AXIS! B=" << ax.B.ToDouble() << ", del=" << del.ToDouble() << "\n";
      for (int m = 0; m < 3; m++) {
        std::cout << "  contact " << m << ": start=" << ax.contacts[m].edge_start
                  << ", finish=" << ax.contacts[m].edge_finish
                  << ", start2=" << ax.contacts[m].edge_start2
                  << ", finish2=" << ax.contacts[m].edge_finish2
                  << ", mix=" << ax.contacts[m].mix
                  << ", vertex=" << ax.contacts[m].vertex << "\n";
      }
      break;
    }
  }

  std::cout << "Zero defect candidates found: " << zero_defect_count << "\n";
  return 0;
}
