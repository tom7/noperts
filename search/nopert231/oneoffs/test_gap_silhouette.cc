#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  double box_delta = 234013.0 / 1000000000.0;

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double X = 18.7029, Y = -23.5236; // The gap point
  vec3 p = P0 + X * E1 + Y * E2;
  vec3 view_dir = yocto::normalize(p);

  std::cout << "u0: " << u0.x << ", " << u0.y << ", " << u0.z << "\n";
  std::cout << "p: " << p.x << ", " << p.y << ", " << p.z << "\n";
  std::cout << "Target direction at gap: " << view_dir.x << ", " << view_dir.y << ", " << view_dir.z << "\n";

  auto candidates = Tube229::GenerateCandidatesForView(view_dir, tri, false);
  std::cout << "Found " << candidates.size() << " candidate triplets for view_dir.\n";

  int audited_valid = 0;
  double best_dot = -1.0;
  int best_cand = -1;

  for (size_t i = 0; i < candidates.size(); i++) {
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, candidates[i].contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
      double d_val = del.ToDouble();
      if (d_val <= box_delta) {
        audited_valid++;
        vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                  ctr.y.ToDouble() / cert.B.ToDouble(),
                  ctr.z.ToDouble() / cert.B.ToDouble()};
        double dot_val = yocto::dot(view_dir, v);
        if (dot_val > best_dot) {
          best_dot = dot_val;
          best_cand = i;
        }
      }
    }
  }

  std::cout << "Valid audited axes from view_dir: " << audited_valid << "\n";
  std::cout << "Best dot product at gap: " << best_dot << " (box.delta = " << box_delta << ")\n";
  if (best_cand >= 0) {
    std::cout << "Best candidate triplet contacts:\n";
    for (int k = 0; k < 3; k++) {
      const auto &c = candidates[best_cand].contacts[k];
      std::cout << "  v=" << c.vertex << " mix=" << c.mix
                << " (" << c.edge_start << "->" << c.edge_finish
                << " & " << c.edge_start2 << "->" << c.edge_finish2 << ")\n";
    }
  }

  return 0;
}
