#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo cont0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, cont0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));

  vec3 u0_f = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0_f);
  double u0_len = yocto::length(u0_f);
  std::cout << "u0: len = " << u0_len << " dir = (" << u0_dir.x << ", " << u0_dir.y << ", " << u0_dir.z << ")\n";

  // Search candidates in direction u0_dir and -u0_dir
  auto cands = Tube229::FindOpposingCandidates(tri, u0_dir, 100, 1e-12);
  auto cands_neg = Tube229::FindOpposingCandidates(tri, -u0_dir, 100, 1e-12);
  for (const auto &c : cands_neg) cands.push_back(c);
  std::cout << "Found " << cands.size() << " candidates near u0\n";

  double min_angle = 999.0;
  int min_idx = -1;

  for (size_t i = 0; i < cands.size(); i++) {
    // Audit with max_defect = 0
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    if (!Tube229::AuditAxis(tri, cands[i].contacts, &ax, &center, &delta, &err, BigRat(0))) {
      continue;
    }
    vec3 c_f = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
    vec3 c_dir = yocto::normalize(c_f);
    double dot = yocto::dot(u0_dir, c_dir);
    double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
    if (angle < min_angle) {
      min_angle = angle;
      min_idx = i;
      std::cout << "  New closest zero-defect axis: angle = " << angle << " deg, B = " << ax.B.ToDouble()
                << " len = " << yocto::length(c_f) << "\n";
    }
  }

  std::cout << "Closest zero-defect axis angle: " << min_angle << " deg\n";
  return 0;
}
