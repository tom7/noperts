#include <iostream>
#include <vector>
#include <random>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));
  vec3 p0 = {ctr_ann.x.ToDouble(), ctr_ann.y.ToDouble(), ctr_ann.z.ToDouble()};

  std::vector<vec3> views;
  for (int x = -1; x <= 1; x++) {
    for (int y = -1; y <= 1; y++) {
      for (int z = -1; z <= 1; z++) {
        if (x == 0 && y == 0 && z == 0) continue;
        views.push_back(yocto::normalize(vec3{(float)x, (float)y, (float)z}));
      }
    }
  }

  std::vector<Tube229::CandidateTriple> all_cands;
  for (const auto &v : views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 6, true);
    for (const auto &c : cands) all_cands.push_back(c);
  }

  struct ValidAxis {
    ContactInfo ct[3];
    vec3 center;
  };
  std::vector<ValidAxis> valid_axes;
  for (const auto &c_cand : all_cands) {
    ContactInfo ct[3] = {c_cand.contacts[0], c_cand.contacts[1], c_cand.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, ct, &ax, &ctr, &del, &err, BigRat(0))) {
      valid_axes.push_back({
        {ct[0], ct[1], ct[2]},
        vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}
      });
    }
  }
  std::cout << "Audited zero-defect axes: " << valid_axes.size() << "\n";

  // We want to find i, j, k such that conv(p0, pi, pj, pk) encloses (0, 0, 0)
  // To be robust, let's filter axes by octants opposing p0
  // p0 is (-0.0028, +0.0032, -0.0028) -> (-X, +Y, -Z)
  // Opposing directions should have +X, -Y, +Z
  std::vector<int> group_pos_x, group_neg_y, group_pos_z;
  for (size_t i = 0; i < valid_axes.size(); i++) {
    if (valid_axes[i].center.x > 0.02) group_pos_x.push_back(i);
    if (valid_axes[i].center.y < -0.01) group_neg_y.push_back(i);
    if (valid_axes[i].center.z > 0.02) group_pos_z.push_back(i);
  }
  std::cout << "Group sizes: +X: " << group_pos_x.size()
            << ", -Y: " << group_neg_y.size()
            << ", +Z: " << group_pos_z.size() << "\n";

  for (int idx1 : group_pos_x) {
    vec3 p1 = valid_axes[idx1].center;
    for (int idx2 : group_neg_y) {
      vec3 p2 = valid_axes[idx2].center;
      for (int idx3 : group_pos_z) {
        vec3 p3 = valid_axes[idx3].center;

        vec3 d0 = p0 - p3;
        vec3 d1 = p1 - p3;
        vec3 d2 = p2 - p3;
        double det = Det3(d0, d1, d2);
        if (std::abs(det) < 1e-6) continue;

        vec3 dp = -p3;
        double b0 = Det3(dp, d1, d2) / det;
        double b1 = Det3(d0, dp, d2) / det;
        double b2 = Det3(d0, d1, dp) / det;
        double b3 = 1.0 - b0 - b1 - b2;

        if (b0 > 0.05 && b1 > 0.05 && b2 > 0.05 && b3 > 0.05) {
          std::cout << "FOUND SUPER CAGE!\n";
          std::cout << "b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << "\n";
          std::cout << "p0 = (" << p0.x << ", " << p0.y << ", " << p0.z << ")\n";
          std::cout << "p1 = (" << p1.x << ", " << p1.y << ", " << p1.z << ")\n";
          std::cout << "p2 = (" << p2.x << ", " << p2.y << ", " << p2.z << ")\n";
          std::cout << "p3 = (" << p3.x << ", " << p3.y << ", " << p3.z << ")\n";
          std::cout << "Indices: " << idx1 << ", " << idx2 << ", " << idx3 << "\n";
          return 0;
        }
      }
    }
  }

  std::cout << "Did not find in filtered groups.\n";
  return 0;
}
