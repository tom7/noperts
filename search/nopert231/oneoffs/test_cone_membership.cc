#include <iostream>
#include <vector>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000))) return 1;
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), ||u0|| = " << yocto::length(u0) << "\n";

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto raw_candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);

  std::vector<vec3> zero_defect_dirs;
  for (const auto &cand : raw_candidates) {
    ContactInfo ct[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, ct, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      zero_defect_dirs.push_back(yocto::normalize(v));
    }
  }
  std::cout << "Found " << zero_defect_dirs.size() << " zero-defect axes.\n";

  // Check separating hyperplane:
  // By Farkas Lemma, u0 is in cone(V) iff for all w, (w . v_i >= 0 for all i) => (w . u0 >= 0).
  // If u0 is NOT in cone(V), there exists a separating hyperplane w such that:
  // w . v_i >= 0 for all i, but w . u0 < 0!
  // Let us run Gilbert's algorithm / Frank-Wolfe / distance to convex hull of zero_defect_dirs
  // to find the projection of u0 onto cone(V).
  vec3 p = zero_defect_dirs[0];
  for (int iter = 0; iter < 10000; iter++) {
    // find vertex maximizing dot with (u0 - p)
    vec3 d = u0_dir - p;
    double best_dot = -1e9;
    int best_idx = -1;
    for (size_t i = 0; i < zero_defect_dirs.size(); i++) {
      double dt = yocto::dot(zero_defect_dirs[i], d);
      if (dt > best_dot) { best_dot = dt; best_idx = i; }
    }
    vec3 s = zero_defect_dirs[best_idx];
    // line search from p to s
    vec3 diff = s - p;
    double denom = yocto::dot(diff, diff);
    if (denom < 1e-15) break;
    double alpha = yocto::dot(u0_dir - p, diff) / denom;
    alpha = std::max(0.0, std::min(1.0, alpha));
    p = p + alpha * diff;
  }

  double dist = yocto::length(u0_dir - p);
  std::cout << "Closest point in conv(V) to u0_dir has distance: " << dist << "\n";
  std::cout << "Dot(p, u0_dir) = " << yocto::dot(p, u0_dir) << "\n";

  // What is the separating vector?
  vec3 sep = u0_dir - p;
  double min_dot_sep = 1e9;
  for (const auto &v : zero_defect_dirs) {
    min_dot_sep = std::min(min_dot_sep, yocto::dot(v, sep));
  }
  std::cout << "min(v . (u0_dir - p)) = " << min_dot_sep << ", u0_dir . (u0_dir - p) = " << yocto::dot(u0_dir, sep) << "\n";

  return 0;
}
