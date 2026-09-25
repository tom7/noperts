#include <iostream>
#include <vector>
#include <algorithm>
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

  // Annular axis u0:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000))) {
    std::cerr << "Failed to audit u0\n";
    return 1;
  }
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);
  std::cout << "u0 = (" << u0.x << ", " << u0.y << ", " << u0.z << "), ||u0|| = " << yocto::length(u0) << "\n";

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto raw_candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);

  struct AxisData {
    vec3 v;
    vec3 dir;
    double dot_u0;
    Tube229::CandidateTriple cand;
    AxisCertificate cert;
  };
  std::vector<AxisData> all_axes;

  for (const auto &cand : raw_candidates) {
    ContactInfo ct[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, ct, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      vec3 dir = yocto::normalize(v);
      all_axes.push_back({v, dir, yocto::dot(dir, u0_dir), cand, cert});
    }
  }

  std::cout << "Audited " << all_axes.size() << " zero-defect axes.\n";

  // Filter to diverse axes:
  std::vector<AxisData> diverse;
  for (const auto &a : all_axes) {
    bool dup = false;
    for (const auto &d : diverse) {
      if (yocto::dot(a.dir, d.dir) > 0.98) { dup = true; break; }
    }
    if (!dup) diverse.push_back(a);
  }
  std::cout << "Filtered to " << diverse.size() << " diverse axes.\n";

  auto Det3 = [](vec3 a, vec3 b, vec3 c) {
    return yocto::dot(a, yocto::cross(b, c));
  };

  double c_cone = 0.045; // test value
  double best_c_core = 0;
  int best_tri[3] = {-1, -1, -1};
  vec3 best_mu;

  for (size_t i = 0; i < diverse.size(); i++) {
    for (size_t j = i + 1; j < diverse.size(); j++) {
      for (size_t k = j + 1; k < diverse.size(); k++) {
        vec3 v1 = diverse[i].v;
        vec3 v2 = diverse[j].v;
        vec3 v3 = diverse[k].v;
        double det = Det3(v1, v2, v3);
        if (std::abs(det) < 1e-12) continue;

        double mu1 = Det3(u0, v2, v3) / det;
        double mu2 = Det3(v1, u0, v3) / det;
        double mu3 = Det3(v1, v2, u0) / det;

        if (mu1 > 0 && mu2 > 0 && mu3 > 0) {
          double S = mu1 + mu2 + mu3;
          double c_core_achieved = (1.0 * c_cone) / S;
          if (c_core_achieved > best_c_core) {
            best_c_core = c_core_achieved;
            best_tri[0] = i; best_tri[1] = j; best_tri[2] = k;
            best_mu = {mu1, mu2, mu3};
            std::cout << "FOUND POSITIVE CONE! mu = (" << mu1 << ", " << mu2 << ", " << mu3
                      << "), S = " << S << ", c_core = " << c_core_achieved << "\n";
            std::cout << "  Axes dot with u0: " << diverse[i].dot_u0 << ", " << diverse[j].dot_u0 << ", " << diverse[k].dot_u0 << "\n";
          }
        }
      }
    }
  }

  std::cout << "Best c_core: " << best_c_core << "\n";
  if (best_tri[0] >= 0) {
    std::cout << "Winning triple details:\n";
    for (int idx : {best_tri[0], best_tri[1], best_tri[2]}) {
      std::cout << "  Axis " << idx << " (dot = " << diverse[idx].dot_u0 << "):\n";
      for (int m = 0; m < 3; m++) {
        const auto &ct = diverse[idx].cand.contacts[m];
        std::cout << "    [" << ct.edge_start << "->" << ct.edge_finish << ", mix " << ct.mix << ", v " << ct.vertex << "]\n";
      }
    }
  }

  return 0;
}
