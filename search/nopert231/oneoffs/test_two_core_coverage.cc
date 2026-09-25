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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Annular axis u0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // Generate zero-defect axes:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 400, 500, 600, 800, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  int C = cand_contacts.size();
  std::vector<vec3> zero_defect_dirs;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          zero_defect_dirs.push_back({center.x.ToDouble() / ax.B.ToDouble(),
                                     center.y.ToDouble() / ax.B.ToDouble(),
                                     center.z.ToDouble() / ax.B.ToDouble()});
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_dirs.size() << " zero-defect axes.\n";

  // Sample 50,000 points on sphere in the cone: dot(a, u0) >= 0.0041195
  double c_thresh = 0.0041195;
  std::vector<vec3> cone_pts;
  int N = 200000;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) >= c_thresh) {
      cone_pts.push_back(a);
    }
  }

  std::cout << "Points in u0 cone: " << cone_pts.size() << "\n";

  // Test if any pair of zero-defect axes covers the entire cone with margin > 0.001:
  bool found_pair = false;
  int best_i = -1, best_j = -1;
  double best_min_cover = -1e9;

  // Subsample zero_defect_dirs for speed:
  int M = std::min((size_t)300, zero_defect_dirs.size());
  for (int i = 0; i < M; i++) {
    for (int j = i + 1; j < M; j++) {
      double min_cover = 1e9;
      for (const auto &pt : cone_pts) {
        double d1 = yocto::dot(pt, zero_defect_dirs[i]);
        double d2 = yocto::dot(pt, zero_defect_dirs[j]);
        double m = std::max(d1, d2);
        if (m < min_cover) min_cover = m;
        if (min_cover < best_min_cover) break;
      }
      if (min_cover > best_min_cover) {
        best_min_cover = min_cover;
        best_i = i; best_j = j;
        std::cout << "New best pair (" << i << ", " << j << ") with min_cover = " << min_cover << "\n";
      }
    }
  }

done:
  std::cout << "Best pair (" << best_i << ", " << best_j << ") min_cover: " << best_min_cover << "\n";
  return 0;
}
