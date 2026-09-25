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

  // Axis 0:
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

  // 3 complement axes from earlier:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  int idx0 = 421, idx1 = 264, idx2 = 428;
  vec3 u1 = {axes500[idx0].center.x.ToDouble() / axes500[idx0].cert.B.ToDouble(),
             axes500[idx0].center.y.ToDouble() / axes500[idx0].cert.B.ToDouble(),
             axes500[idx0].center.z.ToDouble() / axes500[idx0].cert.B.ToDouble()};
  vec3 u2 = {axes500[idx1].center.x.ToDouble() / axes500[idx1].cert.B.ToDouble(),
             axes500[idx1].center.y.ToDouble() / axes500[idx1].cert.B.ToDouble(),
             axes500[idx1].center.z.ToDouble() / axes500[idx1].cert.B.ToDouble()};
  vec3 u3 = {axes500[idx2].center.x.ToDouble() / axes500[idx2].cert.B.ToDouble(),
             axes500[idx2].center.y.ToDouble() / axes500[idx2].cert.B.ToDouble(),
             axes500[idx2].center.z.ToDouble() / axes500[idx2].cert.B.ToDouble()};

  // Find the fail points where u1 < 0.005, u2 < 0.005, u3 < 0.005:
  int N = 100000;
  std::vector<vec3> fail_pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    if (yocto::dot(a, u1) < 0.005 &&
        yocto::dot(a, u2) < 0.005 &&
        yocto::dot(a, u3) < 0.005) {
      fail_pts.push_back(a);
    }
  }
  std::cout << "Number of fail points: " << fail_pts.size() << " / " << N << "\n";

  // Generate candidate contacts:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {200, 400, 500, 600, 800}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
  }

  int C = cand_contacts.size();
  std::vector<vec3> zero_defect_vecs;
  std::vector<std::array<ContactInfo, 3>> zero_defect_triples;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          vec3 v = {center.x.ToDouble() / ax.B.ToDouble(),
                    center.y.ToDouble() / ax.B.ToDouble(),
                    center.z.ToDouble() / ax.B.ToDouble()};
          zero_defect_vecs.push_back(v);
          zero_defect_triples.push_back({triple[0], triple[1], triple[2]});
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_vecs.size() << " zero-defect axes.\n";

  // Check if ANY single axis covers ALL fail points:
  int best_cover_ax = -1;
  double best_min_dot = -1e9;
  for (size_t c = 0; c < zero_defect_vecs.size(); c++) {
    double min_d = 1e9;
    for (const auto &p : fail_pts) {
      double d = yocto::dot(p, zero_defect_vecs[c]);
      if (d < min_d) min_d = d;
    }
    if (min_d > best_min_dot) {
      best_min_dot = min_d;
      best_cover_ax = c;
    }
  }

  std::cout << "Best single zero-defect axis on fail points: index " << best_cover_ax
            << " with min dot = " << best_min_dot << "\n";

  if (best_min_dot >= 0.005) {
    std::cout << "AMAZING! Axis " << best_cover_ax << " covers ALL fail points with dot >= 0.005!\n";
  } else if (best_min_dot > 0) {
    std::cout << "Axis " << best_cover_ax << " covers ALL fail points with dot > 0 (dot = " << best_min_dot << ")!\n";
  }

  // Also check if any pair of axes covers all fail points:
  int pair_i = -1, pair_j = -1;
  double best_pair_min = -1e9;
  for (size_t i = 0; i < zero_defect_vecs.size(); i++) {
    for (size_t j = i + 1; j < zero_defect_vecs.size(); j++) {
      double min_d = 1e9;
      for (const auto &p : fail_pts) {
        double d = std::max(yocto::dot(p, zero_defect_vecs[i]), yocto::dot(p, zero_defect_vecs[j]));
        if (d < min_d) min_d = d;
      }
      if (min_d > best_pair_min) {
        best_pair_min = min_d;
        pair_i = i; pair_j = j;
      }
    }
  }
  std::cout << "Best pair of zero-defect axes on fail points: (" << pair_i << ", " << pair_j
            << ") with min dot = " << best_pair_min << "\n";

  return 0;
}
