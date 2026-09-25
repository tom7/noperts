#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

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

  // Stored comps 1 and 2
  ContactInfo ct1[3] = { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15) };
  ContactInfo ct2[3] = { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(4, 8, 8, 9, 800, 8), MakeContact(14, 15, 15, 19, 800, 15) };

  AxisCertificate ax1, ax2;
  BigVecQ3 ctr1, ctr2;
  BigRat del1, del2;
  Tube229::AuditAxis(tri, ct1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, ct2, &ax2, &ctr2, &del2, &err, BigRat(0));
  vec3 p2 = {ctr1.x.ToDouble(), ctr1.y.ToDouble(), ctr1.z.ToDouble()};
  vec3 p3 = {ctr2.x.ToDouble(), ctr2.y.ToDouble(), ctr2.z.ToDouble()};

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

  for (const auto &c_cand : all_cands) {
    ContactInfo ct[3] = {c_cand.contacts[0], c_cand.contacts[1], c_cand.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (!Tube229::AuditAxis(tri, ct, &ax, &ctr, &del, &err, BigRat(0))) continue;
    vec3 p1 = {ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()};

    vec3 d0 = p0 - p3;
    vec3 d1 = p1 - p3;
    vec3 d2 = p2 - p3;
    double det = Det3(d0, d1, d2);
    if (std::abs(det) < 1e-7) continue;

    vec3 dp = -p3;
    double b0 = Det3(dp, d1, d2) / det;
    double b1 = Det3(d0, dp, d2) / det;
    double b2 = Det3(d0, d1, dp) / det;
    double b3 = 1.0 - b0 - b1 - b2;

    if (b0 > 0.01 && b1 > 0.01 && b2 > 0.01 && b3 > 0.01) {
      std::cout << "FOUND WINNING CAGE! b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << "\n";
      std::cout << "  p1 = (" << p1.x << ", " << p1.y << ", " << p1.z << ")\n";
      std::cout << "  Contact 0: (" << ct[0].edge_start << "->" << ct[0].edge_finish << ", mix=" << ct[0].mix << ", v=" << ct[0].vertex << ")\n";
      std::cout << "  Contact 1: (" << ct[1].edge_start << "->" << ct[1].edge_finish << ", mix=" << ct[1].mix << ", v=" << ct[1].vertex << ")\n";
      std::cout << "  Contact 2: (" << ct[2].edge_start << "->" << ct[2].edge_finish << ", mix=" << ct[2].mix << ", v=" << ct[2].vertex << ")\n";
      return 0;
    }
  }

  std::cout << "Trying replacement of ct1 or ct2...\n";
  return 0;
}
