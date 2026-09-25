#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  vec3 v = {0.0205096, 0.931624, 0.362843};
  auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, true);

  std::vector<Tube229::AuditedAxis> audited;
  for (const auto &cand : cands) {
    ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      audited.push_back({cert, center, delta});
    }
  }

  std::cout << "Audited " << audited.size() << " axes\n";
  int idx[3] = {7, 11, 22};
  for (int m = 0; m < 3; m++) {
    int i = idx[m];
    vec3 u = {audited[i].center.x.ToDouble() / audited[i].cert.B.ToDouble(),
              audited[i].center.y.ToDouble() / audited[i].cert.B.ToDouble(),
              audited[i].center.z.ToDouble() / audited[i].cert.B.ToDouble()};
    std::cout << "Axis " << i << ": B=" << audited[i].cert.B.ToDouble()
              << " u=(" << u.x << ", " << u.y << ", " << u.z << ")\n";
    for (int c = 0; c < 3; c++) {
      std::cout << "  contact " << c << ": v=" << audited[i].cert.contacts[c].vertex
                << " mix=" << audited[i].cert.contacts[c].mix << "\n";
    }
  }

  double delta = 3.33e-7;
  double c_cone = 0.028;
  vec3 u1 = {audited[7].center.x.ToDouble() / audited[7].cert.B.ToDouble(),
             audited[7].center.y.ToDouble() / audited[7].cert.B.ToDouble(),
             audited[7].center.z.ToDouble() / audited[7].cert.B.ToDouble()};
  vec3 u2 = {audited[11].center.x.ToDouble() / audited[11].cert.B.ToDouble(),
             audited[11].center.y.ToDouble() / audited[11].cert.B.ToDouble(),
             audited[11].center.z.ToDouble() / audited[11].cert.B.ToDouble()};
  vec3 u3 = {audited[22].center.x.ToDouble() / audited[22].cert.B.ToDouble(),
             audited[22].center.y.ToDouble() / audited[22].cert.B.ToDouble(),
             audited[22].center.z.ToDouble() / audited[22].cert.B.ToDouble()};

  std::vector<vec3> oct_dirs = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  for (double box_c : {1e-3, 1e-4, 1e-5, 1e-6, 1e-7}) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
    vec3 c12 = yocto::cross(d1, d2);
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);
    double det = yocto::dot(c12, d3);

    double min_all = 1e9;
    for (int k = 0; k < 6; k++) {
      vec3 dp = oct_dirs[k] * R - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(dp, c31) / det;
      double l3 = yocto::dot(dp, c12) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      min_all = std::min({min_all, l0, l1, l2, l3});
    }
    vec3 dp = -v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(dp, c31) / det;
    double l3 = yocto::dot(dp, c12) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "box_c = " << box_c << ": min_l = " << min_all
              << ", origin = (" << l0 << ", " << l1 << ", " << l2 << ", " << l3 << ")\n";
  }

  return 0;
}
