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
  vec3 u = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};

  // Generate candidate zero-defect axes by varying contact 2, 1, and 0:
  std::vector<vec3> zero_axes;
  std::vector<ContactInfo[3]> zero_contacts;

  // Add the 3 known complement axes:
  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, comp[i], &ax, &ctr, &del, &err, BigRat(0))) {
      zero_axes.push_back({ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    }
  }

  // Vary contact 2 with c0[0], c0[1]:
  for (int v2 = 0; v2 < 20; v2++) {
    for (int v1 = 0; v1 < 20; v1++) {
      if (v1 == v2) continue;
      for (int v3 = 0; v3 < 20; v3++) {
        if (v3 == v2 || v3 == v1) continue;
        for (int mix : {0, 200, 400, 600, 800, 1000}) {
          ContactInfo test_c[3] = { c0[0], c0[1], MakeContact(v1, v2, v2, v3, mix, v2) };
          AxisCertificate ax; BigVecQ3 ctr; BigRat del;
          if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
            zero_axes.push_back({ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
          }
        }
      }
    }
  }

  // Also vary contact 1:
  for (int v2 : {1, 4, 8}) {
    for (int mix : {200, 400, 600, 800}) {
      ContactInfo test_c[3] = { c0[0], MakeContact(1, 4, 4, 8, mix, v2), MakeContact(14, 15, 15, 19, 400, 15) };
      AxisCertificate ax; BigVecQ3 ctr; BigRat del;
      if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
        zero_axes.push_back({ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      }
    }
  }

  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  for (const auto &cand : axes500) {
    zero_axes.push_back({cand.center.x.ToDouble(), cand.center.y.ToDouble(), cand.center.z.ToDouble()});
  }

  std::cout << "Total zero defect axes in pool: " << zero_axes.size() << "\n";

  // Test sphere points outside cone:
  int N = 100000;
  double min_outside = 1e9;
  vec3 worst_a = {};
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u);
    if (dot0 < 0.038) {
      double max_d = -1e9;
      for (const auto &v : zero_axes) {
        double d = yocto::dot(a, v);
        if (d > max_d) max_d = d;
      }
      if (max_d < min_outside) {
        min_outside = max_d;
        worst_a = a;
      }
    }
  }
  std::cout << "MINIMUM ZERO-DEFECT MARGIN OUTSIDE CONE (dot0 < 0.038): " << min_outside << "\n";
  std::cout << "WORST POINT: (" << worst_a.x << ", " << worst_a.y << ", " << worst_a.z
            << ") dot0=" << yocto::dot(worst_a, u) << " margin=" << min_outside << "\n";





  return 0;
}
