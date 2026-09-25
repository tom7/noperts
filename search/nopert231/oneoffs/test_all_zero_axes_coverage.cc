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
  std::string target = "03121303022";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo cont0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  AxisCertificate ax0;
  BigVecQ3 c0;
  BigRat d0;
  std::string err;
  Tube229::AuditAxis(tri, cont0, &ax0, &c0, &d0, &err, BigRat(5, 1000));
  vec3 u0 = {c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};

  // Generate candidate zero-defect axes
  vec3 view = {tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()};
  auto cands = Tube229::GenerateCandidatesForView(view, tri, false, 5, false);
  std::cout << "Generated " << cands.size() << " candidates\n";

  std::vector<vec3> zero_axes;
  for (const auto &cand : cands) {
    ContactInfo cont[3] = {
      cand.contacts[0],
      cand.contacts[1],
      cand.contacts[2]
    };
    AxisCertificate ax;
    BigVecQ3 c;
    BigRat d;
    if (Tube229::AuditAxis(tri, cont, &ax, &c, &d, &err, BigRat(0))) {
      zero_axes.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
    }
  }
  std::cout << "Valid zero-defect axes: " << zero_axes.size() << "\n";

  for (double c_cone : {0.060, 0.055, 0.050, 0.045, 0.040, 0.035}) {
    double min_cover_all = 999.0;
    int N = 200000;
    for (int i = 0; i < N; i++) {
      double z = 1.0 - 2.0 * (i + 0.5) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

      if (yocto::dot(a, u0) >= c_cone) continue;

      double max_d = -999.0;
      for (const auto &u : zero_axes) {
        double d = yocto::dot(a, u);
        if (d > max_d) max_d = d;
      }
      if (max_d < min_cover_all) min_cover_all = max_d;
    }

    std::cout << "c_cone = " << c_cone << ": min coverage outside cone = "
              << min_cover_all << "\n";
  }

  return 0;
}
