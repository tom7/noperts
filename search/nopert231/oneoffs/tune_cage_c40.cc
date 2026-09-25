#include <iostream>
#include <vector>
#include <cmath>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // From task-6208, the best axes at c_cone = 0.04 were (182, 370, 401)
  // Let us re-run the collection of all 420 axes to get exact contact definitions:
  int N = 400;
  std::vector<Tube229::AuditedAxis> all_audited;

  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : cands) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        all_audited.push_back({cert, center, delta});
      }
    }
  }

  std::vector<Tube229::AuditedAxis> diverse;
  std::vector<vec3> u_diverse;
  for (const auto &ax : all_audited) {
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    double ulen = yocto::length(u);
    if (ulen < 1e-6) continue;
    vec3 unorm = u / ulen;
    bool too_close = false;
    for (const auto &other : u_diverse) {
      if (yocto::dot(unorm, other / yocto::length(other)) > 0.996) {
        too_close = true;
        break;
      }
    }
    if (!too_close) {
      diverse.push_back(ax);
      u_diverse.push_back(u);
    }
  }

  std::cout << "Axes (182, 370, 401) contacts:\n";
  int idxs[3] = {182, 370, 401};
  for (int a = 0; a < 3; a++) {
    std::cout << "Axis " << idxs[a] << ":\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = diverse[idxs[a]].cert.contacts[m];
      std::cout << "  MakeContact(" << c.edge_start << ", " << c.edge_finish
                << ", " << c.edge_start2 << ", " << c.edge_finish2
                << ", " << c.mix << ", " << c.vertex << "),\n";
    }
  }

  return 0;
}
