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
  std::string err;

  // Zero-defect Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 400, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 390, 15)
  };
  AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0));
  BigVecQ3 u0_exact = cnt0 / ax0.B;
  vec3 u0 = {u0_exact.x.ToDouble(), u0_exact.y.ToDouble(), u0_exact.z.ToDouble()};

  vec3 n = yocto::normalize(u0);
  vec3 up = {0, 0, 1};
  if (std::abs(yocto::dot(n, up)) > 0.9) up = {1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(up, n));
  vec3 ey = yocto::cross(n, ex);

  std::cout << "Harvesting and inspecting angles...\n";
  int count_trans = 0;
  double min_ang = 1000, max_ang = -1000;

  int N = 50;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto candidates = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : candidates) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        vec3 u_vec = {center.x.ToDouble() / cert.B.ToDouble(),
                      center.y.ToDouble() / cert.B.ToDouble(),
                      center.z.ToDouble() / cert.B.ToDouble()};
        double px = yocto::dot(u_vec, ex);
        double py = yocto::dot(u_vec, ey);
        double trans_len = std::hypot(px, py);
        if (trans_len > 0.001) {
          double ang = std::atan2(py, px) * 180.0 / M_PI;
          if (ang < min_ang) min_ang = ang;
          if (ang > max_ang) max_ang = ang;
          count_trans++;
        }
      }
    }
  }

  std::cout << "Count: " << count_trans << ", min_ang = " << min_ang << " deg, max_ang = " << max_ang << " deg\n";
  return 0;
}
