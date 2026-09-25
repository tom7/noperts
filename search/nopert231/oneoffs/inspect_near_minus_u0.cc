#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // u0 from test_full_box_03121303200.lean or canyon:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 280, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 395, 15)
  };
  AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0));
  BigVecQ3 u0_ex = cnt0 / ax0.B;
  vec3 u0 = yocto::normalize(vec3{u0_ex.x.ToDouble(), u0_ex.y.ToDouble(), u0_ex.z.ToDouble()});
  vec3 target_ray = -u0;

  std::cout << "Target ray -u0 = (" << target_ray.x << ", " << target_ray.y << ", " << target_ray.z << ")\n";

  // Harvest all zero-defect candidates:
  struct Cand {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    vec3 v;
    double dot_target;
  };

  std::vector<Cand> pool;
  int N = 80;
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
        BigVecQ3 u_ex = center / cert.B;
        vec3 u_vec = yocto::normalize(vec3{u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()});
        double d = yocto::dot(u_vec, target_ray);
        pool.push_back({ {contacts[0], contacts[1], contacts[2]}, cert, center, u_vec, d });
      }
    }
  }

  std::cout << "Total zero-defect axes: " << pool.size() << "\n";

  // Filter those with dot_target > 0.5 (within 60 degrees of -u0):
  std::vector<Cand> near_target;
  for (const auto& c : pool) {
    if (c.dot_target > 0.0) {
      near_target.push_back(c);
    }
  }
  std::cout << "Axes with dot(-u0) > 0: " << near_target.size() << "\n";

  // Sort by dot_target descending:
  std::sort(near_target.begin(), near_target.end(), [](const Cand& a, const Cand& b) {
    return a.dot_target > b.dot_target;
  });

  std::cout << "Max dot(-u0): " << near_target[0].dot_target << "\n";
  for (int i = 0; i < std::min((int)near_target.size(), 10); i++) {
    std::cout << "  #" << i << " dot=" << near_target[i].dot_target
              << " v=(" << near_target[i].v.x << ", " << near_target[i].v.y << ", " << near_target[i].v.z << ")\n";
  }

  return 0;
}
