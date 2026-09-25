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

struct AxisInfo {
  ContactInfo contacts[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 dir;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // coreAxis from test_full_box_03121303200.lean:
  ContactInfo core_c[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  if (!Tube229::AuditAxis(tri, core_c, &core_cert, &core_center, &core_delta, &err, BigRat(0))) {
    std::cout << "coreAxis audit failed: " << err << "\n";
    return 1;
  }
  std::cout << "coreAxis audited OK! B = " << core_cert.B.ToString() << "\n";
  BigVecQ3 u_core_ex = core_center / core_cert.B;
  vec3 u_core = yocto::normalize(vec3{u_core_ex.x.ToDouble(), u_core_ex.y.ToDouble(), u_core_ex.z.ToDouble()});
  std::cout << "coreAxis direction: (" << u_core.x << ", " << u_core.y << ", " << u_core.z << ")\n";

  std::cout << "Harvesting all zero-defect candidates...\n";
  std::vector<AxisInfo> pool;
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
        AxisInfo info;
        info.contacts[0] = contacts[0];
        info.contacts[1] = contacts[1];
        info.contacts[2] = contacts[2];
        info.cert = cert;
        info.center = center;
        info.delta = delta;
        info.dir = u_vec;
        pool.push_back(info);
      }
    }
  }

  // Find enclosed pool axes closest to coreAxis:
  struct Cand {
    int idx;
    double angle_deg;
    double margin;
  };
  std::vector<Cand> cands;

  for (size_t i = 0; i < pool.size(); i++) {
    vec3 target_ray = -pool[i].dir;
    vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
    vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
    vec3 ey = yocto::cross(target_ray, ex);

    int num_angles = 36;
    double min_support = 1e9;

    for (int a = 0; a < num_angles; a++) {
      double theta = a * 2.0 * M_PI / num_angles;
      double dir_x = std::cos(theta);
      double dir_y = std::sin(theta);

      double max_proj = -1e9;
      for (size_t j = 0; j < pool.size(); j++) {
        if (i == j) continue;
        double dot_t = yocto::dot(pool[j].dir, target_ray);
        if (dot_t > 0.05) {
          double qx = yocto::dot(pool[j].dir, ex) / dot_t;
          double qy = yocto::dot(pool[j].dir, ey) / dot_t;
          double proj = dir_x * qx + dir_y * qy;
          if (proj > max_proj) max_proj = proj;
        }
      }
      if (max_proj < min_support) min_support = max_proj;
    }

    if (min_support > 0) {
      double dot = std::clamp(yocto::dot(pool[i].dir, u_core), -1.0, 1.0);
      double angle = std::acos(dot) * 180.0 / M_PI;
      cands.push_back({(int)i, angle, min_support});
    }
  }

  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.angle_deg < b.angle_deg;
  });

  std::cout << "Top 10 closest enclosed axes to coreAxis:\n";
  for (int i = 0; i < std::min(10, (int)cands.size()); i++) {
    const auto &c = cands[i];
    std::cout << "Axis " << c.idx << ": angle = " << c.angle_deg
              << " deg, cone margin = " << c.margin
              << ", dir = (" << pool[c.idx].dir.x << ", " << pool[c.idx].dir.y
              << ", " << pool[c.idx].dir.z << ")\n";
  }

  return 0;
}
