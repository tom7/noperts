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
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 2000);
  std::cout << "Found " << axes500.size() << " hull support axes.\n";

  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    vec3 c = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    pool.push_back(c);
  }

  // Generate dense points in the annulus: a . u0 in [0.005, 0.035]
  int N = 500000;
  std::vector<vec3> annulus_pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u0);
    if (dot0 >= 0.005 && dot0 <= 0.032) {
      annulus_pts.push_back(a);
    }
  }
  std::cout << "Annulus [0.005, 0.032] has " << annulus_pts.size() << " points.\n";


  // Load v_core:
  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  vec3 v_core = {core_center.x.ToDouble() / core_cert.B.ToDouble(),
                 core_center.y.ToDouble() / core_cert.B.ToDouble(),
                 core_center.z.ToDouble() / core_cert.B.ToDouble()};

  // Check if pool + v_core covers the annulus:
  double worst_cover = 1e9;
  int uncovered = 0;
  for (const auto &a : annulus_pts) {
    double best = yocto::dot(a, v_core);
    for (const auto &v : pool) {
      double d = yocto::dot(a, v);
      if (d > best) best = d;
    }
    if (best < worst_cover) worst_cover = best;
    if (best < 0.001) uncovered++;
  }

  std::cout << "Worst coverage of annulus by pool + v_core: " << worst_cover << "\n";
  std::cout << "Uncovered points (< 0.001): " << uncovered << " / " << annulus_pts.size() << "\n";

  for (const auto &a : annulus_pts) {
    double best = yocto::dot(a, v_core);
    for (const auto &v : pool) {
      double d = yocto::dot(a, v);
      if (d > best) best = d;
    }
    if (best < 0) {
      std::cout << "Negative cover point: a = (" << a.x << ", " << a.y << ", " << a.z
                << ") dot0=" << yocto::dot(a, u0) << " best=" << best << "\n";
      auto opt_ax = Tube229::FindHullSupportAxis(tri, a);
      if (opt_ax.has_value()) {
        vec3 c = {opt_ax->center.x.ToDouble() / opt_ax->cert.B.ToDouble(),
                  opt_ax->center.y.ToDouble() / opt_ax->cert.B.ToDouble(),
                  opt_ax->center.z.ToDouble() / opt_ax->cert.B.ToDouble()};
        std::cout << "Found dedicated hull support axis! dot(a, c) = " << yocto::dot(a, c)
                  << ", delta = " << opt_ax->delta.ToDouble() << "\n";
      } else {
        std::cout << "FindHullSupportAxis failed for this direction.\n";
      }
      break;
    }

  }



  return 0;
}
