#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct SphericalTri {
  vec3 p1, p2, p3;
  int axis_idx;
};

// Subdivide a triangle on the unit sphere
void Subdivide(const vec3 &p1, const vec3 &p2, const vec3 &p3, int depth, std::vector<SphericalTri> &out) {
  if (depth == 0) {
    out.push_back({p1, p2, p3, -1});
    return;
  }
  vec3 m12 = yocto::normalize(p1 + p2);
  vec3 m23 = yocto::normalize(p2 + p3);
  vec3 m31 = yocto::normalize(p3 + p1);
  Subdivide(p1, m12, m31, depth - 1, out);
  Subdivide(m12, p2, m23, depth - 1, out);
  Subdivide(m31, m23, p3, depth - 1, out);
  Subdivide(m12, m23, m31, depth - 1, out);
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0_raw = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);

  double c_cone = 0.017;
  double c_core = 0.000234013;
  double cos_cap = c_cone / norm_u0; // ~0.33269

  std::vector<std::pair<vec3, int>> candidate_v;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000234013) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      candidate_v.push_back({v, (int)i});
    }
  }
  std::cout << "Audited candidate axes: " << candidate_v.size() << "\n";

  // Build a base triangulation covering the cap.
  // u0 is the north pole.
  // Create an N-gon ring of points at colatitude slightly larger than the cap,
  // say colatitude alpha_ring where cos(alpha_ring) = cos_cap - 0.05.
  // And connect the north pole u0 to the ring to form N base triangles.
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double alpha_cap = std::acos(cos_cap);
  std::cout << "Cap half-angle: " << alpha_cap * 180.0 / M_PI << " deg\n";

  for (int N_ring : {16}) {
    for (int depth : {4}) {
      std::vector<SphericalTri> tris;
      double dphi = 2.0 * M_PI / N_ring;
      // Vertices on the boundary ring
      std::vector<vec3> ring;
      for (int i = 0; i < N_ring; i++) {
        double phi = i * dphi;
        vec3 p = std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi) * k1 + std::sin(phi) * k2);
        ring.push_back(yocto::normalize(p));
      }

      for (int i = 0; i < N_ring; i++) {
        vec3 p1 = u0;
        vec3 p2 = ring[i];
        vec3 p3 = ring[(i + 1) % N_ring];
        Subdivide(p1, p2, p3, depth, tris);
      }

      int covered = 0;
      std::set<int> distinct;
      for (auto &t : tris) {
        // Find an axis covering all 3 vertices
        int best_ax = -1;
        double best_margin = -1e9;
        for (const auto &cv : candidate_v) {
          double m1 = yocto::dot(t.p1, cv.first) - c_core;
          double m2 = yocto::dot(t.p2, cv.first) - c_core;
          double m3 = yocto::dot(t.p3, cv.first) - c_core;
          double min_m = std::min({m1, m2, m3});
          if (min_m > best_margin) {
            best_margin = min_m;
            best_ax = cv.second;
          }
        }
        if (best_margin >= 0) {
          covered++;
          t.axis_idx = best_ax;
          distinct.insert(best_ax);
        }
      }

      std::cout << "N_ring=" << N_ring << ", depth=" << depth
                << ": " << covered << " / " << tris.size() << " triangles covered"
                << " using " << distinct.size() << " distinct axes.\n";
    }
  }

  return 0;
}
