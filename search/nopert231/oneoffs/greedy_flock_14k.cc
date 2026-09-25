#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Point2D {
  double x, y;
};

struct Halfplane {
  double a, b, c; // a*x + b*y + c >= 0
};

std::vector<Point2D> ClipPolygon(const std::vector<Point2D> &poly, const Halfplane &hp) {
  std::vector<Point2D> out;
  if (poly.empty()) return out;
  auto eval = [&](const Point2D &p) { return hp.a * p.x + hp.b * p.y + hp.c; };
  for (size_t i = 0; i < poly.size(); i++) {
    Point2D cur = poly[i];
    Point2D next = poly[(i + 1) % poly.size()];
    double e_cur = eval(cur);
    double e_next = eval(next);
    if (e_cur >= -1e-12) {
      out.push_back(cur);
    }
    if ((e_cur > 1e-12 && e_next < -1e-12) || (e_cur < -1e-12 && e_next > 1e-12)) {
      double t = e_cur / (e_cur - e_next);
      out.push_back({cur.x + t * (next.x - cur.x), cur.y + t * (next.y - cur.y)});
    }
  }
  return out;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double R_disk = std::sqrt(1.0 - c_cone * c_cone) / c_cone;

  // 64-gon tangent to disk
  int N_sides = 64;
  std::vector<Point2D> base_poly;
  double R_outer = R_disk / std::cos(M_PI / N_sides);
  for (int i = 0; i < N_sides; i++) {
    double phi = (i + 0.5) * (2.0 * M_PI / N_sides);
    base_poly.push_back({R_outer * std::cos(phi), R_outer * std::sin(phi)});
  }

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };

  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, true, 4, true, 1e-12);
  std::cout << "Loaded " << cands.size() << " candidates.\n";

  struct AxisLinear {
    int id;
    double A, B, C;
  };
  std::vector<AxisLinear> all_al;
  for (size_t i = 0; i < cands.size(); i++) {
    vec3 v = cands[i].normalized_a;
    all_al.push_back({(int)i, yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Seed with 6 diverse axes
  std::vector<int> flock_indices = {14060};
  // Add 5 more widely separated candidates:
  for (int step = 0; step < 5; step++) {
    int idx = (cands.size() / 6) * (step + 1);
    flock_indices.push_back(idx);
  }

  for (int iter = 0; iter < 40; iter++) {
    std::cout << "--- Iteration " << iter << ": Flock size = " << flock_indices.size() << " ---\n";
    std::vector<AxisLinear> flock;
    for (int idx : flock_indices) {
      flock.push_back(all_al[idx]);
    }

    double global_min_dot = 1e9;
    Point2D worst_pt = {0, 0};
    int worst_axis = -1;

    for (size_t k = 0; k < flock.size(); k++) {
      std::vector<Point2D> poly = base_poly;
      for (size_t m = 0; m < flock.size(); m++) {
        if (m == k) continue;
        Halfplane hp = {
          flock[k].B - flock[m].B,
          flock[k].C - flock[m].C,
          flock[k].A - flock[m].A
        };
        poly = ClipPolygon(poly, hp);
        if (poly.empty()) break;
      }
      if (poly.empty()) continue;

      for (const auto &p : poly) {
        double norm = std::sqrt(1.0 + p.x * p.x + p.y * p.y);
        double sphere_dot = (flock[k].A + flock[k].B * p.x + flock[k].C * p.y) / norm;
        if (sphere_dot < global_min_dot) {
          global_min_dot = sphere_dot;
          worst_pt = p;
          worst_axis = flock[k].id;
        }
      }
    }

    std::cout << "Global min sphere dot: " << std::scientific << std::setprecision(6) << global_min_dot
              << " at (" << worst_pt.x << ", " << worst_pt.y << ") on cand " << worst_axis << "\n";

    if (global_min_dot > 1e-5) {
      std::cout << "SUCCESS! Minimum margin everywhere strictly positive: " << global_min_dot << " > 1e-5!\n";
      break;
    }

    // Find best candidate in all_al at worst_pt
    double best_val = -1e9;
    int best_idx = -1;
    for (size_t i = 0; i < all_al.size(); i++) {
      double val = all_al[i].A + all_al[i].B * worst_pt.x + all_al[i].C * worst_pt.y;
      if (val > best_val) {
        best_val = val;
        best_idx = i;
      }
    }
    std::cout << "Adding cand " << best_idx << " with dot on plane = " << best_val << "\n";
    bool found = false;
    for (int idx : flock_indices) {
      if (idx == best_idx) { found = true; break; }
    }
    if (found) {
      std::cout << "Cand " << best_idx << " already in flock! Stopping.\n";
      break;
    }
    flock_indices.push_back(best_idx);
  }

  std::cout << "\nFinal flock indices:\n{";
  for (size_t i = 0; i < flock_indices.size(); i++) {
    std::cout << flock_indices[i] << (i + 1 < flock_indices.size() ? ", " : "}\n");
  }

  return 0;
}
