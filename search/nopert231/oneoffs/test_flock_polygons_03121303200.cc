#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Point2D {
  double x, y;
};

// Sutherland-Hodgman polygon clipping by halfplane: a*x + b*y + c >= 0
std::vector<Point2D> ClipPolygon(const std::vector<Point2D>& poly, double a, double b, double c) {
  std::vector<Point2D> out;
  if (poly.empty()) return out;

  auto inside = [&](const Point2D& p) {
    return a * p.x + b * p.y + c >= -1e-12;
  };

  auto intersect = [&](const Point2D& p1, const Point2D& p2) {
    double d1 = a * p1.x + b * p1.y + c;
    double d2 = a * p2.x + b * p2.y + c;
    double t = d1 / (d1 - d2);
    return Point2D{p1.x + t * (p2.x - p1.x), p1.y + t * (p2.y - p1.y)};
  };

  for (size_t i = 0; i < poly.size(); i++) {
    const Point2D& cur = poly[i];
    const Point2D& prev = poly[(i + poly.size() - 1) % poly.size()];
    if (inside(cur)) {
      if (!inside(prev)) {
        out.push_back(intersect(prev, cur));
      }
      out.push_back(cur);
    } else if (inside(prev)) {
      out.push_back(intersect(prev, cur));
    }
  }
  return out;
}

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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0; // cos(alpha)
  double R = std::sqrt(1.0 / (cos_alpha * cos_alpha) - 1.0);
  double c_core = 0.0001;
  double target_gamma = c_core / cos_alpha;

  std::cout << "norm_u0 = " << norm_u0 << ", c0 = " << c0 << ", R = " << R << "\n";
  std::cout << "c_core = " << c_core << ", target_gamma = " << target_gamma << "\n";

  // Flock indices from find_minimal_flock_c0:
  // {3063, 389, 3449, 213, 25}
  std::vector<int> flock_indices = {3063, 389, 3449, 213, 25};
  struct AxisLinear {
    int id;
    double A, B, C;
  };
  std::vector<AxisLinear> al;
  for (int idx : flock_indices) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    al.push_back({idx, yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Regular N-gon enclosing the disk of radius R
  int N_sides = 32;
  double R_outer = R / std::cos(M_PI / N_sides);
  std::vector<Point2D> base_poly;
  for (int i = 0; i < N_sides; i++) {
    double ang = 2.0 * M_PI * i / N_sides;
    base_poly.push_back({R_outer * std::cos(ang), R_outer * std::sin(ang)});
  }

  std::cout << "Base enclosing polygon has " << base_poly.size() << " vertices, R_outer = " << R_outer << "\n";

  bool all_ok = true;
  for (size_t k = 0; k < al.size(); k++) {
    std::vector<Point2D> poly = base_poly;
    for (size_t j = 0; j < al.size(); j++) {
      if (j == k) continue;
      // Halfplane where axis k beats axis j:
      // (A_k - A_j) + (B_k - B_j)*x + (C_k - C_j)*y >= 0
      double a = al[k].B - al[j].B;
      double b = al[k].C - al[j].C;
      double c = al[k].A - al[j].A;
      poly = ClipPolygon(poly, a, b, c);
    }
    std::cout << "Axis " << al[k].id << " territory polygon has " << poly.size() << " vertices.\n";
    if (poly.empty()) {
      std::cout << "  (Empty territory)\n";
      continue;
    }
    double min_f = 1e9;
    for (const auto& p : poly) {
      double f = al[k].A + al[k].B * p.x + al[k].C * p.y;
      if (f < min_f) min_f = f;
    }
    std::cout << "  Min dot on projective plane: " << min_f
              << " (target_gamma = " << target_gamma << ", margin = " << min_f - target_gamma << ")\n";
    if (min_f < target_gamma) all_ok = false;
  }

  std::cout << "Overall result: " << (all_ok ? "SUCCESS! ALL TERRITORIES SATISFIED!" : "Some vertices below target") << "\n";
  return 0;
}
