#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c0 = c_cone / norm_u0; // ~ 0.210027
  double R = std::sqrt(1.0 / (c0 * c0) - 1.0); // ~ 4.655
  double c_core = 0.0008;
  double target_gamma = c_core / c0; // ~ 0.003809

  std::vector<int> flock_indices = {391, 3058, 13, 3053, 74, 4893, 4907};
  struct AxisLinear {
    int id;
    double A, B, C;
  };
  std::vector<AxisLinear> al;
  for (int idx : flock_indices) {
    vec3 v = yocto::normalize(vec3{axes[idx].center.x.ToDouble(),
                                  axes[idx].center.y.ToDouble(),
                                  axes[idx].center.z.ToDouble()});
    al.push_back({idx, yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Regular 16-gon enclosing the disk of radius R
  int N_sides = 64;
  double R_outer = R / std::cos(M_PI / N_sides);
  std::vector<Point2D> base_poly;
  for (int i = 0; i < N_sides; i++) {
    double ang = 2.0 * M_PI * i / N_sides;
    base_poly.push_back({R_outer * std::cos(ang), R_outer * std::sin(ang)});
  }

  std::cout << "Base enclosing polygon has " << base_poly.size() << " vertices, R_outer = " << R_outer << "\n";

  for (size_t k = 0; k < al.size(); k++) {
    std::vector<Point2D> poly = base_poly;
    for (size_t j = 0; j < al.size(); j++) {
      if (j == k) continue;
      // Halfplane: (A_k - A_j) + (B_k - B_j)*x + (C_k - C_j)*y >= 0
      double a = al[k].B - al[j].B;
      double b = al[k].C - al[j].C;
      double c = al[k].A - al[j].A;
      poly = ClipPolygon(poly, a, b, c);
    }
    std::cout << "Axis " << al[k].id << " territory polygon has " << poly.size() << " vertices.\n";
    // Check minimum dot product at all vertices
    double min_f = 1e9;
    for (const auto& p : poly) {
      double f = al[k].A + al[k].B * p.x + al[k].C * p.y;
      if (f < min_f) min_f = f;
    }
    std::cout << "  Min dot on projective plane: " << min_f
              << " (need target_gamma = " << target_gamma << ")\n";
  }

  return 0;
}
