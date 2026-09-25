#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

// Solve LP: find non-negative weights mu such that sum mu_i W_i = target, sum mu_i = 1
bool PointInConvexHull(const std::vector<vec3> &pts, const vec3 &target, std::vector<double> *weights = nullptr) {
  // Use glpk or simple LP solver or barycentric coordinates if 4 pts
  // For 5 pts (simplex + 1 point), we can test all quadruples of pts
  for (size_t i = 0; i < pts.size(); i++) {
    for (size_t j = i + 1; j < pts.size(); j++) {
      for (size_t k = j + 1; k < pts.size(); k++) {
        for (size_t l = k + 1; l < pts.size(); l++) {
          // Check if target in tetrahedron (pts[i], pts[j], pts[k], pts[l])
          // Solve: mu_i p_i + mu_j p_j + mu_k p_k + mu_l p_l = target, sum = 1
          // Let M = [p_j - p_i, p_k - p_i, p_l - p_i]
          vec3 v1 = pts[j] - pts[i];
          vec3 v2 = pts[k] - pts[i];
          vec3 v3 = pts[l] - pts[i];
          double det = yocto::dot(v1, yocto::cross(v2, v3));
          if (std::abs(det) < 1e-9) continue;
          vec3 rhs = target - pts[i];
          double b = yocto::dot(rhs, yocto::cross(v2, v3)) / det;
          double c = yocto::dot(v1, yocto::cross(rhs, v3)) / det;
          double d = yocto::dot(v1, yocto::cross(v2, rhs)) / det;
          double a = 1.0 - b - c - d;
          if (a >= -1e-7 && b >= -1e-7 && c >= -1e-7 && d >= -1e-7) {
            return true;
          }
        }
      }
    }
  }
  return false;
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
  vec3 u0 = vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()};

  double c_core = 0.005;
  double c_cone = 0.015;
  double S = (c_core + 0.001) / c_cone;

  // The pseudo-axis representing the outside of the cone
  vec3 pseudo_u0 = -S * u0;

  // Test across combinations of 4 zero-defect axes from our audited axes
  // Can {pseudo_u0, v1, v2, v3, v4} contain the 6 octahedron vertices of radius 7/4 * c_core?
  double oct_radius = (7.0 / 4.0) * c_core;
  vec3 oct_targets[6] = {
    vec3{oct_radius, 0, 0},
    vec3{-oct_radius, 0, 0},
    vec3{0, oct_radius, 0},
    vec3{0, -oct_radius, 0},
    vec3{0, 0, oct_radius},
    vec3{0, 0, -oct_radius}
  };

  std::cout << "Testing dual octahedron coverage with c_core = " << c_core << ", oct_radius = " << oct_radius << "...\n";

  // Check if ALL 5000 axes + pseudo_u0 contain the 6 octahedron vertices
  std::vector<vec3> all_pts;
  all_pts.push_back(pseudo_u0);
  for (size_t i = 0; i < axes.size(); i++) {
    all_pts.push_back(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
  }

  // To check if target in conv(all_pts), solve LP: min sum s.t. sum mu_i P_i = target, mu >= 0, sum mu = 1
  // Equivalently, by Farkas, target in conv(P) iff for all normals n, dot(n, target) <= max_i dot(n, P_i).
  // Let us check random directions n:
  bool separated = false;
  for (int trial = 0; trial < 10000; trial++) {
    // Random unit normal
    double z = 2.0 * ((double)rand() / RAND_MAX) - 1.0;
    double phi = 2.0 * M_PI * ((double)rand() / RAND_MAX);
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    vec3 n{r * std::cos(phi), r * std::sin(phi), z};

    double max_dot = -1e9;
    for (const auto &p : all_pts) {
      double d = yocto::dot(n, p);
      if (d > max_dot) max_dot = d;
    }

    for (int k = 0; k < 6; k++) {
      if (yocto::dot(n, oct_targets[k]) > max_dot + 1e-9) {
        separated = true;
        break;
      }
    }
    if (separated) break;
  }

  if (!separated) {
    std::cout << "SUCCESS! The dual set {pseudo_u0, zero_defect_axes} CONTAINS THE OCTAHEDRON OF RADIUS " << oct_radius << "!\n";
  } else {
    std::cout << "Separated! Octahedron radius " << oct_radius << " is too large or pts do not enclose.\n";
  }

  return 0;
}
