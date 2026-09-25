#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Tri {
  vec3 v[3];
};

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

  std::vector<vec3> V;
  for (size_t m = 0; m < axes.size(); m++) {
    V.push_back(yocto::normalize(vec3{axes[m].center.x.ToDouble(),
                                      axes[m].center.y.ToDouble(),
                                      axes[m].center.z.ToDouble()}));
  }

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_target = 0.005;

  int N_sectors = 32;
  int N_rings = 8;
  std::vector<Tri> triangles;

  for (int r = 0; r < N_rings; r++) {
    double theta0 = (double)r / N_rings * alpha;
    double theta1 = (double)(r + 1) / N_rings * alpha;
    for (int s = 0; s < N_sectors; s++) {
      double phi0 = 2.0 * M_PI * s / N_sectors;
      double phi1 = 2.0 * M_PI * (s + 1) / N_sectors;

      auto pt = [&](double th, double ph) -> vec3 {
        return std::cos(th) * u0 + std::sin(th) * (std::cos(ph) * e1 + std::sin(ph) * e2);
      };

      vec3 p00 = pt(theta0, phi0);
      vec3 p01 = pt(theta0, phi1);
      vec3 p10 = pt(theta1, phi0);
      vec3 p11 = pt(theta1, phi1);

      if (r == 0) {
        triangles.push_back({u0, p10, p11});
      } else {
        triangles.push_back({p00, p10, p11});
        triangles.push_back({p00, p11, p01});
      }
    }
  }

  int fully_covered = 0;
  std::vector<int> used_axes;
  for (size_t t = 0; t < triangles.size(); t++) {
    int best_k = -1;
    double best_margin = -1e9;
    for (size_t k = 0; k < V.size(); k++) {
      double d0 = yocto::dot(triangles[t].v[0], V[k]);
      double d1 = yocto::dot(triangles[t].v[1], V[k]);
      double d2 = yocto::dot(triangles[t].v[2], V[k]);
      double min_d = std::min({d0, d1, d2});
      if (min_d > best_margin) {
        best_margin = min_d;
        best_k = k;
      }
    }
    if (best_margin >= c_target) {
      fully_covered++;
      used_axes.push_back(best_k);
    } else {
      std::cout << "Triangle " << t << " failed: best margin = " << best_margin << "\n";
    }
  }

  std::cout << "Triangles covered with margin >= " << c_target << ": "
            << fully_covered << " / " << triangles.size() << "\n";

  return 0;
}
