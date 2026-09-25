#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

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

  // In test_flock_polygons, find the vertex where dot ~ -7.42e-5
  // Let's test the 6 axes: 391, 3058, 13, 3053, 74, 4893
  std::vector<int> flock_indices = {391, 3058, 13, 3053, 74, 4893};
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

  // Find all pairwise intersection of 3 lines:
  // For triples of axes (i, j, k):
  // Line ij: (A_i - A_j) + (B_i - B_j) x + (C_i - C_j) y = 0
  // Line jk: (A_j - A_k) + (B_j - B_k) x + (C_j - C_k) y = 0
  for (size_t i = 0; i < al.size(); i++) {
    for (size_t j = i + 1; j < al.size(); j++) {
      for (size_t k = j + 1; k < al.size(); k++) {
        double a1 = al[i].B - al[j].B, b1 = al[i].C - al[j].C, c1 = al[i].A - al[j].A;
        double a2 = al[j].B - al[k].B, b2 = al[j].C - al[k].C, c2 = al[j].A - al[k].A;
        double det = a1 * b2 - a2 * b1;
        if (std::abs(det) < 1e-9) continue;
        double x = (-c1 * b2 + c2 * b1) / det;
        double y = (-a1 * c2 + a2 * c1) / det;

        // Check if this point is in the Voronoi cell of i, j, k (i.e. dot products are equal and >= others)
        double fi = al[i].A + al[i].B * x + al[i].C * y;
        bool is_voronoi = true;
        for (size_t m = 0; m < al.size(); m++) {
          double fm = al[m].A + al[m].B * x + al[m].C * y;
          if (fm > fi + 1e-6) {
            is_voronoi = false;
            break;
          }
        }
        if (is_voronoi && fi < 0.0038) {
          std::cout << "Triple vertex (" << al[i].id << ", " << al[j].id << ", " << al[k].id
                    << ") at (" << x << ", " << y << "), fi = " << fi << "\n";
          // Find best axis in all 5000 axes at this point
          vec3 pt_3d = yocto::normalize(u0 + x * e1 + y * e2);
          int best_ax = -1;
          double best_d = -1e9;
          for (size_t ax = 0; ax < axes.size(); ax++) {
            vec3 v = yocto::normalize(vec3{axes[ax].center.x.ToDouble(),
                                          axes[ax].center.y.ToDouble(),
                                          axes[ax].center.z.ToDouble()});
            double d = yocto::dot(pt_3d, v);
            if (d > best_d) {
              best_d = d;
              best_ax = ax;
            }
          }
          std::cout << "  Best axis from 5000: " << best_ax << " with dot = " << best_d << "\n";
        }
      }
    }
  }

  return 0;
}
