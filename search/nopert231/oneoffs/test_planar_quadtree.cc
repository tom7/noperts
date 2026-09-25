#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct PlanarCell {
  double x0, x1, y0, y1;
  int depth;
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

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c0 = c_cone / norm_u0; // ~ 0.210027
  double R = std::sqrt(1.0 / (c0 * c0) - 1.0); // ~ 4.655
  double c_core = 0.0008;
  double target_gamma = c_core / c0; // ~ 0.003809

  struct LinearAxis {
    double A, B, C;
  };
  std::vector<LinearAxis> la;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                  axes[i].center.y.ToDouble(),
                                  axes[i].center.z.ToDouble()});
    la.push_back({yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Initial root: [-R, R] x [-R, R] split into 16x16 = 256 cells
  int N = 16;
  std::vector<PlanarCell> queue;
  for (int ix = 0; ix < N; ix++) {
    double x0 = -R + 2.0 * R * ix / N;
    double x1 = -R + 2.0 * R * (ix + 1) / N;
    for (int iy = 0; iy < N; iy++) {
      double y0 = -R + 2.0 * R * iy / N;
      double y1 = -R + 2.0 * R * (iy + 1) / N;
      queue.push_back({x0, x1, y0, y1, 0});
    }
  }

  int closed_leaves = 0;
  int outside_disk_leaves = 0;
  int max_depth = 8;
  int pending = 0;

  while (!queue.empty()) {
    PlanarCell c = queue.back();
    queue.pop_back();

    // Check if cell is completely outside disk of radius R
    double cx = (c.x0 > 0) ? c.x0 : ((c.x1 < 0) ? c.x1 : 0);
    double cy = (c.y0 > 0) ? c.y0 : ((c.y1 < 0) ? c.y1 : 0);
    if (cx * cx + cy * cy > R * R) {
      outside_disk_leaves++;
      continue;
    }

    // Check if all 4 corners are covered by the SAME axis
    bool ok = false;
    for (size_t i = 0; i < la.size(); i++) {
      double f00 = la[i].A + la[i].B * c.x0 + la[i].C * c.y0;
      double f01 = la[i].A + la[i].B * c.x0 + la[i].C * c.y1;
      double f10 = la[i].A + la[i].B * c.x1 + la[i].C * c.y0;
      double f11 = la[i].A + la[i].B * c.x1 + la[i].C * c.y1;
      if (f00 >= target_gamma && f01 >= target_gamma &&
          f10 >= target_gamma && f11 >= target_gamma) {
        ok = true;
        break;
      }
    }

    if (ok) {
      closed_leaves++;
    } else if (c.depth < max_depth) {
      double mx = 0.5 * (c.x0 + c.x1);
      double my = 0.5 * (c.y0 + c.y1);
      queue.push_back({c.x0, mx, c.y0, my, c.depth + 1});
      queue.push_back({mx, c.x1, c.y0, my, c.depth + 1});
      queue.push_back({c.x0, mx, my, c.y1, c.depth + 1});
      queue.push_back({mx, c.x1, my, c.y1, c.depth + 1});
    } else {
      pending++;
    }
  }

  std::cout << "Planar Quadtree Result:\n";
  std::cout << "  Closed cells: " << closed_leaves << "\n";
  std::cout << "  Outside disk: " << outside_disk_leaves << "\n";
  std::cout << "  Pending at depth " << max_depth << ": " << pending << "\n";

  return 0;
}
