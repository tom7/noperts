#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

struct Box {
  double x1, x2, y1, y2, z1, z2;
};

vec3 u0;
double c_cone = 0.015;
double c_core = 0.001;
std::vector<vec3> zd_axes;
std::vector<int> zd_idx;

int total_leaves = 0;
int out_sphere_leaves = 0;
int out_cone_leaves = 0;
int covered_leaves = 0;

struct LeafInfo {
  Box b;
  int type; // 0: out sphere, 1: out cone, 2: covered by axis
  int axis_idx;
};
std::vector<LeafInfo> tree_leaves;

bool Subdivide(Box b, int depth) {
  // 1. Check if outside unit sphere
  double min_x = (b.x1 <= 0 && b.x2 >= 0) ? 0 : std::min(std::abs(b.x1), std::abs(b.x2));
  double min_y = (b.y1 <= 0 && b.y2 >= 0) ? 0 : std::min(std::abs(b.y1), std::abs(b.y2));
  double min_z = (b.z1 <= 0 && b.z2 >= 0) ? 0 : std::min(std::abs(b.z1), std::abs(b.z2));
  double min_r2 = min_x * min_x + min_y * min_y + min_z * min_z;

  double max_x = std::max(std::abs(b.x1), std::abs(b.x2));
  double max_y = std::max(std::abs(b.y1), std::abs(b.y2));
  double max_z = std::max(std::abs(b.z1), std::abs(b.z2));
  double max_r2 = max_x * max_x + max_y * max_y + max_z * max_z;

  if (min_r2 > 1.0 || max_r2 < 1.0) {
    total_leaves++;
    out_sphere_leaves++;
    tree_leaves.push_back({b, 0, -1});
    return true;
  }

  // 2. Check if outside cone
  double max_dot_u0 = (u0.x >= 0 ? u0.x * b.x2 : u0.x * b.x1) +
                      (u0.y >= 0 ? u0.y * b.y2 : u0.y * b.y1) +
                      (u0.z >= 0 ? u0.z * b.z2 : u0.z * b.z1);
  if (max_dot_u0 < c_cone) {
    total_leaves++;
    out_cone_leaves++;
    tree_leaves.push_back({b, 1, -1});
    return true;
  }

  // 3. Check if covered by one of the zero defect axes
  for (size_t i = 0; i < zd_axes.size(); i++) {
    const auto &v = zd_axes[i];
    double min_dot_v = (v.x >= 0 ? v.x * b.x1 : v.x * b.x2) +
                       (v.y >= 0 ? v.y * b.y1 : v.y * b.y2) +
                       (v.z >= 0 ? v.z * b.z1 : v.z * b.z2);
    if (min_dot_v >= c_core) {
      total_leaves++;
      covered_leaves++;
      tree_leaves.push_back({b, 2, zd_idx[i]});
      return true;
    }
  }

  // Need subdivision
  if (depth >= 8) {
    std::cout << "Depth limit reached at box [" << b.x1 << ", " << b.x2 << "] x ["
              << b.y1 << ", " << b.y2 << "] x [" << b.z1 << ", " << b.z2 << "]\n";
    return false;
  }

  double xm = (b.x1 + b.x2) / 2.0;
  double ym = (b.y1 + b.y2) / 2.0;
  double zm = (b.z1 + b.z2) / 2.0;

  for (int ix = 0; ix < 2; ix++) {
    double x1 = ix ? xm : b.x1, x2 = ix ? b.x2 : xm;
    for (int iy = 0; iy < 2; iy++) {
      double y1 = iy ? ym : b.y1, y2 = iy ? b.y2 : ym;
      for (int iz = 0; iz < 2; iz++) {
        double z1 = iz ? zm : b.z1, z2 = iz ? b.z2 : zm;
        if (!Subdivide({x1, x2, y1, y2, z1, z2}, depth + 1)) return false;
      }
    }
  }
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0_q = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  u0 = {u0_q.x.ToDouble(), u0_q.y.ToDouble(), u0_q.z.ToDouble()};

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      zd_axes.push_back(v);
      zd_idx.push_back((int)i);
    }
  }

  std::cout << "Starting octree subdivision on [-1, 1]^3...\n";
  bool ok = Subdivide({-1, 1, -1, 1, -1, 1}, 0);
  std::cout << "Finished! Success: " << (ok ? "YES" : "NO") << "\n";
  std::cout << "Total leaves: " << total_leaves << "\n";
  std::cout << "  Out of sphere: " << out_sphere_leaves << "\n";
  std::cout << "  Out of cone: " << out_cone_leaves << "\n";
  std::cout << "  Covered by zero-defect axis: " << covered_leaves << "\n";

  return 0;
}
