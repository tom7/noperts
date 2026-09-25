#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Point2D {
  double x, y;
};

struct Triangle2D {
  Point2D v[3];
};

struct AxisLinear {
  int id;
  double A, B, C;
};

static std::vector<AxisLinear> all_al;

// Return index of an axis that is > 0 on all 3 vertices, or -1
int FindCoveringAxis(const Triangle2D &t, double min_val = 1e-6) {
  for (size_t i = 0; i < all_al.size(); i++) {
    double m0 = all_al[i].A + all_al[i].B * t.v[0].x + all_al[i].C * t.v[0].y;
    if (m0 <= min_val) continue;
    double m1 = all_al[i].A + all_al[i].B * t.v[1].x + all_al[i].C * t.v[1].y;
    if (m1 <= min_val) continue;
    double m2 = all_al[i].A + all_al[i].B * t.v[2].x + all_al[i].C * t.v[2].y;
    if (m2 > min_val) return i;
  }
  return -1;
}

int total_leaves = 0;
int max_depth_reached = 0;

bool SubdivideAndCover(const Triangle2D &t, int depth, int max_depth) {
  int cov = FindCoveringAxis(t);
  if (cov >= 0) {
    total_leaves++;
    if (depth > max_depth_reached) max_depth_reached = depth;
    return true;
  }
  if (depth >= max_depth) {
    return false;
  }

  // Subdivide triangle into 4 smaller triangles by midpoint splitting:
  Point2D m01 = {(t.v[0].x + t.v[1].x) * 0.5, (t.v[0].y + t.v[1].y) * 0.5};
  Point2D m12 = {(t.v[1].x + t.v[2].x) * 0.5, (t.v[1].y + t.v[2].y) * 0.5};
  Point2D m20 = {(t.v[2].x + t.v[0].x) * 0.5, (t.v[2].y + t.v[0].y) * 0.5};

  Triangle2D sub[4] = {
    {t.v[0], m01, m20},
    {t.v[1], m12, m01},
    {t.v[2], m20, m12},
    {m01, m12, m20}
  };

  for (int i = 0; i < 4; i++) {
    if (!SubdivideAndCover(sub[i], depth + 1, max_depth)) return false;
  }
  return true;
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

  double c_cone = 0.035;
  double R_disk = std::sqrt(1.0 - c_cone * c_cone) / c_cone; // ~28.55
  std::cout << "For c_cone = " << c_cone << ", R_disk = " << R_disk << "\n";

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };

  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, true, 4, true, 1e-12);
  for (size_t i = 0; i < cands.size(); i++) {
    vec3 v = cands[i].normalized_a;
    all_al.push_back({(int)i, yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Base mesh: N_rings=30, N_sectors=128
  int N_rings = 30;
  int N_sectors = 128;
  std::vector<Triangle2D> mesh;

  double r1 = R_disk / N_rings;
  for (int s = 0; s < N_sectors; s++) {
    double th0 = s * 2.0 * M_PI / N_sectors;
    double th1 = (s + 1) * 2.0 * M_PI / N_sectors;
    mesh.push_back({
      Point2D{0, 0},
      Point2D{r1 * std::cos(th0), r1 * std::sin(th0)},
      Point2D{r1 * std::cos(th1), r1 * std::sin(th1)}
    });
  }

  for (int ring = 1; ring < N_rings; ring++) {
    double ra = ring * R_disk / N_rings;
    double rb = (ring + 1) * R_disk / N_rings;
    for (int s = 0; s < N_sectors; s++) {
      double th0 = s * 2.0 * M_PI / N_sectors;
      double th1 = (s + 1) * 2.0 * M_PI / N_sectors;
      Point2D p0a = {ra * std::cos(th0), ra * std::sin(th0)};
      Point2D p1a = {ra * std::cos(th1), ra * std::sin(th1)};
      Point2D p0b = {rb * std::cos(th0), rb * std::sin(th0)};
      Point2D p1b = {rb * std::cos(th1), rb * std::sin(th1)};
      mesh.push_back({p0a, p0b, p1b});
      mesh.push_back({p0a, p1b, p1a});
    }
  }

  std::cout << "Base mesh: " << mesh.size() << " triangles.\n";
  int success = 0;
  for (size_t t = 0; t < mesh.size(); t++) {
    if (SubdivideAndCover(mesh[t], 0, 14)) {
      success++;
    } else {
      std::cout << "Base triangle " << t << " failed to close within depth 8!\n";
    }
  }

  std::cout << "Success: " << success << " / " << mesh.size() << " base triangles!\n";
  std::cout << "Total leaf triangles: " << total_leaves << "\n";
  std::cout << "Max depth reached: " << max_depth_reached << "\n";

  return 0;
}
