#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Axis 0
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};

  // Find all zero-defect axes with contacts 0 and 1 fixed:
  std::vector<vec3> zero_defect_axes;
  for (int v2 = 0; v2 < 20; v2++) {
    for (int v1 = 0; v1 < 20; v1++) {
      if (v1 == v2) continue;
      for (int v3 = 0; v3 < 20; v3++) {
        if (v3 == v2 || v3 == v1) continue;
        for (int mix : {0, 200, 400, 600, 800, 1000}) {
          ContactInfo test_c[3] = {
            c0[0], c0[1],
            MakeContact(v1, v2, v2, v3, mix, v2)
          };
          AxisCertificate test_ax;
          BigVecQ3 test_center;
          BigRat test_delta;
          if (Tube229::AuditAxis(tri, test_c, &test_ax, &test_center, &test_delta, &err, BigRat(0))) {
            zero_defect_axes.push_back({test_center.x.ToDouble(), test_center.y.ToDouble(), test_center.z.ToDouble()});
          }
        }
      }
    }
  }
  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax_c;
    BigVecQ3 center_c;
    BigRat delta_c;
    if (Tube229::AuditAxis(tri, comp[i], &ax_c, &center_c, &delta_c, &err, BigRat(0))) {
      zero_defect_axes.push_back({center_c.x.ToDouble(), center_c.y.ToDouble(), center_c.z.ToDouble()});
    }
  }

  std::cout << "Found " << zero_defect_axes.size() << " zero-defect axes near Axis 0 + comp!\n";

  // Test coverage on annulus points:
  int N = 100000;
  int annulus_pts = 0;
  int covered_pts = 0;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u);
    if (dot0 >= 0.005 && dot0 < 0.061) {
      annulus_pts++;
      double max_d = -1e9;
      for (const auto &v : zero_defect_axes) {
        double d = yocto::dot(a, v);
        if (d > max_d) max_d = d;
      }
      if (max_d > 0.001) covered_pts++;
    }
  }

  std::cout << "Annulus points: " << annulus_pts << ", covered: " << covered_pts << " ("
            << (100.0 * covered_pts / annulus_pts) << "%)\n";

  double min_outside_margin = 1e9;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u);
    if (dot0 < 0.061) {
      double max_d = -1e9;
      for (const auto &v : zero_defect_axes) {
        double d = yocto::dot(a, v);
        if (d > max_d) max_d = d;
      }
      if (max_d < min_outside_margin) min_outside_margin = max_d;
    }
  }
  std::cout << "MINIMUM ZERO-DEFECT MARGIN OUTSIDE CONE (dot0 < 0.061): " << min_outside_margin << "\n";
  return 0;
  int print_cnt = 0;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u);
    if (dot0 >= 0.005 && dot0 < 0.061) {
      double max_d = -1e9;
      for (const auto &v : zero_defect_axes) {
        double d = yocto::dot(a, v);
        if (d > max_d) max_d = d;
      }
      if (max_d <= 0.001) {
        if (print_cnt++ < 5) {
          std::cout << "Uncovered point: (" << a.x << ", " << a.y << ", " << a.z << ") dot0=" << dot0 << " max_d=" << max_d << "\n";
        }
      }
    }
  }
  return 0;
}
