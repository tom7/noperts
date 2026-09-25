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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  std::cout << "Testing core axis with Contact 2 on (10,15,15,19):\n";
  for (int m = 0; m <= 1000; m += 50) {
    ContactInfo core_c[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(10, 15, 15, 19, m, 15)
    };
    AxisCertificate core_ax;
    BigVecQ3 core_ctr;
    BigRat core_del;
    if (Tube229::AuditAxis(tri, core_c, &core_ax, &core_ctr, &core_del, &err, BigRat(0))) {
      vec3 uc = {core_ctr.x.ToDouble() / core_ax.B.ToDouble(),
                 core_ctr.y.ToDouble() / core_ax.B.ToDouble(),
                 core_ctr.z.ToDouble() / core_ax.B.ToDouble()};
      vec3 uc_dir = yocto::normalize(uc);
      double dot = yocto::dot(u0_dir, uc_dir);
      double angle_deg = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
      std::cout << "m=" << m << ": Audit OK! B=" << core_ax.B.ToDouble()
                << ", dot=" << dot << ", angle=" << angle_deg << " deg\n";
    }
  }

  // Also test other edges for contact 2:
  std::vector<std::pair<int, int>> edges = {
    {10, 15}, {15, 19}, {19, 3}, {3, 2}, {2, 1}, {1, 4}, {4, 8}, {8, 9}, {9, 10}, {14, 15}
  };
  std::cout << "\nTesting other candidate zero-defect edges for contact 2:\n";
  for (auto e : edges) {
    for (int m : {0, 500, 1000}) {
      ContactInfo core_c[3] = {
        MakeContact(3, 2, 2, 1, 150, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(e.first, e.second, e.first, e.second, m, e.first)
      };
      AxisCertificate core_ax;
      BigVecQ3 core_ctr;
      BigRat core_del;
      if (Tube229::AuditAxis(tri, core_c, &core_ax, &core_ctr, &core_del, &err, BigRat(0))) {
        vec3 uc = {core_ctr.x.ToDouble() / core_ax.B.ToDouble(),
                   core_ctr.y.ToDouble() / core_ax.B.ToDouble(),
                   core_ctr.z.ToDouble() / core_ax.B.ToDouble()};
        vec3 uc_dir = yocto::normalize(uc);
        double dot = yocto::dot(u0_dir, uc_dir);
        double angle_deg = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
        std::cout << "edge (" << e.first << "->" << e.second << ") m=" << m
                  << ": dot=" << dot << ", angle=" << angle_deg << " deg\n";
      }
    }
  }

  return 0;
}
