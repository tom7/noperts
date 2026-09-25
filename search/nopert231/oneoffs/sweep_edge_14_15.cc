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
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "Sweeping contact 2 along edge (14, 15):\n";
  for (int mix = 0; mix <= 1000; mix += 50) {
    // Test vertex 14 and vertex 15
    for (int v : {14, 15}) {
      ContactInfo cand[3] = {
        MakeContact(3, 2, 2, 1, 800, 2),
        MakeContact(1, 4, 4, 8, 800, 4),
        MakeContact(13, 14, 14, 15, mix, v)
      };
      AxisCertificate ax;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, cand, &ax, &center, &delta, &err, BigRat(1, 100))) {
        vec3 u = {center.x.ToDouble() / ax.B.ToDouble(),
                  center.y.ToDouble() / ax.B.ToDouble(),
                  center.z.ToDouble() / ax.B.ToDouble()};
        double angle = std::acos(yocto::dot(yocto::normalize(u0), yocto::normalize(u))) * 180.0 / M_PI;
        // Check defect against all 20 vertices:
        double max_defect = 0.0;
        BigVecQ3 edge = Tube229::GetExactEdge(cand[2]);
        BigVecQ3 v_sel = Tube229::VertexQ(v);
        for (int k = 0; k < 20; k++) {
          if (k == v) continue;
          BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
          BigVecQ3 s_coeff = BigVecQ3::Cross(edge, delta_v);
          BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
          for (int c = 1; c < 3; c++) {
            BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
            if (val > max_s) max_s = val;
          }
          if (max_s.ToDouble() > max_defect) max_defect = max_s.ToDouble();
        }
        std::cout << "mix=" << mix << " v=" << v << ": angle=" << angle << " deg, max_defect="
                  << max_defect << ", B=" << ax.B.ToDouble() << "\n";
      }
    }
  }

  // Also sweep edge (14, 15) to (15, 19):
  std::cout << "\nSweeping contact 2 along (14, 15) to (15, 19):\n";
  for (int mix = 0; mix <= 1000; mix += 50) {
    for (int v : {14, 15}) {
      ContactInfo cand[3] = {
        MakeContact(3, 2, 2, 1, 800, 2),
        MakeContact(1, 4, 4, 8, 800, 4),
        MakeContact(14, 15, 15, 19, mix, v)
      };
      AxisCertificate ax;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, cand, &ax, &center, &delta, &err, BigRat(1, 100))) {
        vec3 u = {center.x.ToDouble() / ax.B.ToDouble(),
                  center.y.ToDouble() / ax.B.ToDouble(),
                  center.z.ToDouble() / ax.B.ToDouble()};
        double angle = std::acos(yocto::dot(yocto::normalize(u0), yocto::normalize(u))) * 180.0 / M_PI;
        double max_defect = 0.0;
        BigVecQ3 edge = Tube229::GetExactEdge(cand[2]);
        BigVecQ3 v_sel = Tube229::VertexQ(v);
        for (int k = 0; k < 20; k++) {
          if (k == v) continue;
          BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
          BigVecQ3 s_coeff = BigVecQ3::Cross(edge, delta_v);
          BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
          for (int c = 1; c < 3; c++) {
            BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
            if (val > max_s) max_s = val;
          }
          if (max_s.ToDouble() > max_defect) max_defect = max_s.ToDouble();
        }
        std::cout << "mix=" << mix << " v=" << v << ": angle=" << angle << " deg, max_defect="
                  << max_defect << ", B=" << ax.B.ToDouble() << "\n";
      }
    }
  }

  return 0;
}
