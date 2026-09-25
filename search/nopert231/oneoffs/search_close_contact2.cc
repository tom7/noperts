#include <iostream>
#include <iomanip>
#include <vector>
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

  // Axis 0 target direction:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {cnt0.x.ToDouble() / ax0.B.ToDouble(),
             cnt0.y.ToDouble() / ax0.B.ToDouble(),
             cnt0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "Searching for zero-defect Contact 2 close to Axis 0...\n";

  // Silhouette pairs of edges that meet at a vertex:
  struct EdgePair {
    int e1_s, e1_f, e2_s, e2_f, v;
  };

  std::vector<EdgePair> pairs;
  // Edges around 14, 15, 10, 19, 18:
  int adj_v[] = {10, 13, 14, 15, 18, 19};
  // Let's test all directed edges in nopert229
  // In nopert229, edges are 0..23 vertices
  for (int v : adj_v) {
    for (int e1_s = 0; e1_s < 24; e1_s++) {
      for (int e2_f = 0; e2_f < 24; e2_f++) {
        if (e1_s != v && e2_f != v && e1_s != e2_f) {
          pairs.push_back({e1_s, v, v, e2_f, v});
        }
      }
    }
  }

  double min_angle = 180.0;
  EdgePair best_pair;
  int best_m = -1;

  for (const auto& p : pairs) {
    for (int m : {0, 250, 500, 750, 1000}) {
      ContactInfo cc[3] = {
        MakeContact(3, 2, 2, 1, 150, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(p.e1_s, p.e1_f, p.e2_s, p.e2_f, m, p.v)
      };
      AxisCertificate axc;
      BigVecQ3 cntc;
      BigRat delc;
      if (Tube229::AuditAxis(tri, cc, &axc, &cntc, &delc, &err, BigRat(0))) {
        vec3 uc = {cntc.x.ToDouble() / axc.B.ToDouble(),
                   cntc.y.ToDouble() / axc.B.ToDouble(),
                   cntc.z.ToDouble() / axc.B.ToDouble()};
        double dot = yocto::dot(u0, uc) / (yocto::length(u0) * yocto::length(uc));
        double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
        if (angle < min_angle) {
          min_angle = angle;
          best_pair = p;
          best_m = m;
          std::cout << "Found better zero-defect contact! angle=" << angle << " deg, dot=" << dot
                    << " edge=(" << p.e1_s << "->" << p.e1_f << ", " << p.e2_s << "->" << p.e2_f << ", mix " << m << ", v " << p.v << ")\n";
        }
      }
    }
  }

  std::cout << "Best pair angle: " << min_angle << " deg\n";
  return 0;
}
