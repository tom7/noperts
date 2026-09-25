#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  ContactInfo c1[3] = {
    MakeContact(18, 1, 1, 5, 200, 1),
    MakeContact(9, 10, 10, 15, 270, 10),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo c2[3] = {
    MakeContact(15, 19, 19, 3, 290, 19),
    MakeContact(5, 8, 8, 9, 600, 8),
    MakeContact(15, 19, 19, 3, 600, 19)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 130, 2),
    MakeContact(2, 1, 1, 5, 420, 1),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  std::vector<ContactInfo> contacts = {
    c0[0], c0[1], c0[2],
    c1[0], c1[1], c1[2],
    c2[0], c2[1], c2[2],
    c3[0], c3[1], c3[2]
  };

  TubeCertificate cert;
  std::string err;
  // Let's test if FindDecomposedBarycentric can find barycentric coords for c_cone
  // Let's sweep c_cone
  for (double c = 0.005; c <= 0.050; c += 0.005) {
    BigRat c_cone(std::round(c * 1000.0), 1000);
    // Audit each axis:
    AxisCertificate ax[4];
    BigVecQ3 ctr[4];
    BigRat del[4];
    bool ok = true;
    for (int j = 0; j < 4; j++) {
      if (!Tube229::AuditAxis(tri, &contacts[j*3], &ax[j], &ctr[j], &del[j], &err, BigRat(0))) {
        ok = false;
        break;
      }
    }
    if (!ok) {
      std::cout << "Audit failed\n";
      break;
    }
    // Check if origin can be enclosed by convex combination of {u0, u1, u2, u3}
    // and if the 6 octahedron vertices can be enclosed
    std::vector<vec3> pts;
    for (int j = 0; j < 4; j++) {
      pts.push_back(vec3{ctr[j].x.ToDouble() / ax[j].B.ToDouble(),
                         ctr[j].y.ToDouble() / ax[j].B.ToDouble(),
                         ctr[j].z.ToDouble() / ax[j].B.ToDouble()});
    }
    // Octahedron targets: (7/4)*(c_cone + delta)*e_k
    double c_target = (7.0 / 4.0) * (c + 0.0001);
    vec3 targets[6] = {
      vec3{c_target, 0, 0}, vec3{-c_target, 0, 0},
      vec3{0, c_target, 0}, vec3{0, -c_target, 0},
      vec3{0, 0, c_target}, vec3{0, 0, -c_target}
    };
    bool all_in = true;
    for (int t = 0; t < 6; t++) {
      // Check if target t is in convex hull of pts
      // We can check if PointInTetrahedron(targets[t], pts[0], pts[1], pts[2], pts[3])
      double margin = 0;
      if (!Tube229::PointInTetrahedron(targets[t], pts[0], pts[1], pts[2], pts[3], &margin) || margin < 0) {
        all_in = false;
        break;
      }
    }
    std::cout << "c_cone = " << c << ": " << (all_in ? "ENCLOSED!" : "outside") << "\n";
  }

  return 0;
}
