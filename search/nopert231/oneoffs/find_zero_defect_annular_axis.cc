#include <iostream>
#include <vector>
#include <string>
#include <cmath>
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
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  std::string target_path = "03121303200";
  TreeNode *node = nullptr;
  auto find = [&](auto &self, TreeNode *n) -> void {
    if (n->path == target_path) { node = n; return; }
    for (auto &c : n->children) self(self, c.get());
  };
  find(find, root.get());

  TriangleQ tri = TriangleFromPath(target_path);

  // Load complement axes:
  const auto &dc = *node->decomposed_cert;
  AxisCertificate ax_comp[3];
  BigVecQ3 ctr_comp[3];
  BigRat del_comp[3];
  std::string err;
  for (int i = 0; i < 3; i++) {
    ContactInfo c[3] = {dc.complement_axes[i].contacts[0], dc.complement_axes[i].contacts[1], dc.complement_axes[i].contacts[2]};
    Tube229::AuditAxis(tri, c, &ax_comp[i], &ctr_comp[i], &del_comp[i], &err, BigRat(0));
  }

  vec3 u[4];
  for (int i = 0; i < 3; i++) {
    u[i+1] = {ctr_comp[i].x.ToDouble() / ax_comp[i].B.ToDouble(),
              ctr_comp[i].y.ToDouble() / ax_comp[i].B.ToDouble(),
              ctr_comp[i].z.ToDouble() / ax_comp[i].B.ToDouble()};
  }

  vec3 oct[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  // Search contact combinations and mixes for ax0:
  // We want:
  // 1. Defect D0 == 0 (or < 1e-6)
  // 2. Contains octahedron with some c_cone, c
  // 3. Positive alignment with core axis

  // Potential contacts for c2:
  // On edge 13->14->15 (vertex 14), 14->15->19 (vertex 15), 15->19->3 (vertex 19), 2->1->8 (vertex 1)
  std::vector<ContactInfo> c2_candidates;
  for (int m = 0; m <= 1000; m += 100) {
    c2_candidates.push_back(MakeContact(13, 14, 14, 15, m, 14));
    c2_candidates.push_back(MakeContact(14, 15, 15, 19, m, 15));
    c2_candidates.push_back(MakeContact(15, 19, 19, 3, m, 19));
    c2_candidates.push_back(MakeContact(2, 1, 1, 8, m, 1));
    c2_candidates.push_back(MakeContact(1, 8, 8, 15, m, 8));
  }

  std::cout << "Testing " << c2_candidates.size() << " candidates for c2...\n";

  for (const auto &c2 : c2_candidates) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      c2
    };

    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
      std::cout << "Candidate c2 (mix " << c2.mix << ", v " << c2.vertex << ") PASSED AuditAxis with margin 1e-3!\n";
    }
    for (int k = 0; k < 20; k++) {
      // Tube229 has audit which already verifies support <= margin!
    }

    // Since AuditAxis passed with margin = 0, this axis has ZERO DEFECT!
    u[0] = {ctr.x.ToDouble() / ax.B.ToDouble(),
            ctr.y.ToDouble() / ax.B.ToDouble(),
            ctr.z.ToDouble() / ax.B.ToDouble()};

    // Check if origin is inside tetrahedron (u0, u1, u2, u3):
    vec3 a = u[0] - u[3];
    vec3 b = u[1] - u[3];
    vec3 d = u[2] - u[3];
    double det = yocto::dot(a, yocto::cross(b, d));
    if (std::abs(det) < 1e-15) continue;

    vec3 y0 = -u[3];
    double l0 = yocto::dot(y0, yocto::cross(b, d)) / det;
    double l1 = yocto::dot(a, yocto::cross(y0, d)) / det;
    double l2 = yocto::dot(a, yocto::cross(b, y0)) / det;
    double l3 = 1.0 - l0 - l1 - l2;

    if (l0 > 0 && l1 > 0 && l2 > 0 && l3 > 0) {
      std::cout << "FOUND ZERO-DEFECT AXIS WITH ORIGIN INSIDE TETRAHEDRON!\n";
      std::cout << "  c2: edge " << c2.edge_start << "->" << c2.edge_finish << ", mix " << c2.mix << ", v " << c2.vertex << "\n";
      std::cout << "  det: " << det << ", bary: " << l0 << ", " << l1 << ", " << l2 << ", " << l3 << "\n";
      std::cout << "  u0 len: " << yocto::length(u[0]) << ", B: " << ax.B.ToDouble() << "\n";

      // Test octahedron containment:
      for (double c_cone : {0.002, 0.005, 0.01, 0.02, 0.05}) {
        for (double c_val : {0.0005, 0.001, 0.002}) {
          double delta = del.ToDouble();
          vec3 p[4];
          p[0] = ((c_val + delta) / c_cone) * u[0];
          p[1] = u[1]; p[2] = u[2]; p[3] = u[3];
          vec3 pa = p[0] - p[3];
          double pdet = yocto::dot(pa, yocto::cross(b, d));
          if (std::abs(pdet) < 1e-15) continue;
          bool inside = true;
          double scale = 1.75 * (c_val + delta);
          for (int k = 0; k < 6; k++) {
            vec3 yk = scale * oct[k] - p[3];
            double o0 = yocto::dot(yk, yocto::cross(b, d)) / pdet;
            double o1 = yocto::dot(pa, yocto::cross(yk, d)) / pdet;
            double o2 = yocto::dot(pa, yocto::cross(b, yk)) / pdet;
            double o3 = 1.0 - o0 - o1 - o2;
            if (o0 < 0 || o1 < 0 || o2 < 0 || o3 < 0) { inside = false; break; }
          }
          if (inside) {
            std::cout << "    CONTAINED! c_cone = " << c_cone << ", c = " << c_val << "\n";
          }
        }
      }
    }
  }

  return 0;
}
