#include <iostream>
#include <vector>
#include <string>
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

  // Annular axis replaced by the ZERO-DEFECT axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  // Complement axes:
  const auto &dc = *node->decomposed_cert;
  AxisCertificate ax_comp[3];
  BigVecQ3 ctr_comp[3];
  BigRat del_comp[3];
  for (int i = 0; i < 3; i++) {
    ContactInfo c[3] = {dc.complement_axes[i].contacts[0], dc.complement_axes[i].contacts[1], dc.complement_axes[i].contacts[2]};
    Tube229::AuditAxis(tri, c, &ax_comp[i], &ctr_comp[i], &del_comp[i], &err, BigRat(0));
  }

  // Print double-precision centers:
  vec3 u[4];
  u[0] = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
          ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
          ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  for (int i = 0; i < 3; i++) {
    u[i+1] = {ctr_comp[i].x.ToDouble() / ax_comp[i].B.ToDouble(),
              ctr_comp[i].y.ToDouble() / ax_comp[i].B.ToDouble(),
              ctr_comp[i].z.ToDouble() / ax_comp[i].B.ToDouble()};
  }

  std::cout << "Center 0: " << u[0].x << ", " << u[0].y << ", " << u[0].z << " (len " << yocto::length(u[0]) << ")\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "Center " << (i+1) << ": " << u[i+1].x << ", " << u[i+1].y << ", " << u[i+1].z << " (len " << yocto::length(u[i+1]) << ")\n";
  }

  // Octahedron axes (from LocalCertificate.lean):
  // (+-1, 0, 0), (0, +-1, 0), (0, 0, +-1)
  vec3 oct[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  double delta = del_ann.ToDouble();

  vec3 p[4];
  p[0] = u[0];
  p[1] = u[1];
  p[2] = u[2];
  p[3] = u[3];

  vec3 a = p[0] - p[3];
  vec3 b = p[1] - p[3];
  vec3 d = p[2] - p[3];
  double det = yocto::dot(a, yocto::cross(b, d));
  std::cout << "Tetrahedron det: " << det << "\n";

  vec3 y0 = -p[3];
  double l0 = yocto::dot(y0, yocto::cross(b, d)) / det;
  double l1 = yocto::dot(a, yocto::cross(y0, d)) / det;
  double l2 = yocto::dot(a, yocto::cross(b, y0)) / det;
  double l3 = 1.0 - l0 - l1 - l2;
  std::cout << "Origin bary: " << l0 << ", " << l1 << ", " << l2 << ", " << l3 << "\n";

  return 0;
}
