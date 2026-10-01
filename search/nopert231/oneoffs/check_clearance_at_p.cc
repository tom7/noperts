#include <iostream>
#include <vector>
#include <cmath>
#include "nopert231.h"
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

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

  double x = 1.26511, y = -0.969618;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 view = yocto::normalize(vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  });

  // Project vertices along view:
  vec3 up = std::abs(view.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 basis_x = yocto::normalize(yocto::cross(view, up));
  vec3 basis_y = yocto::cross(view, basis_x);

  std::vector<vec2> outer(20);
  for (int i = 0; i < 20; i++) {
    vec3 v = Vertex(i);
    outer[i] = vec2{yocto::dot(v, basis_x), yocto::dot(v, basis_y)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(outer);
  int H = hull.size();

  std::cout << "Outer hull has " << H << " vertices: ";
  for (int idx : hull) std::cout << idx << " ";
  std::cout << "\n";

  // Check outward normal at each edge:
  // For edge (hull[i] -> hull[i+1]):
  // Outward normal in 2D is: (dy, -dx) / len
  // For rotation around p by angle theta:
  for (double theta : {1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 0.01}) {
    // Rodrigues rotation around p:
    // R(v) = v*cos + cross(p, v)*sin + p*(p.v)*(1 - cos)
    double ct = std::cos(theta), st = std::sin(theta);
    // Find penetration across all translations:
    // To test if rotated hull penetrates outer hull without translation (t = 0):
    double max_penetration = -1e9;
    int max_v = -1, max_edge = -1;
    for (int i = 0; i < 20; i++) {
      vec3 v = Vertex(i);
      vec3 v_rot = v * ct + yocto::cross(p, v) * st + p * yocto::dot(p, v) * (1.0 - ct);
      vec2 pt_rot = vec2{yocto::dot(v_rot, basis_x), yocto::dot(v_rot, basis_y)};

      // Distance outside each hull edge:
      for (int e = 0; e < H; e++) {
        vec2 p1 = outer[hull[e]];
        vec2 p2 = outer[hull[(e + 1) % H]];
        vec2 edge_dir = p2 - p1;
        vec2 n_out = yocto::normalize(vec2{edge_dir.y, -edge_dir.x});
        // Check outward orientation (dot with (p1 - centroid) > 0)
        double d = yocto::dot(pt_rot - p1, n_out);
        if (d > max_penetration) {
          max_penetration = d;
          max_v = i;
          max_edge = e;
        }
      }
    }
    std::cout << "theta=" << theta << ": max penetration = " << max_penetration
              << " at vertex " << max_v << " past edge " << hull[max_edge] << "->" << hull[(max_edge+1)%H] << "\n";
  }

  return 0;
}
