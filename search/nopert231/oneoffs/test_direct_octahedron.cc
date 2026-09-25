#include <iostream>
#include <vector>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // We want to see if the convex hull of all zero-defect axes contains the 6 octahedron vertices
  // for c = 1/1000.
  // delta = 234013 / 1000000000
  // R = (7/4) * (c + delta)
  double delta = 0.000234013;
  double c = 0.001;
  double R = (7.0 / 4.0) * (c + delta);

  std::cout << "Target octahedron radius R = " << R << "\n";

  // For each direction d in S^2, the support function of the convex hull of axes is:
  // h(d) = max_i (v_i . d)
  // If h(d) >= R for ALL unit directions d, then the convex hull contains the sphere of radius R!
  // In particular, for the 6 octahedron directions (+/- x, +/- y, +/- z):
  // Does each of the 6 directions have max_i (v_i . e_k) >= R?
  // AND does the hull contain the origin?

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  vec3 dirs[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  for (int k = 0; k < 6; k++) {
    double max_d = -1e9;
    int best_i = -1;
    for (size_t i = 0; i < all_v.size(); i++) {
      double d = yocto::dot(all_v[i], dirs[k]);
      if (d > max_d) {
        max_d = d;
        best_i = i;
      }
    }
    std::cout << "Direction " << k << " (" << dirs[k].x << "," << dirs[k].y << "," << dirs[k].z << "): "
              << "max projection = " << max_d << " (R=" << R << ", margin=" << max_d - R << ")\n";
  }

  return 0;
}
