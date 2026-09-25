#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <random>
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

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return a.x * (b.y * c.z - b.z * c.y) -
         a.y * (b.x * c.z - b.z * c.x) +
         a.z * (b.x * c.y - b.y * c.x);
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 333, 400, 500, 600, 666, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);

  struct AxisInfo {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 u;
    vec3 dir;
    double len;
  };

  std::vector<AxisInfo> zero_defect_axes;
  std::string err;
  for (size_t i = 0; i < candidates.size(); i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, candidates[i].contacts, &ax, &ctr, &del, &err, BigRat(0))) {
      AxisInfo ai;
      for (int k = 0; k < 3; k++) ai.contacts[k] = candidates[i].contacts[k];
      ai.cert = ax; ai.center = ctr; ai.delta = del;
      ai.u = {ctr.x.ToDouble() / ax.B.ToDouble(),
              ctr.y.ToDouble() / ax.B.ToDouble(),
              ctr.z.ToDouble() / ax.B.ToDouble()};
      ai.len = yocto::length(ai.u);
      ai.dir = ai.u / ai.len;
      zero_defect_axes.push_back(ai);
    }
  }

  std::cout << "Audited " << zero_defect_axes.size() << " zero-defect axes.\n";

  // Filter to diverse directions
  std::vector<AxisInfo> diverse;
  for (const auto &ax : zero_defect_axes) {
    bool dup = false;
    for (const auto &ex : diverse) {
      if (yocto::dot(ex.dir, ax.dir) > 0.98) { dup = true; break; }
    }
    if (!dup) diverse.push_back(ax);
  }
  std::cout << "Filtered to " << diverse.size() << " diverse axes.\n";

  vec3 oct[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  // Check 1: Can we find 4 axes forming a STANDARD cage for r = 1/500, c = 0.0015?
  double c_std = 0.0015;
  for (size_t i0 = 0; i0 < diverse.size(); i0++) {
    for (size_t i1 = i0 + 1; i1 < diverse.size(); i1++) {
      for (size_t i2 = i1 + 1; i2 < diverse.size(); i2++) {
        for (size_t i3 = i2 + 1; i3 < diverse.size(); i3++) {
          vec3 u0 = diverse[i0].u;
          vec3 u1 = diverse[i1].u;
          vec3 u2 = diverse[i2].u;
          vec3 u3 = diverse[i3].u;

          vec3 a = u0 - u3;
          vec3 b = u1 - u3;
          vec3 d = u2 - u3;
          double det = Det3(a, b, d);
          if (std::abs(det) < 1e-12) continue;

          vec3 y0 = -u3;
          double o0 = Det3(y0, b, d) / det;
          double o1 = Det3(a, y0, d) / det;
          double o2 = Det3(a, b, y0) / det;
          double o3 = 1.0 - o0 - o1 - o2;
          if (o0 <= 0 || o1 <= 0 || o2 <= 0 || o3 <= 0) continue;

          double max_delta = std::max({diverse[i0].delta.ToDouble(),
                                       diverse[i1].delta.ToDouble(),
                                       diverse[i2].delta.ToDouble(),
                                       diverse[i3].delta.ToDouble()});
          double target_scale = 1.75 * (c_std + max_delta);

          bool all_inside = true;
          for (int m = 0; m < 6; m++) {
            vec3 y = target_scale * oct[m] - u3;
            double l0 = Det3(y, b, d) / det;
            double l1 = Det3(a, y, d) / det;
            double l2 = Det3(a, b, y) / det;
            double l3 = 1.0 - l0 - l1 - l2;
            if (l0 <= 0 || l1 <= 0 || l2 <= 0 || l3 <= 0) { all_inside = false; break; }
          }

          if (all_inside) {
            std::cout << "FOUND STANDARD CAGE with axes " << i0 << ", " << i1 << ", " << i2 << ", " << i3 << "!\n";
            std::cout << "  max_delta = " << max_delta << ", det = " << det << "\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "No standard cage found in diverse axes. Testing decomposed cages...\n";
  return 0;
}
