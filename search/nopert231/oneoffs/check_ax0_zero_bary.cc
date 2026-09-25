#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  // ax0_zero: candidate 47
  ContactInfo c0[3] = { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, contacts[47] };
  ContactInfo c1[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 500, 15}, {3, 2, 2, 1, 0, 2} };
  ContactInfo c2[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 666, 15}, {3, 2, 2, 1, 0, 2} }; // wait, what was ax2 in TestEvalRealCage.lean?
  // Let's check TestEvalRealCage.lean:
  // ax1: {2, 1, 0}, {10, 15, 500}, {3, 2, 0}
  // ax2: {2, 1, 0}, {10, 15, 666}, {3, 2, 0}
  // ax3: {2, 1, 0}, {1, 4, 333}, {15, 19, 1000}
  ContactInfo c3[3] = { {2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 333, 4}, {15, 19, 19, 3, 1000, 19} };

  AxisCertificate ax[4]; BigVecQ3 ctr[4]; BigRat del[4]; std::string err;
  Tube229::AuditAxis(tri, c0, &ax[0], &ctr[0], &del[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, c1, &ax[1], &ctr[1], &del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax[2], &ctr[2], &del[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax[3], &ctr[3], &del[3], &err, BigRat(0));

  double c_cone = 0.017;
  double c_box = 0.001;
  double delta = 0.000165;

  vec3 u0 = vec3{ctr[0].x.ToDouble() / ax[0].B.ToDouble(), ctr[0].y.ToDouble() / ax[0].B.ToDouble(), ctr[0].z.ToDouble() / ax[0].B.ToDouble()};
  vec3 v0 = ((c_box + delta) / c_cone) * u0;

  vec3 v[4];
  v[0] = v0;
  for (int j = 1; j < 4; j++) {
    v[j] = vec3{ctr[j].x.ToDouble() / ax[j].B.ToDouble(), ctr[j].y.ToDouble() / ax[j].B.ToDouble(), ctr[j].z.ToDouble() / ax[j].B.ToDouble()};
  }

  std::cout << "v[0] = (" << v[0].x << ", " << v[0].y << ", " << v[0].z << ")\n";
  std::cout << "v[1] = (" << v[1].x << ", " << v[1].y << ", " << v[1].z << ")\n";
  std::cout << "v[2] = (" << v[2].x << ", " << v[2].y << ", " << v[2].z << ")\n";
  std::cout << "v[3] = (" << v[3].x << ", " << v[3].y << ", " << v[3].z << ")\n";

  // Check 6 targets: ±1.75 * (c_box + delta) * e_i
  double R = 1.75 * (c_box + delta);
  vec3 targets[6] = {
    {+R, 0, 0}, {-R, 0, 0},
    {0, +R, 0}, {0, -R, 0},
    {0, 0, +R}, {0, 0, -R}
  };

  vec3 d0 = v[0] - v[3];
  vec3 d1 = v[1] - v[3];
  vec3 d2 = v[2] - v[3];
  double det = Det3(d0, d1, d2);
  std::cout << "det = " << det << "\n";

  for (int k = 0; k < 6; k++) {
    vec3 dp = targets[k] - v[3];
    double b0 = Det3(dp, d1, d2) / det;
    double b1 = Det3(d0, dp, d2) / det;
    double b2 = Det3(d0, d1, dp) / det;
    double b3 = 1.0 - b0 - b1 - b2;
    std::cout << "Target " << k << ": b = (" << b0 << ", " << b1 << ", " << b2 << ", " << b3 << ")\n";
  }

  return 0;
}
