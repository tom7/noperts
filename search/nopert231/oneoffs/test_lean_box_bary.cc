#include <iostream>
#include <iomanip>
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

static bool SolveTetraTarget(const BigVecQ3& p0, const BigVecQ3& p1,
                             const BigVecQ3& p2, const BigVecQ3& p3,
                             const BigVecQ3& target,
                             BigRat b[4]) {
  BigRat M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  BigRat rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

  BigRat det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (det == BigRat(0)) return false;

  BigRat d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  BigRat d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  BigRat d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  b[0] = d0 / det;
  b[1] = d1 / det;
  b[2] = d2 / det;
  b[3] = BigRat(1) - b[0] - b[1] - b[2];
  return true;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);
  std::string err;

  // Axes from test_full_box_03121303200.lean:
  ContactInfo c0[3] = {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)};
  ContactInfo c1[3] = {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(2, 1, 1, 4, 333, 1)};
  ContactInfo c2[3] = {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 666, 15), MakeContact(3, 2, 2, 1, 0, 2)};
  ContactInfo c3[3] = {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(1, 4, 4, 8, 333, 4), MakeContact(15, 19, 19, 3, 1000, 19)};

  AxisCertificate ax[4]; BigVecQ3 cnt[4]; BigRat del[4];
  std::cout << "Audit 0: " << Tube229::AuditAxis(tri, c0, &ax[0], &cnt[0], &del[0], &err, BigRat(0)) << " err=" << err << "\n";
  std::cout << "Audit 1: " << Tube229::AuditAxis(tri, c1, &ax[1], &cnt[1], &del[1], &err, BigRat(0)) << " err=" << err << "\n";
  std::cout << "Audit 2: " << Tube229::AuditAxis(tri, c2, &ax[2], &cnt[2], &del[2], &err, BigRat(0)) << " err=" << err << "\n";
  std::cout << "Audit 3: " << Tube229::AuditAxis(tri, c3, &ax[3], &cnt[3], &del[3], &err, BigRat(0)) << " err=" << err << "\n";

  BigRat box_c = BigRat(1, 1000);
  BigRat box_delta = BigRat(234013, 1000000000);
  BigRat c_cone = BigRat(15, 1000);

  // Scaled centers p:
  BigVecQ3 p[4];
  p[0] = (cnt[0] / ax[0].B) * ((box_c + box_delta) / c_cone);
  p[1] = cnt[1] / ax[1].B;
  p[2] = cnt[2] / ax[2].B;
  p[3] = cnt[3] / ax[3].B;

  std::cout << "p0 = (" << p[0].x.ToDouble() << ", " << p[0].y.ToDouble() << ", " << p[0].z.ToDouble() << ")\n";
  std::cout << "p1 = (" << p[1].x.ToDouble() << ", " << p[1].y.ToDouble() << ", " << p[1].z.ToDouble() << ")\n";
  std::cout << "p2 = (" << p[2].x.ToDouble() << ", " << p[2].y.ToDouble() << ", " << p[2].z.ToDouble() << ")\n";
  std::cout << "p3 = (" << p[3].x.ToDouble() << ", " << p[3].y.ToDouble() << ", " << p[3].z.ToDouble() << ")\n";

  // Check origin:
  BigRat b_orig[4];
  SolveTetraTarget(p[0], p[1], p[2], p[3], BigVecQ3{BigRat(0), BigRat(0), BigRat(0)}, b_orig);
  std::cout << "Origin weights: " << b_orig[0].ToDouble() << ", " << b_orig[1].ToDouble()
            << ", " << b_orig[2].ToDouble() << ", " << b_orig[3].ToDouble() << "\n";

  // Octahedron targets:
  BigRat R = BigRat(7, 4) * (box_c + box_delta);
  BigVecQ3 oct[6] = {
    {R, BigRat(0), BigRat(0)},
    {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)},
    {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R},
    {BigRat(0), BigRat(0), -R}
  };

  for (int k = 0; k < 6; k++) {
    BigRat b[4];
    SolveTetraTarget(p[0], p[1], p[2], p[3], oct[k], b);
    std::cout << "Oct target " << k << ": "
              << b[0].ToDouble() << ", " << b[1].ToDouble() << ", "
              << b[2].ToDouble() << ", " << b[3].ToDouble()
              << " (min=" << std::min({b[0].ToDouble(), b[1].ToDouble(), b[2].ToDouble(), b[3].ToDouble()}) << ")\n";
  }

  return 0;
}
