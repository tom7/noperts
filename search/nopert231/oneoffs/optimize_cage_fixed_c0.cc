#include <iostream>
#include <vector>
#include <iomanip>
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

double Eval(const TriangleQ &tri, const int m[12]) {
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, m[0], 2),
    MakeContact(1, 4, 4, 8, m[1], 4),
    MakeContact(13, 14, 14, 15, m[2], 14)
  };
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, m[3], 1),
    MakeContact(10, 15, 15, 19, m[4], 15),
    MakeContact(19, 3, 3, 2, m[5], 3)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, m[6], 1),
    MakeContact(8, 9, 9, 10, m[7], 9),
    MakeContact(9, 10, 10, 15, m[8], 10)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, m[9], 2),
    MakeContact(1, 4, 4, 8, m[10], 4),
    MakeContact(10, 15, 15, 19, m[11], 15)
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat delta[4];

  for (int a = 0; a < 4; a++) {
    ContactInfo *c = (a == 0 ? c0 : (a == 1 ? c1 : (a == 2 ? c2 : c3)));
    // For a == 0, max_allowed_defect is 0!
    BigRat max_defect = (a == 0 ? BigRat(0) : BigRat(5, 1000));
    if (!Tube229::AuditAxis(tri, c, &ax[a], &cnt[a], &delta[a], &err, max_defect)) return -1e9;
    if (ax[a].B.ToDouble() < 0.05) return -1e9;
    if (delta[a].ToDouble() / ax[a].B.ToDouble() > 0.000234013) return -1e9;
  }

  vec3 u0 = {cnt[0].x.ToDouble() / ax[0].B.ToDouble(),
             cnt[0].y.ToDouble() / ax[0].B.ToDouble(),
             cnt[0].z.ToDouble() / ax[0].B.ToDouble()};
  vec3 u1 = {cnt[1].x.ToDouble() / ax[1].B.ToDouble(),
             cnt[1].y.ToDouble() / ax[1].B.ToDouble(),
             cnt[1].z.ToDouble() / ax[1].B.ToDouble()};
  vec3 u2 = {cnt[2].x.ToDouble() / ax[2].B.ToDouble(),
             cnt[2].y.ToDouble() / ax[2].B.ToDouble(),
             cnt[2].z.ToDouble() / ax[2].B.ToDouble()};
  vec3 u3 = {cnt[3].x.ToDouble() / ax[3].B.ToDouble(),
             cnt[3].y.ToDouble() / ax[3].B.ToDouble(),
             cnt[3].z.ToDouble() / ax[3].B.ToDouble()};

  double d = 0.000234013;
  double box_c = 0.000255;
  double c_cone = 0.0278;
  vec3 v0 = u0 * ((box_c + d) / c_cone);
  vec3 v1 = u1;
  vec3 v2 = u2;
  vec3 v3 = u3;

  double R = 1.75 * (box_c + d);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 d1 = v1 - v0;
  vec3 d2 = v2 - v0;
  vec3 d3 = v3 - v0;
  vec3 c12 = yocto::cross(d1, d2);
  double det = yocto::dot(c12, d3);
  if (std::abs(det) < 1e-10) return -1e9;

  vec3 c23 = yocto::cross(d2, d3);
  vec3 c31 = yocto::cross(d3, d1);

  double min_l = 1.0;
  for (int p = 0; p < 6; p++) {
    vec3 dp = oct[p] - v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(dp, c31) / det;
    double l3 = yocto::dot(dp, c12) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    min_l = std::min({min_l, l0, l1, l2, l3});
  }
  return min_l;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // m[0..2] is FIXED at pure support axis contacts [800, 800, 200]
  int m[12] = {
    800, 800, 200,   // c0 (pure support axis, D0 = 0)
    50, 800, 950,    // c1
    1000, 1000, 343, // c2
    113, 320, 150    // c3
  };

  double best_score = Eval(tri, m);
  std::cout << "Initial score with fixed c0: " << std::setprecision(10) << best_score << "\n";

  int step_sizes[] = {50, 20, 10, 5, 2, 1};
  for (int step : step_sizes) {
    bool improved = true;
    while (improved) {
      improved = false;
      // Only vary i = 3..11 (c1, c2, c3)!
      for (int i = 3; i < 12; i++) {
        for (int dir : {-step, step}) {
          int old_val = m[i];
          int next_val = old_val + dir;
          if (next_val < 0 || next_val > 1000) continue;
          m[i] = next_val;
          double score = Eval(tri, m);
          if (score > best_score) {
            best_score = score;
            improved = true;
            std::cout << "Step " << step << " improved: score=" << best_score
                      << " m[" << i << "]=" << m[i] << "\n";
          } else {
            m[i] = old_val;
          }
        }
      }
    }
  }

  std::cout << "Final best score: " << best_score << "\n";
  std::cout << "Final mixes:\n";
  std::cout << "  c0: [" << m[0] << ", " << m[1] << ", " << m[2] << "]\n";
  std::cout << "  c1: [" << m[3] << ", " << m[4] << ", " << m[5] << "]\n";
  std::cout << "  c2: [" << m[6] << ", " << m[7] << ", " << m[8] << "]\n";
  std::cout << "  c3: [" << m[9] << ", " << m[10] << ", " << m[11] << "]\n";
  return 0;
}
