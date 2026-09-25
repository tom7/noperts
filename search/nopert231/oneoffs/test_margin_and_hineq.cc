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

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo tpl[4][3] = {
    // c0
    { MakeContact(3, 2, 2, 1, 200, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(13, 14, 14, 15, 480, 14) },
    // c1 (base 24)
    { MakeContact(2, 1, 1, 4, 0, 1),
      MakeContact(10, 15, 15, 19, 624, 15),
      MakeContact(3, 2, 2, 1, 0, 2) },
    // c2 (base 1041)
    { MakeContact(2, 1, 1, 4, 116, 1),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(10, 15, 15, 19, 200, 15) },
    // c3 (base 4074)
    { MakeContact(3, 2, 2, 1, 540, 2),
      MakeContact(8, 9, 9, 10, 200, 9),
      MakeContact(3, 2, 2, 1, 541, 2) }
  };

  int mix[4][3];
  for (int a = 0; a < 4; a++) {
    for (int k = 0; k < 3; k++) {
      mix[a][k] = tpl[a][k].mix;
    }
  }

  double delta = 0.000234013;
  double box_c = 0.000255;
  double c_cone = 0.0278;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 v[4];
  std::string err;

  auto UpdateAxis = [&](int a) -> bool {
    ContactInfo ci[3];
    for (int k = 0; k < 3; k++) {
      ci[k] = tpl[a][k];
      ci[k].mix = mix[a][k];
    }
    AxisCertificate ax;
    BigVecQ3 cnt;
    BigRat dlt;
    if (!Tube229::AuditAxis(tri, ci, &ax, &cnt, &dlt, &err, BigRat(5, 1000))) return false;
    vec3 u = {cnt.x.ToDouble() / ax.B.ToDouble(),
              cnt.y.ToDouble() / ax.B.ToDouble(),
              cnt.z.ToDouble() / ax.B.ToDouble()};
    if (a == 0) {
      v[0] = u * ((box_c + delta) / c_cone);
    } else {
      v[a] = u;
    }
    return true;
  };

  for (int a = 0; a < 4; a++) {
    if (!UpdateAxis(a)) { std::cout << "Init axis " << a << " failed\n"; return 1; }
  }

  auto Eval = [&]() -> double {
    vec3 v0 = v[0];
    vec3 d1 = v[1] - v0;
    vec3 d2 = v[2] - v0;
    vec3 d3 = v[3] - v0;
    vec3 c12 = yocto::cross(d1, d2);
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);
    double det = yocto::dot(c12, d3);
    if (std::abs(det) < 1e-12) return -1e9;
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
  };

  // Continue optimizing with step sizes 20, 10, 5, 2, 1 to maximize margin!
  double cur_score = Eval();
  std::cout << std::setprecision(10);
  std::cout << "Starting positive score: " << cur_score << "\n";

  for (int step : {20, 10, 5, 2, 1}) {
    bool step_improved = true;
    while (step_improved) {
      step_improved = false;
      for (int a = 0; a < 4; a++) {
        for (int k = 0; k < 3; k++) {
          for (int dir : {step, -step}) {
            int old_m = mix[a][k];
            int new_m = old_m + dir;
            if (new_m < 0 || new_m > 1000) continue;
            mix[a][k] = new_m;
            vec3 old_v = v[a];
            if (!UpdateAxis(a)) {
              mix[a][k] = old_m;
              v[a] = old_v;
              continue;
            }
            double s = Eval();
            if (s > cur_score) {
              cur_score = s;
              step_improved = true;
              std::cout << "Step " << step << ": Axis " << a << " contact " << k
                        << " -> " << new_m << " (score: " << cur_score << ")\n";
            } else {
              mix[a][k] = old_m;
              v[a] = old_v;
            }
          }
        }
      }
    }
  }

  std::cout << "Final maximized margin: " << cur_score << "\n";
  for (int a = 0; a < 4; a++) {
    std::cout << "Axis " << a << " mix: "
              << mix[a][0] << ", " << mix[a][1] << ", " << mix[a][2] << "\n";
  }

  // Check hineq for Axis 0
  ContactInfo ci0[3];
  for (int k = 0; k < 3; k++) {
    ci0[k] = tpl[0][k];
    ci0[k].mix = mix[0][k];
  }
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat dlt0;
  Tube229::AuditAxis(tri, ci0, &ax0, &cnt0, &dlt0, &err, BigRat(5, 1000));

  BigRat B0 = ax0.B;
  BigRat D0 = dlt0;
  BigRat r_min(1, 20); // r = 0.05
  BigRat r(1, 10);
  BigRat c_c(278, 10000);

  bool ok = Tube229::CheckAnnularDominance(B0, D0, c_c, dlt0, &r_min, &r);
  std::cout << "Tube229::CheckAnnularDominance result: " << (ok ? "TRUE" : "FALSE") << "\n";
  std::cout << "r_min = " << r_min.ToDouble() << ", r = " << r.ToDouble() << "\n";

  return 0;
}
