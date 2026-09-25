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
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.000255;
  double c_cone = 0.0278;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };
  vec3 v0 = u0 * ((box_c + delta) / c_cone);

  int idx[3] = {24, 1041, 4074};
  ContactInfo tpl[3][3];
  int mix[3][3];
  vec3 v[3];

  for (int a = 0; a < 3; a++) {
    for (int k = 0; k < 3; k++) {
      tpl[a][k] = base_axes[idx[a]].cert.contacts[k];
      mix[a][k] = tpl[a][k].mix;
    }
  }

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
    v[a] = {cnt.x.ToDouble() / ax.B.ToDouble(),
            cnt.y.ToDouble() / ax.B.ToDouble(),
            cnt.z.ToDouble() / ax.B.ToDouble()};
    return true;
  };

  for (int a = 0; a < 3; a++) {
    if (!UpdateAxis(a)) { std::cout << "Initial axis " << a << " failed audit!\n"; return 1; }
  }

  auto Eval = [&]() -> double {
    vec3 d1 = v[0] - v0;
    vec3 d2 = v[1] - v0;
    vec3 d3 = v[2] - v0;
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

  double cur_score = Eval();
  std::cout << "Starting score: " << cur_score << "\n";

  for (int step : {50, 20, 10, 5, 2, 1}) {
    bool step_improved = true;
    while (step_improved) {
      step_improved = false;
      for (int a = 0; a < 3; a++) {
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
              if (cur_score > 0) {
                std::cout << "SUCCESS! min_l > 0!\n";
                goto finished;
              }
            } else {
              mix[a][k] = old_m;
              v[a] = old_v;
            }
          }
        }
      }
    }
  }

finished:
  std::cout << "Final score: " << cur_score << "\n";
  std::cout << "Final mixes:\n";
  for (int a = 0; a < 3; a++) {
    std::cout << "Axis " << a << " (idx " << idx[a] << "): "
              << mix[a][0] << ", " << mix[a][1] << ", " << mix[a][2] << "\n";
  }

  // Print contact info for Lean
  for (int a = 0; a < 3; a++) {
    std::cout << "\nAxis " << (a+1) << " certificate:\n";
    for (int k = 0; k < 3; k++) {
      std::cout << "Contact " << k << ": start=" << tpl[a][k].edge_start
                << " finish=" << tpl[a][k].edge_finish
                << " start2=" << tpl[a][k].edge_start2
                << " finish2=" << tpl[a][k].edge_finish2
                << " mix=" << mix[a][k]
                << " vertex=" << tpl[a][k].vertex << "\n";
    }
  }

  return 0;
}
