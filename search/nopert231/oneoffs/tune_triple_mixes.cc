#include <iostream>
#include <vector>
#include <iomanip>
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
  double box_c = 0.00026;
  double c_cone = 0.028;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };
  vec3 v0 = u0 * ((box_c + delta) / c_cone);

  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(2, 1, 1, 4, 333, 1)
  };
  ContactInfo c2[3] = {
    MakeContact(3, 2, 2, 1, 0, 2),
    MakeContact(8, 9, 9, 10, 200, 9),
    MakeContact(19, 3, 3, 2, 0, 3)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 500, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 666, 15)
  };

  auto Eval = [&](const vec3& v1, const vec3& v2, const vec3& v3) -> double {
    vec3 d1 = v1 - v0;
    vec3 d2 = v2 - v0;
    vec3 d3 = v3 - v0;
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

  AxisCertificate ax1, ax2, ax3;
  BigVecQ3 cnt1, cnt2, cnt3;
  BigRat dlt1, dlt2, dlt3;
  Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &dlt1, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &dlt2, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &dlt3, &err, BigRat(5, 1000));

  vec3 v1 = {cnt1.x.ToDouble() / ax1.B.ToDouble(), cnt1.y.ToDouble() / ax1.B.ToDouble(), cnt1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 v2 = {cnt2.x.ToDouble() / ax2.B.ToDouble(), cnt2.y.ToDouble() / ax2.B.ToDouble(), cnt2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 v3 = {cnt3.x.ToDouble() / ax3.B.ToDouble(), cnt3.y.ToDouble() / ax3.B.ToDouble(), cnt3.z.ToDouble() / ax3.B.ToDouble()};

  double cur_min_l = Eval(v1, v2, v3);
  std::cout << "Initial min_l: " << cur_min_l << "\n";

  // Try perturbing each mix
  int best_m[3][3] = {
    {c1[0].mix, c1[1].mix, c1[2].mix},
    {c2[0].mix, c2[1].mix, c2[2].mix},
    {c3[0].mix, c3[1].mix, c3[2].mix}
  };

  bool improved = true;
  while (improved) {
    improved = false;
    for (int axis = 0; axis < 3; axis++) {
      for (int k = 0; k < 3; k++) {
        for (int delta_mix : {-50, -20, -10, -5, 5, 10, 20, 50}) {
          int old_m = best_m[axis][k];
          int new_m = old_m + delta_mix;
          if (new_m < 0 || new_m > 1000) continue;

          ContactInfo tc[3];
          for (int i = 0; i < 3; i++) {
            tc[i] = (axis == 0 ? c1[i] : (axis == 1 ? c2[i] : c3[i]));
            tc[i].mix = best_m[axis][i];
          }
          tc[k].mix = new_m;

          AxisCertificate tax;
          BigVecQ3 tcnt;
          BigRat tdlt;
          if (!Tube229::AuditAxis(tri, tc, &tax, &tcnt, &tdlt, &err, BigRat(5, 1000))) continue;
          vec3 tv = {tcnt.x.ToDouble() / tax.B.ToDouble(),
                     tcnt.y.ToDouble() / tax.B.ToDouble(),
                     tcnt.z.ToDouble() / tax.B.ToDouble()};

          vec3 tv1 = (axis == 0 ? tv : v1);
          vec3 tv2 = (axis == 1 ? tv : v2);
          vec3 tv3 = (axis == 2 ? tv : v3);

          double score = Eval(tv1, tv2, tv3);
          if (score > cur_min_l) {
            cur_min_l = score;
            best_m[axis][k] = new_m;
            if (axis == 0) v1 = tv;
            else if (axis == 1) v2 = tv;
            else v3 = tv;
            std::cout << "Improved min_l: " << cur_min_l << " (axis " << axis << " contact " << k << " mix " << new_m << ")\n";
            improved = true;
            if (cur_min_l > 0) {
              std::cout << "SUCCESS! min_l > 0 reached!\n";
              goto done;
            }
          }
        }
      }
    }
  }
done:
  std::cout << "Final min_l: " << cur_min_l << "\n";
  std::cout << "Mixes:\n";
  for (int a = 0; a < 3; a++) {
    std::cout << "Axis " << a << ": " << best_m[a][0] << ", " << best_m[a][1] << ", " << best_m[a][2] << "\n";
  }

  return 0;
}
