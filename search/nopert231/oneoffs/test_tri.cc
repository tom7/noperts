#include <cstdio>
#include <iostream>
#include "tubetree229.h"

using namespace tubetree229;

static const std::string_view VERTICES_Q[20][3] = {
  {"17136292830659/400000000000000", "5680663556187131/10000000000000000", "5648167326177671/10000000000000000"},
  {"-42773513204957/250000000000000", "9384169756351713/10000000000000000", "4802676718449/16000000000000"},
  {"-2791996671138589/10000000000000000", "8916783831939151/10000000000000000", "-420605170858861/10000000000000000"},
  {"581211699562287/10000000000000000", "602579091333187/1000000000000000", "-382169975802723/500000000000000"},
  {"-5270246949360691/10000000000000000", "2162861152231751/10000000000000000", "5648167326177671/10000000000000000"},
  {"-4726792748188159/5000000000000000", "1272666794475643/10000000000000000", "4802676718449/16000000000000"},
  {"-1868627957476221/2000000000000000", "12511388959529/1250000000000000", "-420605170858861/10000000000000000"},
  {"-2775631710731053/5000000000000000", "1207418485492689/5000000000000000", "-382169975802723/500000000000000"},
  {"-921399766144207/2500000000000000", "-1085985462790287/2500000000000000", "5648167326177671/10000000000000000"},
  {"-4131696624115331/10000000000000000", "-2149404605253097/2500000000000000", "4802676718449/16000000000000"},
  {"-7455953197761/25000000000000", "-8854924122951479/10000000000000000", "-420605170858861/10000000000000000"},
  {"-4012081174529903/10000000000000000", "-2266669793986531/5000000000000000", "-382169975802723/500000000000000"},
  {"46756585289803/156250000000000", "-4847564861402479/10000000000000000", "5648167326177671/10000000000000000"},
  {"1380011310293969/2000000000000000", "-411642950060219/625000000000000", "4802676718449/16000000000000"},
  {"3749963394741599/5000000000000000", "-5572735187461599/10000000000000000", "-420605170858861/10000000000000000"},
  {"767915222494757/2500000000000000", "-10188661950973/19531250000000", "-382169975802723/500000000000000"},
  {"5535017234623651/10000000000000000", "673991002072371/5000000000000000", "5648167326177671/10000000000000000"},
  {"1679233219444017/2000000000000000", "2263534535574267/5000000000000000", "4802676718449/16000000000000"},
  {"1523518189628179/2000000000000000", "2705392183398847/5000000000000000", "-420605170858861/10000000000000000"},
  {"5910472006450693/10000000000000000", "327326655638497/2500000000000000", "-382169975802723/500000000000000"}
};

struct QPoly {
  BigRat c[10];
  QPoly() {
    for (int i = 0; i < 10; i++) c[i] = BigRat(0);
  }
  static QPoly MulLinear(const Vec3Q &a, const Vec3Q &b) {
    QPoly p;
    p.c[4] = a.x * b.x;
    p.c[5] = a.x * b.y + a.y * b.x;
    p.c[6] = a.x * b.z + a.z * b.x;
    p.c[7] = a.y * b.y;
    p.c[8] = a.y * b.z + a.z * b.y;
    p.c[9] = a.z * b.z;
    return p;
  }
  void AddScaled(const BigRat &s, const QPoly &o) {
    for (int i = 0; i < 10; i++) c[i] += s * o.c[i];
  }
  std::pair<BigRat, BigRat> EvalCentered(const Vec3Q &center, const Vec3Q &radius) const {
    BigRat val = c[0] + c[1] * center.x + c[2] * center.y + c[3] * center.z +
                 c[4] * center.x * center.x + c[5] * center.x * center.y +
                 c[6] * center.x * center.z + c[7] * center.y * center.y +
                 c[8] * center.y * center.z + c[9] * center.z * center.z;

    BigRat grad_x = c[1] + BigRat(2) * c[4] * center.x + c[5] * center.y + c[6] * center.z;
    BigRat grad_y = c[2] + c[5] * center.x + BigRat(2) * c[7] * center.y + c[8] * center.z;
    BigRat grad_z = c[3] + c[6] * center.x + c[8] * center.y + BigRat(2) * c[9] * center.z;

    auto abs_r = [](const BigRat &x) { return x < 0 ? -x : x; };

    BigRat lin_bound = abs_r(grad_x) * radius.x + abs_r(grad_y) * radius.y + abs_r(grad_z) * radius.z;
    BigRat quad_bound = abs_r(c[4]) * radius.x * radius.x + abs_r(c[5]) * radius.x * radius.y +
                        abs_r(c[6]) * radius.x * radius.z + abs_r(c[7]) * radius.y * radius.y +
                        abs_r(c[8]) * radius.y * radius.z + abs_r(c[9]) * radius.z * radius.z;
    return {val, lin_bound + quad_bound};
  }
};

static Vec3Q GetExactEdge(const ContactInfo &c) {
  Vec3Q v_start(VERTICES_Q[c.edge_start][0], VERTICES_Q[c.edge_start][1], VERTICES_Q[c.edge_start][2]);
  Vec3Q v_finish(VERTICES_Q[c.edge_finish][0], VERTICES_Q[c.edge_finish][1], VERTICES_Q[c.edge_finish][2]);
  Vec3Q v_start2(VERTICES_Q[c.edge_start2][0], VERTICES_Q[c.edge_start2][1], VERTICES_Q[c.edge_start2][2]);
  Vec3Q v_finish2(VERTICES_Q[c.edge_finish2][0], VERTICES_Q[c.edge_finish2][1], VERTICES_Q[c.edge_finish2][2]);
  BigRat mixQ(c.mix, 1000);
  return (v_start - v_finish) * mixQ + (v_start2 - v_finish2) * (BigRat(1) - mixQ);
}

static bool Barycentric4(const Vec3Q pts[4], const Vec3Q &target, BigRat lam[4]) {
  Vec3Q v0 = pts[0] - pts[3];
  Vec3Q v1 = pts[1] - pts[3];
  Vec3Q v2 = pts[2] - pts[3];
  Vec3Q w = target - pts[3];
  BigRat den = Vec3Q::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = Vec3Q::Det(w, v1, v2) / den;
  lam[1] = Vec3Q::Det(v0, w, v2) / den;
  lam[2] = Vec3Q::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

int main() {
  TriangleQ tri = TriangleFromPath("3101031");
  ContactInfo axes_contacts[4][3] = {
    {
      ContactInfo{.edge_start = 8, .edge_finish = 9, .edge_start2 = 9, .edge_finish2 = 13, .mix = 200, .vertex = 9},
      ContactInfo{.edge_start = 13, .edge_finish = 14, .edge_start2 = 14, .edge_finish2 = 19, .mix = 0, .vertex = 14},
      ContactInfo{.edge_start = 2, .edge_finish = 5, .edge_start2 = 5, .edge_finish2 = 8, .mix = 1000, .vertex = 5}
    },
    {
      ContactInfo{.edge_start = 9, .edge_finish = 13, .edge_start2 = 13, .edge_finish2 = 14, .mix = 800, .vertex = 13},
      ContactInfo{.edge_start = 13, .edge_finish = 14, .edge_start2 = 14, .edge_finish2 = 19, .mix = 0, .vertex = 14},
      ContactInfo{.edge_start = 19, .edge_finish = 3, .edge_start2 = 3, .edge_finish2 = 2, .mix = 0, .vertex = 3}
    },
    {
      ContactInfo{.edge_start = 9, .edge_finish = 13, .edge_start2 = 13, .edge_finish2 = 14, .mix = 800, .vertex = 13},
      ContactInfo{.edge_start = 13, .edge_finish = 14, .edge_start2 = 14, .edge_finish2 = 19, .mix = 0, .vertex = 14},
      ContactInfo{.edge_start = 3, .edge_finish = 2, .edge_start2 = 2, .edge_finish2 = 5, .mix = 0, .vertex = 2}
    },
    {
      ContactInfo{.edge_start = 9, .edge_finish = 13, .edge_start2 = 13, .edge_finish2 = 14, .mix = 800, .vertex = 13},
      ContactInfo{.edge_start = 14, .edge_finish = 19, .edge_start2 = 19, .edge_finish2 = 3, .mix = 0, .vertex = 19},
      ContactInfo{.edge_start = 2, .edge_finish = 5, .edge_start2 = 5, .edge_finish2 = 8, .mix = 1000, .vertex = 5}
    }
  };

  BigRat Bs[4] = {
    BigRat("2112657239/1000000000"),
    BigRat("184472551/100000000"),
    BigRat("2055389341/1000000000"),
    BigRat("1697528997/1000000000")
  };

  Vec3Q ball_center, ball_radius;
  for (int c = 0; c < 3; c++) {
    BigRat c0 = (c == 0 ? tri.corners[0].x : c == 1 ? tri.corners[0].y : tri.corners[0].z);
    BigRat c1 = (c == 0 ? tri.corners[1].x : c == 1 ? tri.corners[1].y : tri.corners[1].z);
    BigRat c2 = (c == 0 ? tri.corners[2].x : c == 1 ? tri.corners[2].y : tri.corners[2].z);
    BigRat lo = std::min({c0, c1, c2});
    BigRat hi = std::max({c0, c1, c2});
    BigRat mid = (lo + hi) / BigRat(2);
    BigRat rad = (hi - lo) / BigRat(2);
    if (c == 0) { ball_center.x = mid; ball_radius.x = rad; }
    else if (c == 1) { ball_center.y = mid; ball_radius.y = rad; }
    else { ball_center.z = mid; ball_radius.z = rad; }
  }

  Vec3Q centers[4];
  for (int a = 0; a < 4; a++) {
    Vec3Q edges[3] = {GetExactEdge(axes_contacts[a][0]), GetExactEdge(axes_contacts[a][1]), GetExactEdge(axes_contacts[a][2])};
    Vec3Q w_coeffs[3] = {
      Vec3Q::Cross(edges[1], edges[2]),
      Vec3Q::Cross(edges[2], edges[0]),
      Vec3Q::Cross(edges[0], edges[1])
    };
    QPoly polys[3];
    for (int coord = 0; coord < 3; coord++) {
      for (int i = 0; i < 3; i++) {
        Vec3Q v_supp(VERTICES_Q[axes_contacts[a][i].vertex][0],
                     VERTICES_Q[axes_contacts[a][i].vertex][1],
                     VERTICES_Q[axes_contacts[a][i].vertex][2]);
        Vec3Q lift_row[3] = {
          {BigRat(0), edges[i].z, -edges[i].y},
          {-edges[i].z, BigRat(0), edges[i].x},
          {edges[i].y, -edges[i].x, BigRat(0)}
        };
        Vec3Q cross_lift;
        if (coord == 0) {
          cross_lift = {v_supp.y * lift_row[2].x - v_supp.z * lift_row[1].x,
                        v_supp.y * lift_row[2].y - v_supp.z * lift_row[1].y,
                        v_supp.y * lift_row[2].z - v_supp.z * lift_row[1].z};
        } else if (coord == 1) {
          cross_lift = {v_supp.z * lift_row[0].x - v_supp.x * lift_row[2].x,
                        v_supp.z * lift_row[0].y - v_supp.x * lift_row[2].y,
                        v_supp.z * lift_row[0].z - v_supp.x * lift_row[2].z};
        } else {
          cross_lift = {v_supp.x * lift_row[1].x - v_supp.y * lift_row[0].x,
                        v_supp.x * lift_row[1].y - v_supp.y * lift_row[0].y,
                        v_supp.x * lift_row[1].z - v_supp.y * lift_row[0].z};
        }
        QPoly term = QPoly::MulLinear(w_coeffs[i], cross_lift);
        polys[coord].AddScaled(BigRat(1), term);
      }
    }
    std::pair<BigRat, BigRat> evals[3] = {
      polys[0].EvalCentered(ball_center, ball_radius),
      polys[1].EvalCentered(ball_center, ball_radius),
      polys[2].EvalCentered(ball_center, ball_radius)
    };
    centers[a] = {evals[0].first / Bs[a], evals[1].first / Bs[a], evals[2].first / Bs[a]};
    printf("C++ center %d: (%s, %s, %s)\n", a, centers[a].x.ToString().c_str(), centers[a].y.ToString().c_str(), centers[a].z.ToString().c_str());
  }

  BigRat c("130143/200000000");
  BigRat delta("4427967/1000000000");
  BigRat scale = (c + delta) * BigRat(7, 4);
  printf("scale = %s\n", scale.ToString().c_str());
  for (int k = 0; k < 6; k++) {
    Vec3Q target;
    if (k == 0) target = {scale, BigRat(0), BigRat(0)};
    else if (k == 1) target = {-scale, BigRat(0), BigRat(0)};
    else if (k == 2) target = {BigRat(0), scale, BigRat(0)};
    else if (k == 3) target = {BigRat(0), -scale, BigRat(0)};
    else if (k == 4) target = {BigRat(0), BigRat(0), scale};
    else if (k == 5) target = {BigRat(0), BigRat(0), -scale};

    BigRat lam[4];
    bool ok = Barycentric4(centers, target, lam);
    printf("target %d: ok=%d lam=[%s, %s, %s, %s]\n", k, ok,
           lam[0].ToString().c_str(), lam[1].ToString().c_str(), lam[2].ToString().c_str(), lam[3].ToString().c_str());
  }
  return 0;
}
