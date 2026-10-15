// Checks the half-turn prune of the 5D search (exact5d::HalfTurnPruneValid)
// in floating point, independently of the exact quadratic bound:
//
//   group      the 60 rounded rotations of ico-group.h map the model's vertex
//              set to itself, and the model is centrally symmetric
//   invariant  for random views u and rotations R, the clearance of (u, R)
//              equals that of (u, H_u R g) for every g (the reduction)
//   boxes      for random small boxes (view sub-triangle x Cayley box) on
//              which HalfTurnPruneValid holds for some g, sampled points
//              really have trace(H_u R g) > trace(R)
//
// Usage: halfturn-check.exe [--boxes N] [--samples N]

#include <array>
#include <cmath>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "geom5d.h"
#include "ico-group.h"
#include "model-vertices.h"
#include "rigidity-margin.h"

namespace {

using vec3 = yocto::vec<double, 3>;
// Row-major 3x3 matrices.
using M = std::array<double, 9>;

M FromYocto(const geom5d::mat3 &r) {
  M m;
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) m[3 * i + j] = r[j][i];
  return m;
}
M Mul(const M &a, const M &b) {
  M c{};
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++)
      for (int k = 0; k < 3; k++) c[3 * i + j] += a[3 * i + k] * b[3 * k + j];
  return c;
}
double Trace(const M &m) { return m[0] + m[4] + m[8]; }
M Group(int g) {
  M m;
  for (int k = 0; k < 9; k++) m[k] = (double)ICO_GROUP_NUM[g][k] / ICO_GROUP_DENOM;
  return m;
}
M HalfTurn(const vec3 &u0) {
  const vec3 u = yocto::normalize(u0);
  M h;
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) h[3 * i + j] = 2 * u[i] * u[j] - (i == j ? 1 : 0);
  return h;
}
vec3 Apply(const M &m, const vec3 &v) {
  return {m[0] * v.x + m[1] * v.y + m[2] * v.z, m[3] * v.x + m[4] * v.y + m[5] * v.z,
          m[6] * v.x + m[7] * v.y + m[8] * v.z};
}
// Axis-angle of a rotation matrix (for PassageClearance).
void AxisAngle(const M &m, vec3 *axis, double *theta) {
  *theta = std::acos(std::clamp((Trace(m) - 1) / 2, -1.0, 1.0));
  vec3 a{m[7] - m[5], m[2] - m[6], m[3] - m[1]};
  if (yocto::length(a) < 1e-9) {
    // theta ~ pi: the axis is the column of (M + I) of largest norm.
    vec3 best{0, 0, 1};
    double bn = -1;
    for (int j = 0; j < 3; j++) {
      const vec3 c{m[j] + (j == 0), m[3 + j] + (j == 1), m[6 + j] + (j == 2)};
      if (yocto::length(c) > bn) { bn = yocto::length(c); best = c; }
    }
    a = best;
  }
  *axis = yocto::normalize(a);
}

}  // namespace

int main(int argc, char **argv) {
  int num_boxes = 400, samples = 64;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    if (a == "--boxes" && i + 1 < argc) num_boxes = atoi(argv[++i]);
    else if (a == "--samples" && i + 1 < argc) samples = atoi(argv[++i]);
    else LOG(FATAL) << "usage: halfturn-check.exe [--boxes N] [--samples N]";
  }
  std::vector<vec3> verts;
  for (int i = 0; i < NUM_VERTICES_MODEL; i++) {
    const vec3 v{VERTICES_MODEL[i][0], VERTICES_MODEL[i][1], VERTICES_MODEL[i][2]};
    bool dup = false;
    for (const vec3 &w : verts) dup = dup || yocto::distance(v, w) < 1e-12;
    if (!dup) verts.push_back(v);
  }
  auto has = [&](const vec3 &v) {
    for (const vec3 &w : verts) if (yocto::distance(v, w) < 1e-9) return true;
    return false;
  };
  // group
  for (int g = 0; g < ICO_GROUP_SIZE; g++)
    for (const vec3 &v : verts) CHECK(has(Apply(Group(g), v))) << "element " << g << " is not a symmetry";
  for (const vec3 &v : verts) CHECK(has(-v)) << "the model is not centrally symmetric";
  printf("group: %d rotations preserve the %zu vertices; centrally symmetric\n", ICO_GROUP_SIZE, verts.size());

  std::mt19937_64 rng(77);
  std::uniform_real_distribution<double> U(0, 1);
  auto rand_unit = [&]() {
    for (;;) {
      const vec3 v{2 * U(rng) - 1, 2 * U(rng) - 1, 2 * U(rng) - 1};
      if (yocto::length(v) > 0.1 && yocto::length(v) < 1) return yocto::normalize(v);
    }
  };
  // invariant
  double worst = 0;
  for (int n = 0; n < 200; n++) {
    const vec3 u = rand_unit(), ax = rand_unit();
    const double th = U(rng) * M_PI;
    const M r = FromYocto(geom5d::CayleyMatrix(ax * std::tan(th / 2)));
    const double c0 = rigidity::PassageClearance(verts, u, ax, th);
    const int g = rng() % ICO_GROUP_SIZE;
    const M r2 = Mul(Mul(HalfTurn(u), r), Group(g));
    vec3 ax2;
    double th2;
    AxisAngle(r2, &ax2, &th2);
    const double c1 = rigidity::PassageClearance(verts, u, ax2, th2);
    worst = std::max(worst, std::abs(c0 - c1));
  }
  printf("invariant: max |clearance(u, R) - clearance(u, H_u R g)| over 200 samples = %.3e\n", worst);
  CHECK(worst < 1e-9);

  // boxes: sub-triangles of the view triangle T and small Cayley boxes.
  using Q = exact5d::Q;
  const exact5d::TriangleQ T = {{{Q(0), Q(0), Q(1)},
                                 {Q(500, 1343), Q(160, 1343), Q(683, 1343)},
                                 {Q(250, 1281), Q(345, 1281), Q(686, 1281)}}};
  int pruned = 0, tried = 0;
  for (int n = 0; n < num_boxes; n++) {
    exact5d::TriangleQ t = T;
    const int depth = 2 + rng() % 5;
    for (int d = 0; d < depth; d++) t = geom5d::SplitTriangle(t, rng() % 4);
    // A random rotation, as Cayley coordinates in chart 0 (|w| < 1).
    vec3 w;
    do { w = {2 * U(rng) - 1, 2 * U(rng) - 1, 2 * U(rng) - 1}; } while (yocto::length(w) > 0.9);
    const double h = std::ldexp(1.0, -(3 + (int)(rng() % 5)));
    geom5d::BoxQ b;
    for (int a = 0; a < 3; a++) {
      b.lo[a] = Q((int64_t)std::floor((w[a] - h) * 1024), 1024);
      b.hi[a] = Q((int64_t)std::ceil((w[a] + h) * 1024), 1024);
    }
    const exact5d::Interval5 iv = geom5d::ToInterval(b);
    for (int g = 0; g < ICO_GROUP_SIZE; g++) {
      tried++;
      if (!exact5d::HalfTurnPruneValid(iv, t, 0, g)) continue;
      pruned++;
      const geom5d::TriangleD td = geom5d::ToDouble(t);
      for (int s = 0; s < samples; s++) {
        double l0 = U(rng), l1 = U(rng);
        if (l0 + l1 > 1) { l0 = 1 - l0; l1 = 1 - l1; }
        const vec3 p = td.corners[0] * (1 - l0 - l1) + td.corners[1] * l0 + td.corners[2] * l1;
        vec3 ws;
        for (int a = 0; a < 3; a++) ws[a] = b.lo[a].ToDouble() + U(rng) * (b.hi[a].ToDouble() - b.lo[a].ToDouble());
        const M r = FromYocto(geom5d::RelativeRotation(0, ws));
        const double adv = Trace(Mul(Mul(HalfTurn(p), r), Group(g))) - Trace(r);
        CHECK(adv > 0) << "pruned box has a point with advantage " << adv << " (g " << g << ")";
      }
    }
  }
  printf("boxes: %d of %d (box, g) pairs pruned; every sampled point has trace(H_u R g) > trace(R)\n",
         pruned, tried);
  printf("OK\n");
}
