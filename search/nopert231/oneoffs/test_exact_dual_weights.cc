#include <iostream>
#include <vector>
#include <iomanip>
#include <cmath>
#include <algorithm>

struct vec3 {
  double x, y, z;
  vec3 operator+(vec3 o) const { return {x+o.x, y+o.y, z+o.z}; }
  vec3 operator-(vec3 o) const { return {x-o.x, y-o.y, z-o.z}; }
  vec3 operator*(double s) const { return {x*s, y*s, z*s}; }
  vec3 operator/(double s) const { return {x/s, y/s, z/s}; }
};
double dot(vec3 a, vec3 b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
vec3 cross(vec3 a, vec3 b) {
  return {a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
}
double length(vec3 a) { return std::sqrt(dot(a, a)); }
vec3 normalize(vec3 a) { return a / length(a); }

struct vec2 {
  double x, y;
  vec2 operator+(vec2 o) const { return {x+o.x, y+o.y}; }
  vec2 operator-(vec2 o) const { return {x-o.x, y-o.y}; }
  vec2 operator*(double s) const { return {x*s, y*s}; }
  vec2 operator/(double s) const { return {x/s, y/s}; }
};
double dot(vec2 a, vec2 b) { return a.x*b.x + a.y*b.y; }
double length(vec2 a) { return std::sqrt(dot(a, a)); }
vec2 normalize(vec2 a) { return a / length(a); }

const std::vector<vec3> V = {
  { 0.5535017234623651,  0.1347982004144742,  0.5648167326177671 }, // 0
  { 0.7712395632298640, -0.2140411130638515,  0.4273418579730598 }, // 1
  { 0.5111246182283944, -0.6384592067425408,  0.4136932577663248 }, // 2
  { 0.0531778939762696, -0.8035256247920743,  0.4121287664654929 }, // 3
  { 0.7303036814234798,  0.3705018698114424,  0.4072387140813958 }, // 4
  { 0.4431526362879576,  0.7188730403755452,  0.3957264669866299 }, // 5
  {-0.0435422687640323,  0.8407481541300958,  0.3794356616428283 }, // 6
  {-0.5551263421462106,  0.2414836970985378, -0.7643399516054460 }, // 7
  { 0.2848149847113115,  0.7788484180479717, -0.3803875314086659 }, // 8
  { 0.0163351989053896,  0.8173439487508657, -0.4034443725596489 }, // 9
  {-0.0980208886369065,  0.8066531980838944, -0.4030635293237551 }, // 10
  { 0.5898863261614836,  0.0768997576595561, -0.6868848386345445 }, // 11
  { 0.4907106093539744, -0.3672728377035540, -0.6841328646190439 }, // 12
  {-0.1197996350371424,  0.7963385289947963, -0.4357457497184288 }, // 13
  {-0.4449767228221532,  0.6401037583626248, -0.4735515252656910 }, // 14
  {-0.8068770636254095,  0.2798606496467000, -0.4363574163004882 }, // 15
  { 0.5535017234623651,  0.1347982004144742,  0.5648167326177671 }, // 16
  { 0.2758155255470718, -0.6698188164807490, -0.6811488198755601 }, // 17
  {-0.2079089855598165, -0.6806509657417534, -0.6974797377519965 }, // 18
  {-0.6053896574572242, -0.4283623912168962, -0.6409867566270832 }, // 19
};

vec2 project(vec3 v, vec3 u, vec3 ex, vec3 ey) {
  return {dot(v, ex), dot(v, ey)};
}

int main() {
  vec3 c2 = {53756867.0/85983232.0, 373023.0/2686976.0, 494869.0/2097152.0};
  vec3 u = normalize(c2);
  vec3 axis = {0, 1, 0};
  vec3 ex = normalize(cross(u, axis));
  vec3 ey = cross(u, ex);
  vec3 w = normalize(vec3{0.400992, -0.483041, -0.778381});

  std::vector<int> hull = {19, 3, 2, 1, 4, 8, 9, 10, 15};
  int H = hull.size();

  struct HullEdge {
    int v1, v2;
    vec2 n;
    double vel;
  };
  std::vector<HullEdge> edges;
  for (int i = 0; i < H; i++) {
    vec2 p1 = project(V[hull[i]], u, ex, ey);
    vec2 p2 = project(V[hull[(i+1)%H]], u, ex, ey);
    vec2 edge = p2 - p1;
    vec2 n = normalize(vec2{edge.y, -edge.x});

    vec2 dp1 = project(cross(w, V[hull[i]]), u, ex, ey);
    vec2 dp2 = project(cross(w, V[hull[(i+1)%H]]), u, ex, ey);

    double vel = std::min(dot(n, dp1), dot(n, dp2));
    edges.push_back({hull[i], hull[(i+1)%H], n, vel});
  }

  double best_val = -1e9;
  int best_tri[3] = {-1, -1, -1};
  double best_l[3] = {0, 0, 0};

  for (int i = 0; i < H; i++) {
    for (int j = i + 1; j < H; j++) {
      for (int k = j + 1; k < H; k++) {
        vec2 ni = edges[i].n;
        vec2 nj = edges[j].n;
        vec2 nk = edges[k].n;

        double det = ni.x * (nj.y - nk.y) + nj.x * (nk.y - ni.y) + nk.x * (ni.y - nj.y);
        if (std::abs(det) < 1e-9) continue;

        double l0 = (nj.x * nk.y - nj.y * nk.x) / det;
        double l1 = (nk.x * ni.y - nk.y * ni.x) / det;
        double l2 = (ni.x * nj.y - ni.y * nj.x) / det;

        if (l0 >= -1e-9 && l1 >= -1e-9 && l2 >= -1e-9) {
          double val = l0 * edges[i].vel + l1 * edges[j].vel + l2 * edges[k].vel;
          if (val > best_val) {
            best_val = val;
            best_tri[0] = i; best_tri[1] = j; best_tri[2] = k;
            best_l[0] = l0; best_l[1] = l1; best_l[2] = l2;
          }
        }
      }
    }
  }

  std::cout << std::setprecision(10);
  std::cout << "Optimal Dual Combination:\n";
  std::cout << "Value = " << best_val << "\n";
  for (int m = 0; m < 3; m++) {
    int idx = best_tri[m];
    std::cout << "  Edge " << edges[idx].v1 << "->" << edges[idx].v2
              << ": lambda = " << best_l[m]
              << ", normal = (" << edges[idx].n.x << ", " << edges[idx].n.y << ")"
              << ", min_vel = " << edges[idx].vel << "\n";
  }

  return 0;
}
