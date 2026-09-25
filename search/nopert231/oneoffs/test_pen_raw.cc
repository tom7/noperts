#include <iostream>
#include <vector>
#include <iomanip>
#include <cmath>

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

// Nopert #229 rational vertices in double
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

int main() {
  // Corner 2 rational view: (53756867/85983232, 373023/2686976, 494869/2097152)
  vec3 c2 = {53756867.0/85983232.0, 373023.0/2686976.0, 494869.0/2097152.0};
  vec3 u = normalize(c2);

  vec3 axis = {0, 1, 0};
  vec3 first = normalize(cross(u, axis));
  vec3 second = cross(u, first);

  std::vector<int> hull = {19, 3, 2, 1, 4, 8, 9, 10, 15};
  int H = hull.size();

  std::vector<vec2> outer_pts(20);
  for (int k = 0; k < 20; k++) {
    outer_pts[k] = {dot(V[k], first), dot(V[k], second)};
  }

  std::vector<vec2> normals(H);
  std::vector<double> offsets(H);
  for (int i = 0; i < H; i++) {
    int v0 = hull[i];
    int v1 = hull[(i + 1) % H];
    vec2 edge = outer_pts[v1] - outer_pts[v0];
    vec2 n = {edge.y, -edge.x};
    n = n / std::sqrt(dot(n, n));
    normals[i] = n;
    offsets[i] = dot(n, outer_pts[v0]);
  }

  vec3 omega = normalize(vec3{-0.400992, 0.483041, 0.778381});
  vec3 w = omega * -1.0;

  double theta = 1e-5;
  vec2 t = {-1.2e-6, 4.4e-6};

  std::cout << "Penetrations for theta = " << theta << ", t = (" << t.x << ", " << t.y << "):\n";
  for (int k = 0; k < 20; k++) {
    vec3 v = V[k];
    vec3 v_rot = v + cross(w, v) * std::sin(theta) + cross(w, cross(w, v)) * (1.0 - std::cos(theta));
    vec2 p = vec2{dot(v_rot, first), dot(v_rot, second)} + t;
    for (int i = 0; i < H; i++) {
      double pen = dot(normals[i], p) - offsets[i];
      if (pen > 1e-9) {
        std::cout << "  Vertex v" << k << " penetrates hull edge ("
                  << hull[i] << " -> " << hull[(i+1)%H] << ") by "
                  << std::scientific << pen << "\n";
      }
    }
  }

  return 0;
}
