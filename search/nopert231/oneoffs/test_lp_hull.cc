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
};
double dot(vec2 a, vec2 b) { return a.x*b.x + a.y*b.y; }

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
  vec3 c2 = {53756867.0/85983232.0, 373023.0/2686976.0, 494869.0/2097152.0};
  vec3 u = normalize(c2);

  vec3 axis = {0, 1, 0};
  vec3 first = normalize(cross(u, axis));
  vec3 second = cross(u, first);

  std::vector<int> hull = {19, 3, 2, 1, 4, 8, 9, 10, 15};
  int H = hull.size();

  // Project vertices
  std::vector<vec2> pts(20);
  for (int k = 0; k < 20; k++) {
    pts[k] = {dot(V[k], first), dot(V[k], second)};
  }

  vec3 omega = normalize(vec3{-0.400992, 0.483041, 0.778381});
  vec3 target = omega * -1.0;

  // Let's generate a dense set of contacts around the hull:
  // For each hull vertex v, we can interpolate between the incident edges:
  // prev_edge = pts[v] - pts[prev], next_edge = pts[next] - pts[v]
  // In 3D:
  // edge1 = V[v] - V[prev], edge2 = V[next] - V[v]
  // contact edge = (1 - alpha) * edge1 + alpha * edge2
  struct Cand {
    vec2 n;
    vec3 tau;
    int v;
    double alpha;
  };
  std::vector<Cand> cands;

  for (int pos = 0; pos < H; pos++) {
    int v = hull[pos];
    int prev = hull[(pos - 1 + H) % H];
    int next = hull[(pos + 1) % H];

    vec3 e1 = V[v] - V[prev];
    vec3 e2 = V[next] - V[v];

    for (double alpha = 0.0; alpha <= 1.0; alpha += 0.01) {
      vec3 e = e1 * (1.0 - alpha) + e2 * alpha;
      vec3 lift = cross(u, e);
      vec3 tau = cross(V[v], lift);
      vec2 n = {dot(lift, first), dot(lift, second)};
      // verify support upper <= 1e-12 at u
      bool valid = true;
      for (int k = 0; k < 20; k++) {
        vec3 delta = V[k] - V[v];
        if (dot(u, cross(e, delta)) > 1e-11) {
          valid = false;
          break;
        }
      }
      if (valid) {
        cands.push_back({n, tau, v, alpha});
      }
    }
  }

  std::cout << "Valid dense contacts: " << cands.size() << "\n";

  // Now, what is the maximum of dot(sum w_i * tau_i, target)
  // subject to sum w_i * n_i = 0, sum w_i * ||tau_i|| = 1, w_i >= 0?
  // By LP duality, this equals:
  // min_{t in R^2} max_i (dot(tau_i, target) + dot(n_i, t)) / ||tau_i||?
  // No!
  // Let max_{w >= 0, sum w_i n_i = 0} dot(sum w_i tau_i, target) / sum w_i.
  // Dual LP:
  // min_{t in R^2} max_i (dot(tau_i, target) - dot(n_i, t)).
  // If the dual optimal value is < 0, then for that optimal t*,
  // dot(tau_i, target) - dot(n_i, t*) <= value < 0 for ALL i!
  // Which means dot(tau_i, target) < dot(n_i, t*) for all i.
  
  // Let's do gradient descent to find min_{t in R^2} max_i (dot(tau_i, target) - dot(n_i, t)):
  vec2 t = {0, 0};
  double step = 0.1;
  for (int iter = 0; iter < 10000; iter++) {
    double max_val = -1e9;
    vec2 g = {0, 0};
    for (const auto &c : cands) {
      double val = dot(c.tau, target) - dot(c.n, t);
      if (val > max_val) {
        max_val = val;
        g = { -c.n.x, -c.n.y }; // subgradient w.r.t t
      }
    }
    t.x -= step * g.x / (1.0 + iter * 0.01);
    t.y -= step * g.y / (1.0 + iter * 0.01);
  }

  double primal_dual_opt = -1e9;
  int worst_cand = -1;
  for (size_t i = 0; i < cands.size(); i++) {
    double val = dot(cands[i].tau, target) - dot(cands[i].n, t);
    if (val > primal_dual_opt) {
      primal_dual_opt = val;
      worst_cand = i;
    }
  }

  std::cout << "Optimal dual translation t*: (" << t.x << ", " << t.y << ")\n";
  std::cout << "Max opposing torque over all balanced mixtures (primal/dual value): "
            << std::scientific << primal_dual_opt << "\n";

  return 0;
}
