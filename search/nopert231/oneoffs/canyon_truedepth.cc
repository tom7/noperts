// "True" first-order rigidity depth at a single view u, with continuously
// variable contact directions (column generation).
//
// At a view u, a contact is (hull vertex v, direction e(m) = m (v_prev - v) +
// (1 - m) (v - v_next)), m in [0,1]; it is usable if every other vertex has
// support <= -screen. A triple of contacts with nonnegative weights gives an
// axis vector a (as in GenerateCandidatesForView). The depth of the origin in
// conv{a} is the best possible margin of any 4-axis cage at u (before the
// variation delta). We alternate: find the worst direction d for the current
// set, then add, for every multiset of 3 hull vertices, the mixes maximizing
// a.d (grid search + local refinement), until the depth converges.
//
// Usage: canyon_truedepth.exe code tri t s [screen]
//   u = c1 + t (c2 - c1) + s (c0 - (c1 + t (c2 - c1)))

#define TUBECODE_NO_MAIN
#include "../tubecode231.cc"

namespace {

struct Ctx {
  vec3 u;
  std::vector<int> cycle;  // hull vertex cycle
  double screen;
};

vec3 EdgeDir(const Ctx &ctx, int pos, double m) {
  int H = ctx.cycle.size();
  int v = ctx.cycle[pos], p = ctx.cycle[(pos - 1 + H) % H], n = ctx.cycle[(pos + 1) % H];
  return (Vertex(p) - Vertex(v)) * m + (Vertex(v) - Vertex(n)) * (1.0 - m);
}

bool Usable(const Ctx &ctx, int pos, double m) {
  int v = ctx.cycle[pos];
  vec3 e = EdgeDir(ctx, pos, m);
  int H = ctx.cycle.size();
  int p = ctx.cycle[(pos - 1 + H) % H], n = ctx.cycle[(pos + 1) % H];
  for (int k = 0; k < 20; k++) {
    if (k == v) continue;
    // Exact ties for pure edges.
    if (m == 1.0 && k == p) continue;
    if (m == 0.0 && k == n) continue;
    double s = yocto::dot(ctx.u, yocto::cross(e, Vertex(k) - Vertex(v)));
    if (s + ctx.screen > 0) return false;
  }
  return true;
}

// Axis vector for a triple; returns false if weights are not all >= 0
// (after a global sign flip) or all zero.
bool Axis(const Ctx &ctx, const int pos[3], const double m[3], vec3 *out) {
  vec3 e[3], v[3];
  for (int i = 0; i < 3; i++) {
    e[i] = EdgeDir(ctx, pos[i], m[i]);
    v[i] = Vertex(ctx.cycle[pos[i]]);
  }
  double w[3] = {yocto::dot(ctx.u, yocto::cross(e[1], e[2])),
                 yocto::dot(ctx.u, yocto::cross(e[2], e[0])),
                 yocto::dot(ctx.u, yocto::cross(e[0], e[1]))};
  if (w[0] <= 0 && w[1] <= 0 && w[2] <= 0) for (double &x : w) x = -x;
  if (w[0] < 0 || w[1] < 0 || w[2] < 0) return false;
  double B = 2 * (w[0] + w[1] + w[2]);
  if (B <= 1e-15) return false;
  vec3 var{0, 0, 0};
  for (int i = 0; i < 3; i++) var += yocto::cross(v[i], yocto::cross(ctx.u, e[i])) * w[i];
  *out = var / B;
  return true;
}

double DepthOf(const std::vector<vec3> &pts, vec3 *worst) {
  auto Support = [&](const vec3 &d) {
    double best = -1e30;
    for (const auto &a : pts) best = std::max(best, yocto::dot(a, d));
    return best;
  };
  double depth = 1e30;
  const int N = 20000;
  for (int i = 0; i < N; i++) {
    double z = 1 - 2 * (i + 0.5) / N;
    double r = sqrt(std::max(0.0, 1 - z * z));
    double phi = i * 2.399963229728653;
    vec3 d{r * cos(phi), r * sin(phi), z};
    double sd = Support(d);
    if (sd < depth) { depth = sd; *worst = d; }
  }
  for (double step = 0.05; step > 1e-8; step *= 0.5) {
    for (int it = 0; it < 100; it++) {
      bool improved = false;
      for (int k = 0; k < 6; k++) {
        vec3 d = *worst;
        d[k / 2] += (k % 2 ? -step : step);
        d = d / yocto::length(d);
        double sd = Support(d);
        if (sd < depth) { depth = sd; *worst = d; improved = true; }
      }
      if (!improved) break;
    }
  }
  return depth;
}

}  // namespace

int main(int argc, char **argv) {
  CHECK(argc >= 5) << "usage: code tri t s [screen]";
  int code = atoi(argv[1]);
  int tri_idx = atoi(argv[2]);
  double t = atof(argv[3]), s = atof(argv[4]);
  double screen = argc > 5 ? atof(argv[5]) : 1e-13;

  std::string bdd = Util::ReadFile("codebdd231.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  const auto &tj = doc["codes"][code]["triangles"][tri_idx];
  BigVecQ3 c[3];
  for (int k = 0; k < 3; k++)
    c[k] = BigVecQ3(tj[k]["x"].GetString(), tj[k]["y"].GetString(), tj[k]["z"].GetString());
  BigVecQ3 e = c[1] + (c[2] - c[1]) * BigRat::FromDouble(t);
  BigVecQ3 uq = e + (c[0] - e) * BigRat::FromDouble(s);

  Ctx ctx;
  ctx.u = ToDouble(uq);
  ctx.screen = screen;
  {
    vec3 un = ctx.u / yocto::length(ctx.u);
    vec3 axis = std::abs(un.x) < std::abs(un.y) ? (std::abs(un.x) < std::abs(un.z) ? vec3{1, 0, 0} : vec3{0, 0, 1})
                                                 : (std::abs(un.y) < std::abs(un.z) ? vec3{0, 1, 0} : vec3{0, 0, 1});
    vec3 f = yocto::normalize(yocto::cross(un, axis));
    vec3 g = yocto::cross(un, f);
    std::vector<vec2> proj(20);
    for (int k = 0; k < 20; k++) proj[k] = vec2{yocto::dot(Vertex(k), f), yocto::dot(Vertex(k), g)};
    ctx.cycle = ConvexHull2D(proj);
  }
  const int H = ctx.cycle.size();
  printf("u=(%.9f %.9f %.9f) hull:", ctx.u.x, ctx.u.y, ctx.u.z);
  for (int v : ctx.cycle) printf(" %d", v);
  printf("\n");

  // Usable mix grid per hull position.
  const int G = 200;
  std::vector<std::vector<double>> usable(H);
  for (int p = 0; p < H; p++) {
    for (int g = 0; g <= G; g++) {
      double m = (double)g / G;
      if (Usable(ctx, p, m)) usable[p].push_back(m);
    }
  }
  printf("usable mixes per hull vertex:");
  for (int p = 0; p < H; p++) printf(" v%d:%zu", ctx.cycle[p], usable[p].size());
  printf("\n");

  // Initial set: coarse mixes.
  std::vector<vec3> pts;
  std::vector<std::array<int, 3>> multisets;
  for (int a = 0; a < H; a++)
    for (int b = a; b < H; b++)
      for (int cc = b; cc < H; cc++) multisets.push_back({a, b, cc});
  for (const auto &ms : multisets) {
    int pos[3] = {ms[0], ms[1], ms[2]};
    for (double m0 : usable[ms[0]]) {
      if (fmod(m0 * G, 20) != 0) continue;
      for (double m1 : usable[ms[1]]) {
        if (fmod(m1 * G, 20) != 0) continue;
        for (double m2 : usable[ms[2]]) {
          if (fmod(m2 * G, 20) != 0) continue;
          double m[3] = {m0, m1, m2};
          vec3 a;
          if (Axis(ctx, pos, m, &a)) pts.push_back(a);
        }
      }
    }
  }

  for (int iter = 0; iter < 30; iter++) {
    vec3 d;
    double depth = DepthOf(pts, &d);
    printf("iter %d: %zu axes, depth %.6e, worst (%.5f %.5f %.5f)\n", iter, pts.size(), depth, d.x, d.y, d.z);
    fflush(stdout);
    // Column generation: best a.d per multiset over the full usable grid.
    std::vector<vec3> added(multisets.size());
    std::vector<double> addval(multisets.size(), -1e30);
    std::atomic<size_t> next{0};
    std::vector<std::thread> th;
    for (int T = 0; T < 16; T++) {
      th.emplace_back([&]() {
        for (;;) {
          size_t i = next.fetch_add(1);
          if (i >= multisets.size()) return;
          int pos[3] = {multisets[i][0], multisets[i][1], multisets[i][2]};
          for (double m0 : usable[pos[0]])
            for (double m1 : usable[pos[1]])
              for (double m2 : usable[pos[2]]) {
                double m[3] = {m0, m1, m2};
                vec3 a;
                if (Axis(ctx, pos, m, &a)) {
                  double val = yocto::dot(a, d);
                  if (val > addval[i]) { addval[i] = val; added[i] = a; }
                }
              }
        }
      });
    }
    for (auto &x : th) x.join();
    double best = -1e30;
    int n_add = 0;
    for (size_t i = 0; i < multisets.size(); i++) {
      if (addval[i] > depth) { pts.push_back(added[i]); n_add++; }
      best = std::max(best, addval[i]);
    }
    printf("   best new a.d = %.6e (%d added)\n", best, n_add);
    if (best <= depth + 1e-12) break;
  }
  return 0;
}
