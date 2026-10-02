// Search for a near-identity Rupert passage at a fixed outer view u.
// Outer shadow: projection of the polyhedron along u. Inner: R(omega, theta)
// applied to the polyhedron, then projected and translated. For fixed R the
// best translation maximizes min_e (h_e - max_i n_e.q_i - n_e.t), a 3-var LP
// solved by vertex enumeration. We scan theta and hill-climb over omega
// (and optionally over u within the given triangle).
//
// Usage: canyon_passage.exe code tri t s [omega_x omega_y omega_z]

#define TUBECODE_NO_MAIN
#include "../tubecode231.cc"

namespace {

struct Frame { vec3 u, f, g; };

Frame MakeFrame(vec3 u) {
  u = yocto::normalize(u);
  vec3 axis = std::abs(u.x) < std::abs(u.y) ? (std::abs(u.x) < std::abs(u.z) ? vec3{1, 0, 0} : vec3{0, 0, 1})
                                             : (std::abs(u.y) < std::abs(u.z) ? vec3{0, 1, 0} : vec3{0, 0, 1});
  vec3 f = yocto::normalize(yocto::cross(u, axis));
  vec3 g = yocto::cross(u, f);
  return {u, f, g};
}

vec3 Rotate(const vec3 &v, const vec3 &axis, double theta) {
  // Rodrigues
  double c = cos(theta), s = sin(theta);
  return v * c + yocto::cross(axis, v) * s + axis * (yocto::dot(axis, v) * (1 - c));
}

// Returns the best clearance (min over inner vertices and outer edges of
// signed inward distance), optimizing the translation exactly.
double Clearance(const Frame &fr, const vec3 &axis, double theta, vec2 *best_t = nullptr) {
  std::vector<vec2> outer(20), inner(20);
  for (int k = 0; k < 20; k++) {
    vec3 v = Vertex(k);
    outer[k] = vec2{yocto::dot(v, fr.f), yocto::dot(v, fr.g)};
    vec3 w = Rotate(v, axis, theta);
    inner[k] = vec2{yocto::dot(w, fr.f), yocto::dot(w, fr.g)};
  }
  std::vector<int> hull = ConvexHull2D(outer);
  int H = hull.size();
  // Orientation: make normals outward.
  double area = 0;
  for (int i = 0; i < H; i++) {
    vec2 a = outer[hull[i]], b = outer[hull[(i + 1) % H]];
    area += a.x * b.y - a.y * b.x;
  }
  std::vector<vec2> n(H);
  std::vector<double> gcoef(H);
  for (int i = 0; i < H; i++) {
    vec2 a = outer[hull[i]], b = outer[hull[(i + 1) % H]];
    vec2 d = b - a;
    vec2 nn = area > 0 ? vec2{d.y, -d.x} : vec2{-d.y, d.x};
    nn = nn / yocto::length(nn);
    n[i] = nn;
    double h = yocto::dot(nn, a);
    double mx = -1e30;
    for (int k = 0; k < 20; k++) mx = std::max(mx, yocto::dot(nn, inner[k]));
    gcoef[i] = h - mx;  // clearance(t) = min_i gcoef_i - n_i.t
  }
  // Maximize s s.t. s + n_i.t <= g_i. Enumerate triples.
  double best = -1e30;
  vec2 bt{0, 0};
  for (int a = 0; a < H; a++)
    for (int b = a + 1; b < H; b++)
      for (int c = b + 1; c < H; c++) {
        // Solve [n_a 1; n_b 1; n_c 1] [t; s] = g
        double M[3][3] = {{n[a].x, n[a].y, 1}, {n[b].x, n[b].y, 1}, {n[c].x, n[c].y, 1}};
        double rhs[3] = {gcoef[a], gcoef[b], gcoef[c]};
        double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
                     M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
                     M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);
        if (std::abs(det) < 1e-14) continue;
        double x[3];
        for (int col = 0; col < 3; col++) {
          double A[3][3];
          for (int r = 0; r < 3; r++)
            for (int q = 0; q < 3; q++) A[r][q] = (q == col) ? rhs[r] : M[r][q];
          x[col] = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) -
                    A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) +
                    A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) / det;
        }
        vec2 t{x[0], x[1]};
        double s = 1e30;
        for (int i = 0; i < H; i++) s = std::min(s, gcoef[i] - yocto::dot(n[i], t));
        if (s > best) { best = s; bt = t; }
      }
  if (best_t) *best_t = bt;
  return best;
}

}  // namespace

int main(int argc, char **argv) {
  CHECK(argc >= 5) << "usage: code tri t s [omega]";
  int code = atoi(argv[1]);
  int tri_idx = atoi(argv[2]);
  double t = atof(argv[3]), s = atof(argv[4]);
  vec3 omega{0.40166, -0.48337, -0.77784};
  if (argc >= 8) omega = vec3{atof(argv[5]), atof(argv[6]), atof(argv[7])};
  omega = yocto::normalize(omega);

  std::string bdd = Util::ReadFile("codebdd231.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  const auto &tj = doc["codes"][code]["triangles"][tri_idx];
  vec3 c[3];
  for (int k = 0; k < 3; k++)
    c[k] = ToDouble(BigVecQ3(tj[k]["x"].GetString(), tj[k]["y"].GetString(), tj[k]["z"].GetString()));
  vec3 e = c[1] + (c[2] - c[1]) * t;
  vec3 u = e + (c[0] - e) * s;
  Frame fr = MakeFrame(u);
  printf("u = (%.12f %.12f %.12f)\n", fr.u.x, fr.u.y, fr.u.z);

  // Identity clearance should be 0.
  printf("identity clearance = %.3e\n", Clearance(fr, omega, 0.0));

  for (double theta : {1e-9, 1e-8, 1e-7, 3e-7, 1e-6, 3e-6, 1e-5, 3e-5, 1e-4}) {
    for (double sign : {1.0, -1.0}) {
      vec3 ax = omega * sign;
      double best = Clearance(fr, ax, theta);
      // Hill-climb the axis direction.
      for (double step = 0.1; step > 1e-6; step *= 0.5) {
        for (int it = 0; it < 60; it++) {
          bool imp = false;
          for (int k = 0; k < 6; k++) {
            vec3 a2 = ax;
            a2[k / 2] += (k % 2 ? -step : step);
            a2 = yocto::normalize(a2);
            double v = Clearance(fr, a2, theta);
            if (v > best) { best = v; ax = a2; imp = true; }
          }
          if (!imp) break;
        }
      }
      printf("theta %.1e sign %+.0f: best clearance %.4e (clearance/theta %.3e) axis (%.5f %.5f %.5f)\n",
             theta, sign, best, best / theta, ax.x, ax.y, ax.z);
      fflush(stdout);
    }
  }
  return 0;
}
