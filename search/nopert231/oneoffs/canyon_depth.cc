// Explore Tag 1 feasibility at single view directions near an edge of a
// code triangle. For u = c1 + t (c2 - c1) + s (c0 - (c1 + t (c2 - c1)))
// (so s = 0 is on the c1-c2 edge, s > 0 moves into the triangle), generate
// all candidate axis triples at the point triangle {u,u,u} and report the
// depth of the origin in the convex hull of their normalized axis vectors
// (an upper bound on the margin of any 4-axis cage built from them), and
// the worst direction.
//
// Usage: canyon_depth.exe code tri t s [screen_support_error] [cone_samples]

#define TUBECODE_NO_MAIN
#include "../tubecode229.cc"

int main(int argc, char **argv) {
  CHECK(argc >= 5) << "usage: code tri t s [screen] [cone_samples]";
  int code = atoi(argv[1]);
  int tri_idx = atoi(argv[2]);
  BigRat t = BigRat::FromDouble(atof(argv[3]));
  BigRat s = BigRat::FromDouble(atof(argv[4]));
  double screen = argc > 5 ? atof(argv[5]) : 1e-13;
  int cone_samples = argc > 6 ? atoi(argv[6]) : 8;

  std::string bdd = Util::ReadFile("codebdd229.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  const auto &tj = doc["codes"][code]["triangles"][tri_idx];
  BigVecQ3 c[3];
  for (int k = 0; k < 3; k++)
    c[k] = BigVecQ3(tj[k]["x"].GetString(), tj[k]["y"].GetString(), tj[k]["z"].GetString());
  BigVecQ3 e = c[1] + (c[2] - c[1]) * t;
  BigVecQ3 u = e + (c[0] - e) * s;
  TriangleQ pt;
  pt.corners[0] = pt.corners[1] = pt.corners[2] = u;
  vec3 ud = ToDouble(u);

  std::vector<CandidateTriple> cands;
  GenerateCandidatesForView(ud, pt, cone_samples, true, screen, &cands);

  // Hull vertices in the view, for context.
  vec3 un = ud / yocto::length(ud);
  std::vector<vec3> pts;
  for (const auto &cd : cands) pts.push_back(cd.normalized_a);

  // Depth: min over directions d of max_a a.d, sampled on a Fibonacci sphere,
  // then refined locally around the worst direction.
  auto Support = [&](const vec3 &d) {
    double best = -1e30;
    for (const auto &a : pts) best = std::max(best, yocto::dot(a, d));
    return best;
  };
  double depth = 1e30;
  vec3 worst{0, 0, 0};
  const int N = 20000;
  for (int i = 0; i < N; i++) {
    double z = 1 - 2 * (i + 0.5) / N;
    double r = sqrt(std::max(0.0, 1 - z * z));
    double phi = i * 2.399963229728653;
    vec3 d{r * cos(phi), r * sin(phi), z};
    double sd = Support(d);
    if (sd < depth) { depth = sd; worst = d; }
  }
  for (double step = 0.05; step > 1e-7; step *= 0.5) {
    for (int it = 0; it < 50; it++) {
      bool improved = false;
      for (int k = 0; k < 6; k++) {
        vec3 d = worst;
        d[k / 2] += (k % 2 ? -step : step);
        d = d / yocto::length(d);
        double sd = Support(d);
        if (sd < depth) { depth = sd; worst = d; improved = true; }
      }
      if (!improved) break;
    }
  }

  printf("t=%s s=%s u=(%.9f %.9f %.9f) screen=%.1e candidates=%zu depth=%.4e worst_dir=(%.5f %.5f %.5f)\n",
         argv[3], argv[4], un.x, un.y, un.z, screen, cands.size(), depth, worst.x, worst.y, worst.z);

  // Which contacts (support vertices) appear in the candidates that best
  // cover the worst direction?
  std::vector<std::pair<double, int>> by;
  for (int i = 0; i < (int)pts.size(); i++) by.push_back({yocto::dot(pts[i], worst), i});
  std::sort(by.rbegin(), by.rend());
  for (int j = 0; j < std::min<int>(3, by.size()); j++) {
    const auto &cd = cands[by[j].second];
    printf("   best along worst: %.3e  contacts:", by[j].first);
    for (int k = 0; k < 3; k++)
      printf(" [v%d (%d>%d|%d>%d) mix %d]", cd.contacts[k].vertex, cd.contacts[k].edge_start,
             cd.contacts[k].edge_finish, cd.contacts[k].edge_start2, cd.contacts[k].edge_finish2,
             cd.contacts[k].mix);
    printf("\n");
  }
  return 0;
}
