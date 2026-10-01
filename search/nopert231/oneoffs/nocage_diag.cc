// Diagnose "no cage" for one sub-triangle of a code triangle: silhouette at
// the center view, candidate counts, and AuditAxis results on a sample.
// Usage: nocage_diag.exe code tri path [samples]
#include <map>
#define TUBECODE_NO_MAIN
#include "../tubecode229.cc"

int main(int argc, char **argv) {
  CHECK(argc >= 4);
  const int code = atoi(argv[1]), tri_idx = atoi(argv[2]);
  const std::string path = argv[3];
  const int samples = argc > 4 ? atoi(argv[4]) : 300;
  std::string bdd = Util::ReadFile("codebdd229.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  const auto &t = doc["codes"][code]["triangles"][tri_idx];
  TriangleQ tri;
  for (int k = 0; k < 3; k++)
    tri.corners[k] = BigVecQ3(t[k]["x"].GetString(), t[k]["y"].GetString(), t[k]["z"].GetString());
  for (char ch : path) { TriangleQ c[4]; tri.Subdivide(c); tri = c[ch - '0']; }
  vec3 c0 = ToDouble(tri.corners[0]), c1 = ToDouble(tri.corners[1]), c2 = ToDouble(tri.corners[2]);
  vec3 center = yocto::normalize((c0 + c1 + c2) / 3.0);
  printf("center (%.9f %.9f %.9f), diameter %.3e\n", center.x, center.y, center.z,
         std::max({yocto::distance(c0, c1), yocto::distance(c1, c2), yocto::distance(c2, c0)}));

  // Silhouette at the center (same frame as GenerateCandidatesForView).
  int ai = 0; double mn = 1e30;
  for (int i = 0; i < 3; i++) if (std::abs(center[i]) < mn) { mn = std::abs(center[i]); ai = i; }
  vec3 axis = ai == 0 ? vec3{1, 0, 0} : ai == 1 ? vec3{0, 1, 0} : vec3{0, 0, 1};
  vec3 f = yocto::normalize(yocto::cross(center, axis)), g = yocto::cross(center, f);
  std::vector<vec2> pr(20);
  for (int k = 0; k < 20; k++) pr[k] = vec2{yocto::dot(Vertex(k), f), yocto::dot(Vertex(k), g)};
  std::vector<int> cyc = ConvexHull2D(pr);
  printf("hull:");
  for (size_t i = 0; i < cyc.size(); i++) {
    vec2 a = pr[cyc[(i + cyc.size() - 1) % cyc.size()]], b = pr[cyc[i]], c = pr[cyc[(i + 1) % cyc.size()]];
    printf(" %d[ext %.2e]", cyc[i], std::atan2(Cross2(b - a, c - b), yocto::dot(b - a, c - b)));
  }
  printf("\n");

  std::vector<CandidateTriple> cands;
  GenerateCandidatesForView(center, tri, 8, true, 1e-13, &cands);
  printf("candidates: %zu\n", cands.size());
  std::map<std::string, int> reasons;
  std::map<int, int> pass_by_vertexset;
  int pass = 0;
  unsigned int seed = 7;
  for (int s = 0; s < samples && !cands.empty(); s++) {
    const auto &cd = cands[rand_r(&seed) % cands.size()];
    ContactInfo cts[3] = {cd.contacts[0], cd.contacts[1], cd.contacts[2]};
    AxisCertificate ax; BigVecQ3 cent; BigRat del; std::string why;
    if (AuditAxis(tri, cts, &ax, &cent, &del, &why)) pass++;
    else {
      std::string key = why.substr(0, why.find('('));
      if (why.rfind("s_upper", 0) == 0) {
        // Which (contact vertex, offending vertex)?
        int m = -1, k = -1;
        sscanf(why.c_str(), "s_upper > 0 (m=%d, k=%d", &m, &k);
        if (m >= 0) key += StringPrintf("[contact v%d vs v%d]", cts[m].vertex, k);
      }
      reasons[key]++;
    }
  }
  printf("audited %d sample candidates: %d pass\n", samples, pass);
  // Depth of the origin in conv(normalized_a) (sampled directions).
  {
    double depth = 1e30; vec3 worst{};
    const int N = 4000;
    for (int i = 0; i < N; i++) {
      double z = 1 - 2 * (i + 0.5) / N, r = std::sqrt(1 - z * z), ph = i * 2.399963229728653;
      vec3 d{r * std::cos(ph), r * std::sin(ph), z};
      double mx = -1e30;
      for (const auto &cd : cands) mx = std::max(mx, yocto::dot(cd.normalized_a, d));
      if (mx < depth) { depth = mx; worst = d; }
    }
    printf("origin depth in conv(normalized_a) ~ %.3e (worst dir %.3f %.3f %.3f)\n", depth, worst.x, worst.y, worst.z);
    double mxn = 0;
    for (const auto &cd : cands) mxn = std::max(mxn, yocto::length(cd.normalized_a));
    printf("max |normalized_a| = %.3e\n", mxn);
  }
  // Best random tetrahedron margin, ignoring the audit.
  {
    double best = -1e30;
    unsigned int sd = 11;
    for (int trial = 0; trial < 25000; trial++) {
      int i0 = rand_r(&sd) % cands.size(), i1 = rand_r(&sd) % cands.size(), i2 = rand_r(&sd) % cands.size(), i3 = rand_r(&sd) % cands.size();
      vec3 tp[4] = {cands[i0].normalized_a, cands[i1].normalized_a, cands[i2].normalized_a, cands[i3].normalized_a};
      double m, bary[4];
      if (TetrahedronOriginMargin(tp, &m, bary)) best = std::max(best, m);
    }
    printf("best random tetra margin (no audit) = %.3e\n", best);
  }
  {
    std::vector<vec3> pts;
    for (const auto &cd : cands) pts.push_back(cd.normalized_a);
    std::array<int, 4> tet; double m = 0;
    bool ok = SupportSearchTetra(pts, [](int) { return true; }, &tet, &m);
    double m2 = 0, bary[4];
    vec3 tp[4] = {pts[tet[0]], pts[tet[1]], pts[tet[2]], pts[tet[3]]};
    bool ok2 = TetrahedronOriginMargin(tp, &m2, bary);
    printf("SupportSearchTetra: ok %d margin %.3e; TetrahedronOriginMargin ok %d margin %.3e\n", ok, m, ok2, m2);
  }
  {
    std::vector<vec3> pts;
    for (const auto &cd : cands) pts.push_back(cd.normalized_a);
    const int N = pts.size();
    std::vector<int> sup;
    std::vector<int8_t> seen(N, 0);
    for (int i = 0; i < 256; i++) {
      const double z = 1 - 2 * (i + 0.5) / 256, r = std::sqrt(std::max(0.0, 1 - z * z));
      const double ph = i * 2.399963229728653;
      const vec3 d{r * std::cos(ph), r * std::sin(ph), z};
      int bi = -1; double bv = -1e300;
      for (int j = 0; j < N; j++) { double v = yocto::dot(pts[j], d); if (v > bv) { bv = v; bi = j; } }
      if (!seen[bi]) { seen[bi] = 1; sup.push_back(bi); }
    }
    double best = -1e300; int npos = 0;
    const int S = sup.size();
    for (int a = 0; a < S; a++) for (int b = a + 1; b < S; b++) for (int c = b + 1; c < S; c++) for (int d = c + 1; d < S; d++) {
      const vec3 tp[4] = {pts[sup[a]], pts[sup[b]], pts[sup[c]], pts[sup[d]]};
      double m = TetraMargin(tp);
      if (m > 0) npos++;
      best = std::max(best, m);
    }
    // Depth restricted to the support set.
    double depth = 1e30;
    for (int i = 0; i < 4000; i++) {
      double z = 1 - 2 * (i + 0.5) / 4000, r = std::sqrt(1 - z * z), ph = i * 2.399963229728653;
      vec3 d{r * std::cos(ph), r * std::sin(ph), z};
      double mx = -1e30;
      for (int j : sup) mx = std::max(mx, yocto::dot(pts[j], d));
      depth = std::min(depth, mx);
    }
    printf("support set %d points; depth of conv(support) %.3e; brute force best tetra margin %.3e (%d positive)\n",
           S, depth, best, npos);
  }
  {
    LocalCertificate lc; double m = 0; unsigned int sd2 = 5;
    bool ok = FindBestCageForTriangle(tri, &sd2, &lc, &m);
    printf("FindBestCageForTriangle: %s margin %.3e\n", ok ? "found" : "none", m);
    if (ok) {
      LocalCertificate au; std::string why;
      bool ra = ReauditCertificate(tri, lc, BigRat(0), BigRat(0), &au, &why);
      printf("  reaudit: %s %s\n", ra ? "OK" : "FAIL", why.substr(0, 120).c_str());
    }
  }
  for (auto &[k, v] : reasons) printf("  %5d  %s\n", v, k.c_str());
  return 0;
}
