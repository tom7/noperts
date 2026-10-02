// Probe how much a multi-axis cage (each octahedron target ±s e_k in its own
// tetrahedron of audited axis centers) would coarsen the code 51 tree.
// For sampled deep leaves of trees_r1/code.<code>.journal, walk up their
// ancestors and report whether a 4-axis cage (FindBestCageForTriangle +
// exact reaudit) and a multi-axis cage (hull ray extents, double precision)
// pass at each depth.
// Usage: multicage_probe.exe code min_leaf_depth samples [K]
#include <map>
#define TUBECODE_NO_MAIN
#include "../tubecode231.cc"

// Max t with t*e in conv(pts) (pts assumed to contain the origin inside),
// via facet enumeration; returns -1 if the origin is not strictly inside.
// Origin depth of conv(pts): min facet offset (unit normals).
static double HullDepth(const std::vector<vec3> &pts) {
  const int n = pts.size();
  double best = 1e300;
  for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++) {
    vec3 nrm = yocto::cross(pts[b] - pts[a], pts[c] - pts[a]);
    double len = yocto::length(nrm);
    if (len < 1e-30) continue;
    nrm = nrm / len;
    double h = yocto::dot(nrm, pts[a]);
    if (h < 0) { nrm = -nrm; h = -h; }
    bool facet = true;
    for (int k = 0; k < n && facet; k++) if (yocto::dot(nrm, pts[k]) > h + 1e-15) facet = false;
    if (facet) best = std::min(best, h);
  }
  return best;
}

static double RayExtent(const std::vector<vec3> &pts, const vec3 &e) {
  const int n = pts.size();
  double best = 1e300;
  bool any = false;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++)
      for (int c = b + 1; c < n; c++) {
        vec3 nrm = yocto::cross(pts[b] - pts[a], pts[c] - pts[a]);
        double len = yocto::length(nrm);
        if (len < 1e-30) continue;
        nrm = nrm / len;
        double h = yocto::dot(nrm, pts[a]);
        if (h < 0) { nrm = -nrm; h = -h; }
        // facet iff all points on the nrm·x <= h side
        bool facet = true;
        for (int k = 0; k < n && facet; k++)
          if (yocto::dot(nrm, pts[k]) > h + 1e-15) facet = false;
        if (!facet) continue;
        if (h <= 1e-18) return -1;  // origin on/outside a facet
        any = true;
        double ne = yocto::dot(nrm, e);
        if (ne > 0) best = std::min(best, h / ne);
      }
  return any ? best : -1;
}

struct Probe { double depth_audited_na = 0, depth_all_na = 0; bool four = false; double four_cover = 0, four_delta = 0, four_ray = 0, union_ray = 0, union_depth = 0;
               bool multi = false; double multi_cover = 0, multi_delta = 0; int naxes = 0; };

static Probe ProbeTriangle(const TriangleQ &tri, int K) {
  Probe pr;
  std::vector<vec3> four_pts;
  {
    LocalCertificate lc; double m = 0; unsigned int sd = 5;
    if (FindBestCageForTriangle(tri, &sd, &lc, &m)) {
      for (int a = 0; a < 4; a++) {
        ContactInfo cts[3] = {lc.axes[a].contacts[0], lc.axes[a].contacts[1], lc.axes[a].contacts[2]};
        AxisCertificate ax; BigVecQ3 cent; BigRat del;
        if (AuditAxis(tri, cts, &ax, &cent, &del, nullptr)) four_pts.push_back(ToDouble(cent));
      }
      LocalCertificate au; std::string why; BigRat cov, del;
      pr.four = ReauditCertificate(tri, lc, BigRat(0), BigRat(0), &au, &why, &cov, &del);
      pr.four_cover = cov.ToDouble(); pr.four_delta = del.ToDouble();
    }
  }
  vec3 c0 = ToDouble(tri.corners[0]), c1 = ToDouble(tri.corners[1]), c2 = ToDouble(tri.corners[2]);
  vec3 center = yocto::normalize((c0 + c1 + c2) / 3.0);
  std::vector<CandidateTriple> cands;
  GenerateCandidatesForView(center, tri, 8, true, 1e-13, &cands);
  const int N = cands.size();
  std::vector<int8_t> ok(N, -1);
  std::vector<double> dl(N, 0);
  std::vector<vec3> exact_center(N);
  auto Audited = [&](int i) {
    if (ok[i] < 0) {
      ContactInfo cts[3] = {cands[i].contacts[0], cands[i].contacts[1], cands[i].contacts[2]};
      AxisCertificate ax; BigVecQ3 cent; BigRat del;
      ok[i] = AuditAxis(tri, cts, &ax, &cent, &del, nullptr) ? 1 : 0;
      if (ok[i]) { dl[i] = del.ToDouble(); exact_center[i] = ToDouble(cent); }
    }
    return ok[i] == 1;
  };
  std::vector<int> sup; std::vector<int8_t> seen(N, 0);
  for (int i = 0; i < K; i++) {
    const double z = 1 - 2 * (i + 0.5) / K, r = std::sqrt(std::max(0.0, 1 - z * z));
    const double ph = i * 2.399963229728653;
    const vec3 d{r * std::cos(ph), r * std::sin(ph), z};
    for (;;) {
      int bi = -1; double bv = -1e300;
      for (int j = 0; j < N; j++) {
        if (ok[j] == 0) continue;
        double v = yocto::dot(cands[j].normalized_a, d);
        if (v > bv) { bv = v; bi = j; }
      }
      if (bi < 0) break;
      if (!Audited(bi)) continue;
      if (!seen[bi]) { seen[bi] = 1; sup.push_back(bi); }
      break;
    }
  }
  pr.naxes = sup.size();
  {
    // Depth in normalized_a units: audited support set vs support set of all
    // candidates (defective contacts included), from K directions.
    std::vector<vec3> pa, pall; std::vector<int8_t> seen2(N, 0);
    for (int j : sup) pa.push_back(cands[j].normalized_a);
    for (int i = 0; i < K; i++) {
      const double z = 1 - 2 * (i + 0.5) / K, r = std::sqrt(std::max(0.0, 1 - z * z));
      const double ph = i * 2.399963229728653;
      const vec3 d{r * std::cos(ph), r * std::sin(ph), z};
      int bi = -1; double bv = -1e300;
      for (int j = 0; j < N; j++) { double v = yocto::dot(cands[j].normalized_a, d); if (v > bv) { bv = v; bi = j; } }
      if (!seen2[bi]) { seen2[bi] = 1; pall.push_back(cands[bi].normalized_a); }
    }
    if (pa.size() >= 4) pr.depth_audited_na = HullDepth(pa);
    pr.depth_all_na = HullDepth(pall);
  }
  if (sup.size() < 4) return pr;
  std::vector<vec3> pts;
  double delta = 0;
  for (int j : sup) { pts.push_back(exact_center[j]); delta = std::max(delta, dl[j]); }
  double t = 1e300;
  for (int k = 0; k < 3; k++)
    for (int s : {-1, 1}) {
      vec3 e{0, 0, 0}; e[k] = s;
      double x = RayExtent(pts, e);
      if (x < 0) { t = -1; break; }
      t = std::min(t, x);
    }
  auto MinRay = [](const std::vector<vec3> &P) {
    double tt = 1e300;
    for (int k = 0; k < 3; k++) for (int s : {-1, 1}) { vec3 e{0, 0, 0}; e[k] = s; double x = RayExtent(P, e); if (x < 0) return -1.0; tt = std::min(tt, x); }
    return tt;
  };
  if (four_pts.size() == 4) {
    pr.four_ray = MinRay(four_pts);
    std::vector<vec3> u = pts; for (auto &q : four_pts) u.push_back(q);
    pr.union_ray = MinRay(u);
    pr.union_depth = HullDepth(u);
  }
  pr.multi_cover = t > 0 ? t * 0.95 * 4.0 / 7.0 : 0;
  pr.multi_delta = delta;
  pr.multi = t > 0 && pr.multi_cover > delta;
  return pr;
}

int main(int argc, char **argv) {
  CHECK(argc >= 4);
  const int code = atoi(argv[1]), min_depth = atoi(argv[2]), samples = atoi(argv[3]);
  const int K = argc > 4 ? atoi(argv[4]) : 512;
  std::string bdd = Util::ReadFile("codebdd231.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  std::vector<std::pair<int, std::string>> deep;
  for (const std::string &line : Util::ReadFileToLines(StringPrintf("trees_r1/code.%d.journal", code))) {
    int tri; char path[64];
    if (sscanf(line.c_str(), "L %d %63s", &tri, path) == 2 && (int)strlen(path) >= min_depth)
      deep.push_back({tri, path});
  }
  printf("%zu leaves at depth >= %d\n", deep.size(), min_depth);
  unsigned int sd = 1;
  for (int s = 0; s < samples; s++) {
    const auto &[ti, path] = deep[rand_r(&sd) % deep.size()];
    const auto &t = doc["codes"][code]["triangles"][ti];
    TriangleQ root;
    for (int k = 0; k < 3; k++)
      root.corners[k] = BigVecQ3(t[k]["x"].GetString(), t[k]["y"].GetString(), t[k]["z"].GetString());
    printf("tri %d leaf %s\n", ti, path.c_str());
    for (int d = (int)path.size(); d >= 3; d--) {
      TriangleQ tri = root;
      for (int i = 0; i < d; i++) { TriangleQ c[4]; tri.Subdivide(c); tri = c[path[i] - '0']; }
      Probe p = ProbeTriangle(tri, K);
      printf("  depth %2d: 4-axis %s (cover %.2e delta %.2e)  multi %s (cover %.2e delta %.2e, %d axes) [ray4 %.2e union %.2e depth %.2e] na-depth audited %.2e all %.2e\n",
             d, p.four ? "PASS" : "fail", p.four_cover, p.four_delta,
             p.multi ? "PASS" : "fail", p.multi_cover, p.multi_delta, p.naxes, p.four_ray, p.union_ray, p.union_depth, p.depth_audited_na, p.depth_all_na);
      fflush(stdout);
      if (!p.four && !p.multi) break;
    }
  }
  return 0;
}
