// Tests that exact5d agrees exactly with the Lean checker it ports. Boxes
// are generated here, evaluated by the Lean executable exact5d_golden, and
// every intermediate quantity is compared as an exact rational.
//
// exact5d_golden is not in this repository's Lean project (../../proof has
// no such executable); it was built in the searches' Noperthedron branches
// (`lake build exact5d_golden`). Point $EXACT5D_GOLDEN at such a build to run
// the comparison; without it the test prints SKIPPED and passes.
//
// Triangles are sub-triangles of real code triangles (realistic big
// rationals); certificates are random but well-formed, so most boxes are
// not admissible, which still exercises all the quantities.

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <vector>

#include <unistd.h>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "model.h"
#include "tube.h"
#include "tubetree.h"
#include "rapidjson/document.h"
#include "test_data.h"
#include "util.h"

using namespace exact5d;
using vec3 = yocto::vec<double, 3>;

// The Lean side's exact5d_golden executable: $EXACT5D_GOLDEN (no default).
static std::string Golden() {
  const char *e = getenv("EXACT5D_GOLDEN");
  return e != nullptr ? e : "";
}

static std::string R(const Q &q) { return q.ToString(); }

static TriangleQ SubTriangle(TriangleQ t, std::mt19937_64 &rng, int depth) {
  for (int d = 0; d < depth; d++) {
    const VecQ m01 = {(t[0][0] + t[1][0]) / Q(2), (t[0][1] + t[1][1]) / Q(2), (t[0][2] + t[1][2]) / Q(2)};
    const VecQ m12 = {(t[1][0] + t[2][0]) / Q(2), (t[1][1] + t[2][1]) / Q(2), (t[1][2] + t[2][2]) / Q(2)};
    const VecQ m20 = {(t[2][0] + t[0][0]) / Q(2), (t[2][1] + t[0][1]) / Q(2), (t[2][2] + t[0][2]) / Q(2)};
    switch (rng() % 4) {
    case 0: t = {t[0], m01, m20}; break;
    case 1: t = {m01, t[1], m12}; break;
    case 2: t = {m20, m12, t[2]}; break;
    default: t = {m01, m12, m20}; break;
    }
  }
  return t;
}

static AxisCertificate RandomCert(std::mt19937_64 &rng) {
  AxisCertificate c;
  for (int i = 0; i < 3; i++) {
    c.edge_start[i] = rng() % NUM_VERTICES;
    c.edge_finish[i] = rng() % NUM_VERTICES;
    c.edge_start2[i] = rng() % NUM_VERTICES;
    c.edge_finish2[i] = rng() % NUM_VERTICES;
    const int r = rng() % 4;
    c.mix[i] = r == 0 ? 0 : r == 1 ? 1000 : (int)(rng() % 1001);
    c.index[i] = rng() % NUM_VERTICES;
    c.nonzero_witness[i] = rng() % NUM_VERTICES;
  }
  // Sometimes make the exact-support tie cases reachable.
  if (rng() % 3 == 0) c.index[0] = c.edge_finish[0];
  if (rng() % 3 == 0) c.index[1] = c.edge_start2[1];
  c.B = Q((int64_t)(rng() % 1000 + 1), 1000);
  return c;
}

// A certificate from real silhouette contacts at the triangle's centroid
// view (Tube's candidate generator), with the nonzero witness chosen as
// the vertex of most negative exact support bound. These are often
// admissible. Returns false if there are no candidates.
static bool RealisticCert(const TriangleQ &tri, std::mt19937_64 &rng, AxisCertificate *out) {
  tubetree::TriangleQ t;
  for (int i = 0; i < 3; i++) t.corners[i] = BigVecQ3(tri[i][0], tri[i][1], tri[i][2]);
  vec3 view = {0, 0, 0};
  for (int i = 0; i < 3; i++) {
    view += vec3{tri[i][0].ToDouble(), tri[i][1].ToDouble(), tri[i][2].ToDouble()};
  }
  view = yocto::normalize(view);
  auto cands = Tube::GenerateCandidatesForView(view, t, true, 4);
  if (cands.empty()) return false;
  const auto &cand = cands[rng() % cands.size()];
  AxisCertificate c;
  for (int i = 0; i < 3; i++) {
    const auto &ct = cand.contacts[i];
    c.edge_start[i] = ct.edge_start;
    c.edge_finish[i] = ct.edge_finish;
    c.edge_start2[i] = ct.edge_start2;
    c.edge_finish2[i] = ct.edge_finish2;
    c.mix[i] = ct.mix;
    c.index[i] = ct.vertex;
  }
  c.B = Q(1);
  GlobalBox probe;
  probe.triangle = tri;
  probe.certificate = c;
  for (int i = 0; i < 3; i++) {
    int best = 0;
    Q best_v;
    bool first = true;
    for (int k = 0; k < NUM_VERTICES; k++) {
      const Q v = SupportUpper(probe, i, k);
      if (first || v < best_v) { best = k; best_v = v; first = false; }
    }
    c.nonzero_witness[i] = best;
  }
  *out = c;
  return true;
}

static std::string CertString(const AxisCertificate &c) {
  std::string s;
  for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                          &c.mix, &c.index, &c.nonzero_witness}) {
    for (int i = 0; i < 3; i++) s += std::format(" {}", (*arr)[i]);
  }
  s += " " + R(c.B);
  return s;
}

struct Common {
  int chart = 0;
  TriangleQ tri;
  Interval5 iv;
  std::array<Q, 3> center, radius;
};

static Common RandomCommon(const std::vector<TriangleQ> &code_tris, std::mt19937_64 &rng) {
  Common c;
  c.chart = rng() % 4;
  c.tri = SubTriangle(code_tris[rng() % code_tris.size()], rng, rng() % 12);
  for (int a = 0; a < 3; a++) {
    // Dyadic centers in [-1, 1], radii 2^-k.
    c.center[a] = Q((int64_t)(rng() % 2049) - 1024, 1024);
    c.radius[a] = Q(1, (int64_t)1 << (2 + rng() % 20));
    if (rng() % 2) c.radius[a] = -c.radius[a];  // |radius| is used
    c.iv.min[a + 2] = c.center[a] - BigRat::Abs(c.radius[a]);
    c.iv.max[a + 2] = c.center[a] + BigRat::Abs(c.radius[a]);
  }
  c.iv.min[0] = Q(0);
  c.iv.max[0] = Q(8, 5);
  c.iv.min[1] = Q(0);
  c.iv.max[1] = Q(4);
  return c;
}

static std::string CommonString(const Common &c) {
  std::string s = std::format(" {}", c.chart);
  for (int i = 0; i < 3; i++) for (int k = 0; k < 3; k++) s += " " + R(c.tri[i][k]);
  for (int a = 0; a < 3; a++) s += " " + R(c.center[a]);
  for (int a = 0; a < 3; a++) s += " " + R(c.radius[a]);
  return s;
}

static Q ParseQ(const std::string &s) { return Q(s); }

int main(int argc, char **argv) {
  if (Golden().empty() || !std::filesystem::exists(Golden())) {
    printf("SKIPPED exact5d_test: no Lean exact5d_golden executable (it is not in this "
           "repository's ../../proof; set EXACT5D_GOLDEN to one built in Noperthedron)%s%s\n",
           Golden().empty() ? "" : "; not found: ", Golden().c_str());
    return 0;
  }
  if (!HaveCodebddJson("exact5d_test")) return 0;
  const int num_global = argc > 1 ? atoi(argv[1]) : 150;
  const int num_mixed = argc > 2 ? atoi(argv[2]) : 40;
  const int num_prune = argc > 3 ? atoi(argv[3]) : 300;

  rapidjson::Document doc;
  doc.Parse(Util::ReadFile(CodebddJson()).c_str());
  CHECK(!doc.HasParseError());
  std::vector<TriangleQ> code_tris;
  for (const auto &code : doc["codes"].GetArray()) {
    for (const auto &t : code["triangles"].GetArray()) {
      TriangleQ tri;
      for (int i = 0; i < 3; i++) {
        tri[i] = {Q(std::string_view(t[i]["x"].GetString())), Q(std::string_view(t[i]["y"].GetString())),
                  Q(std::string_view(t[i]["z"].GetString()))};
      }
      code_tris.push_back(tri);
    }
  }

  std::mt19937_64 rng(1234);
  std::vector<GlobalBox> gboxes;
  std::vector<MixedBox> mboxes;
  std::ostringstream input;
  for (int n = 0; n < num_global; n++) {
    Common c = RandomCommon(code_tris, rng);
    GlobalBox b;
    b.interval = c.iv;
    b.triangle = c.tri;
    b.chart = c.chart;
    if (n % 2 == 1 || !RealisticCert(c.tri, rng, &b.certificate)) b.certificate = RandomCert(rng);
    for (int i = 0; i < 3; i++) {
      // Inner vertex = outer support vertex is the identity-like case.
      b.inner_index[i] = (rng() % 2) ? b.certificate.index[i] : (int)(rng() % NUM_VERTICES);
    }
    b.ball_multiplier = Q((int64_t)(rng() % 100), 1000);
    gboxes.push_back(b);
    input << "G" << CommonString(c) << CertString(b.certificate)
          << std::format(" {} {} {} ", b.inner_index[0], b.inner_index[1], b.inner_index[2])
          << R(b.ball_multiplier) << "\n";
  }
  for (int n = 0; n < num_mixed; n++) {
    Common c = RandomCommon(code_tris, rng);
    MixedBox b;
    b.interval = c.iv;
    b.triangle = c.tri;
    b.chart = c.chart;
    input << "M" << CommonString(c);
    for (int k = 0; k < 4; k++) {
      if (k % 2 == 1 || !RealisticCert(c.tri, rng, &b.component[k].certificate)) {
        b.component[k].certificate = RandomCert(rng);
      }
      for (int i = 0; i < 3; i++) b.component[k].inner_index[i] = rng() % NUM_VERTICES;
      b.component[k].ball_multiplier = Q((int64_t)(rng() % 100), 1000);
      input << CertString(b.component[k].certificate)
            << std::format(" {} {} {} ", b.component[k].inner_index[0],
                           b.component[k].inner_index[1], b.component[k].inner_index[2])
            << R(b.component[k].ball_multiplier);
    }
    // Weights: sometimes summing to 1, sometimes not.
    std::array<int64_t, 4> w = {(int64_t)(rng() % 5), (int64_t)(rng() % 5), (int64_t)(rng() % 5), 0};
    int64_t total = w[0] + w[1] + w[2] + 1;
    w[3] = (rng() % 4 == 0) ? 2 : 1;
    for (int k = 0; k < 4; k++) {
      b.weight[k] = Q(w[k], total);
      input << " " << R(b.weight[k]);
    }
    input << "\n";
    mboxes.push_back(b);
  }

  // Prune/tube boxes: centers spread over the whole chart range (so the
  // fundamental prune and the ball prune both pass and fail), tube radii
  // near the identity mismatch radius.
  struct PruneCase {
    Interval5 iv;
    int chart;
    Q r;
  };
  std::vector<PruneCase> pcases;
  for (int n = 0; n < num_prune; n++) {
    PruneCase pc;
    pc.chart = rng() % 4;
    std::array<Q, 3> center, radius;
    for (int a = 0; a < 3; a++) {
      center[a] = Q((int64_t)(rng() % 4097) - 2048, 1024);  // [-2, 2]
      radius[a] = Q(1, (int64_t)1 << (1 + rng() % 12));
      pc.iv.min[a + 2] = center[a] - radius[a];
      pc.iv.max[a + 2] = center[a] + radius[a];
    }
    pc.iv.min[0] = Q(0); pc.iv.max[0] = Q(8, 5); pc.iv.min[1] = Q(0); pc.iv.max[1] = Q(4);
    // r just above or below the mismatch radius, or arbitrary.
    const Q m = IdentityMismatchRadius(pc.iv);
    const int mode = rng() % 3;
    pc.r = mode == 0 ? m : mode == 1 ? m - Q(1, 10000000000000000LL) : Q((int64_t)(rng() % 1000), 100);
    pcases.push_back(pc);
    input << "P " << pc.chart;
    for (int a = 0; a < 3; a++) input << " " << R(center[a]);
    for (int a = 0; a < 3; a++) input << " " << R(radius[a]);
    input << " " << R(pc.r) << "\n";
  }

  // Unique per process: concurrent runs must not share the input file.
  const std::string in_path = std::filesystem::temp_directory_path() /
                              std::format("exact5d_test_input.{}.txt", (int)getpid());
  { std::ofstream f(in_path); f << input.str(); }
  const std::string cmd = std::format("{} < {}", Golden(), in_path);
  FILE *p = popen(cmd.c_str(), "r");
  CHECK(p != nullptr);
  std::vector<std::string> lines;
  {
    std::string cur;
    int ch;
    while ((ch = fgetc(p)) != EOF) {
      if (ch == '\n') { lines.push_back(cur); cur.clear(); } else { cur += (char)ch; }
    }
  }
  CHECK(pclose(p) == 0);
  std::filesystem::remove(in_path);
  CHECK((int)lines.size() == num_global + num_mixed + num_prune) << lines.size();

  int compared = 0, admissible = 0, valid = 0;
  auto expect = [&](const std::vector<std::string> &tok, size_t idx, const Q &got,
                    const std::string &what, int box) {
    CHECK(idx < tok.size());
    const Q want = ParseQ(tok[idx]);
    CHECK(want == got) << "box " << box << " " << what << ": Lean " << tok[idx]
                       << " vs C++ " << got.ToString();
    compared++;
  };
  for (int n = 0; n < num_global; n++) {
    std::vector<std::string> tok;
    std::istringstream ss(lines[n]);
    for (std::string t; ss >> t;) tok.push_back(t);
    const GlobalBox &b = gboxes[n];
    size_t idx = 0;
    for (int i = 0; i < 3; i++) {
      for (int k = 0; k < NUM_VERTICES; k++) {
        expect(tok, idx++, SupportUpper(b, i, k), std::format("supportUpper {} {}", i, k), n);
      }
    }
    for (int i = 0; i < 3; i++) expect(tok, idx++, WeightLower(b, i), "weightLower", n);
    for (int i = 0; i < 3; i++) expect(tok, idx++, WeightUpper(b, i), "weightUpper", n);
    expect(tok, idx++, WeightedDefectUpper(b), "weightedDefectUpper", n);
    expect(tok, idx++, BernsteinDisplacementLower(b), "bernsteinDisplacementLower", n);
    const RatBall ball = AdjustedDisplacementBall(b);
    expect(tok, idx++, ball.center, "adjustedDisplacementBall.center", n);
    expect(tok, idx++, ball.radius, "adjustedDisplacementBall.radius", n);
    expect(tok, idx++, CertifiedDisplacementLower(b), "certifiedDisplacementLower", n);
    expect(tok, idx++, DBound(b), "dBound", n);
    expect(tok, idx++, DisplacementError(b), "displacementError", n);
    const bool adm = Admissible(b), val = Valid(b);
    CHECK(tok[idx++] == (adm ? "1" : "0")) << "box " << n << " admissible";
    CHECK(tok[idx++] == (val ? "1" : "0")) << "box " << n << " valid";
    admissible += adm;
    valid += val;
  }
  for (int n = 0; n < num_mixed; n++) {
    std::vector<std::string> tok;
    std::istringstream ss(lines[num_global + n]);
    for (std::string t; ss >> t;) tok.push_back(t);
    const MixedBox &b = mboxes[n];
    expect(tok, 0, BernsteinDisplacementLower(b), "mixed bernsteinDisplacementLower", n);
    expect(tok, 1, WeightedDefectUpper(b), "mixed weightedDefectUpper", n);
    CHECK(tok[2] == (Valid(b) ? "1" : "0")) << "mixed box " << n << " valid";
  }
  int outside = 0, fund_valid = 0, tube_valid = 0;
  for (int n = 0; n < num_prune; n++) {
    std::vector<std::string> tok;
    std::istringstream ss(lines[num_global + num_mixed + n]);
    for (std::string t; ss >> t;) tok.push_back(t);
    const PruneCase &pc = pcases[n];
    CHECK(tok.size() == 7) << lines[num_global + num_mixed + n];
    const bool out = OutsideCayleyBall(pc.iv);
    CHECK(tok[0] == (out ? "1" : "0")) << "prune " << n << " outsideCayleyBall";
    expect(tok, 1, FundamentalLower(pc.iv, pc.chart, 1), "fundamental lower +", n);
    expect(tok, 2, FundamentalLower(pc.iv, pc.chart, -1), "fundamental lower -", n);
    const bool fp = FundamentalPruneValid(pc.iv, pc.chart, 1);
    const bool fn = FundamentalPruneValid(pc.iv, pc.chart, -1);
    CHECK(tok[3] == (fp ? "1" : "0")) << "prune " << n << " fundamental +";
    CHECK(tok[4] == (fn ? "1" : "0")) << "prune " << n << " fundamental -";
    expect(tok, 5, IdentityMismatchRadius(pc.iv), "identity mismatch radius", n);
    const bool tv = IdentityTubeValid(pc.iv, pc.r);
    CHECK(tok[6] == (tv ? "1" : "0")) << "prune " << n << " tube valid";
    outside += out;
    fund_valid += fp + fn;
    tube_valid += tv;
  }
  printf("exact5d agrees with Lean: %d global + %d mixed + %d prune boxes, %d exact quantities "
         "(%d admissible, %d valid; %d outside ball, %d fundamental prunes, %d tube-valid)\n",
         num_global, num_mixed, num_prune, compared, admissible, valid, outside, fund_valid,
         tube_valid);
  return 0;
}
