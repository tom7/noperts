// Identity-tube certificate synthesis for the face-visibility code cells
// of the model. For each projective triangle of each code cell (from
// codebdd.json) we build a quadtree whose leaves carry
// pure Tag 1 (4-axis cage) certificates, audited in exact arithmetic
// with the same conditions as Lean's Box.ViewValid.
//
// The solver is restartable: every certified leaf ("L") and every split
// ("S") is appended to trees/code.<X>.journal as soon as it is decided.
// On restart the journal is replayed and only the pending frontier is
// worked on. Leaves are re-audited on replay, so a journal can never
// inject an unchecked certificate. When every triangle of a code is
// complete, the tree is written to trees/tree.<X>.json (the format read
// by export_codetrees_pack).
//
// With --import, a code with no journal is seeded from its existing
// tree.<X>.json: split nodes and Tag 1 leaves are kept (and re-audited);
// any other leaves (e.g. Tag 2) become pending again.

#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstdio>
#include <filesystem>
#include <functional>
#include <iostream>
#include <map>
#include <mutex>
#include <optional>
#include <string>
#include <thread>
#include <vector>

#include "rapidjson/document.h"
#include "util.h"
#include "yocto-math.h"
#include "model.h"
#include "bignum/big.h"
#include "bignum/big-vec.h"
#include "bignum/big-overloads.h"

using vec3 = yocto::vec<double, 3>;

#include "tubecert.cc"

#include "tubetree.h"

using namespace tubetree;

struct SolverOptions {
  std::string bdd_json = "codebdd.json";
  std::string output_dir = "trees";
  int code_id = -1; // -1 means all
  int tri_id = -1;  // -1 means all triangles of the code
  int num_threads = 16;
  int max_depth = 30;
  BigRat target_c{0}; // Any positive rational c > 0
  BigRat target_r{0}; // Any positive rational r > 0
  bool force = false;
  bool import_tree = false;
  // --cap x,y,z,rho (repeatable): views within angle rho of the unit vector
  // (x, y, z) are left to a separate argument (the deltoidal
  // hexecontahedron's 2-fold axis view and its two-kite views, where the
  // first-order margin tends to 0 and no first-order cage exists):
  // triangles inside a cap become cap leaves instead of being certified.
  struct Cap { double c[3]; double rho; };
  std::vector<Cap> caps;
  // --cap_r R: the tube radius cap leaves claim (tubetree::CapLeaf), for the
  // cap theorems to certify. With R > 0 the tree is written with cap leaves
  // (it is not packable until Lean has the cap theorems); with 0 (default)
  // codes with cap leaves stay incomplete.
  BigRat cap_r{0};
  // --min_r R: a leaf whose certified tube radius is below R is split instead
  // (until --max_depth, where any radius is kept); journal leaves below R are
  // re-certified. Small radii come from a large variation delta across the
  // triangle, which splitting reduces; a tiny radius forces the 5D search to
  // cover rotations down to it (the reached node's subtree minimum).
  BigRat min_r{0};
  // --best_cage: at every node also search for the best cage
  // (FindBestCageForTriangle) and keep whichever certificate has the larger
  // net margin c, instead of the first that passes (the inherited hint).
  // With --min_r, a hint that passes with a small radius is otherwise handed
  // down unchanged until splitting shrinks its delta enough, which can take
  // many levels where a fresh cage would have a much larger cover (the
  // Septopert near (0.9285, 0.3565, 0.1040): cover 1.6e-5 inherited to depth
  // 19-20, vs 4.3e-4 for the best cage).
  bool best_cage = false;
};

// Signed margin of the origin inside the tetrahedron with vertices p[0..3]:
// the minimum over faces of the distance from the origin to the face plane,
// positive iff the origin is strictly inside.
static double TetraMargin(const vec3 p[4]) {
  // Reject (nearly) flat tetrahedra: their face orientations are noise.
  double scale = 0;
  for (int i = 0; i < 4; i++) scale = std::max(scale, yocto::length(p[i]));
  const double vol6 = yocto::dot(yocto::cross(p[1] - p[0], p[2] - p[0]), p[3] - p[0]);
  if (!(std::abs(vol6) > 1e-9 * scale * scale * scale)) return -std::numeric_limits<double>::infinity();
  double margin = std::numeric_limits<double>::infinity();
  for (int skip = 0; skip < 4; skip++) {
    vec3 f[3];
    for (int j = 0, k = 0; j < 4; j++) if (j != skip) f[k++] = p[j];
    vec3 n = yocto::cross(f[1] - f[0], f[2] - f[0]);
    const double ln = yocto::length(n);
    if (ln < 1e-300) return -std::numeric_limits<double>::infinity();
    n /= ln;
    // Orient n toward the opposite vertex (inward).
    if (yocto::dot(n, p[skip] - f[0]) < 0) n = -n;
    margin = std::min(margin, -yocto::dot(n, f[0]));
  }
  return margin;
}

// Lean's Tag 1 check needs the axis-aligned octahedron with vertices
// +-rho e_k inside the tetrahedron of axis centers; this is the largest such
// rho (negative if the origin is outside): min over faces of h / |n|_inf,
// where h is the origin's distance to the face and n its unit normal.
static double TetraAxisRadius(const vec3 p[4]) {
  double scale = 0;
  for (int i = 0; i < 4; i++) scale = std::max(scale, yocto::length(p[i]));
  const double vol6 = yocto::dot(yocto::cross(p[1] - p[0], p[2] - p[0]), p[3] - p[0]);
  if (!(std::abs(vol6) > 1e-9 * scale * scale * scale)) return -std::numeric_limits<double>::infinity();
  double radius = std::numeric_limits<double>::infinity();
  for (int skip = 0; skip < 4; skip++) {
    vec3 f[3];
    for (int j = 0, k = 0; j < 4; j++) if (j != skip) f[k++] = p[j];
    vec3 n = yocto::normalize(yocto::cross(f[1] - f[0], f[2] - f[0]));
    if (yocto::dot(n, p[skip] - f[0]) < 0) n = -n;
    const double h = -yocto::dot(n, f[0]);
    const double ninf = std::max({std::abs(n.x), std::abs(n.y), std::abs(n.z)});
    radius = std::min(radius, h > 0 ? h / ninf : h);
  }
  return radius;
}

// If set, cages are chosen to maximize TetraAxisRadius (what Lean checks)
// and the support-point brute force always runs. (--axis_radius)
static bool g_axis_radius_objective = false;

// Deterministic search for a tetrahedron of candidate points containing
// the origin with a large margin: start from the support points in four
// regular-tetrahedron directions, then repeatedly take the face nearest
// the origin, find the support point along its outward normal, and swap
// it in for whichever vertex most improves the margin. Points with
// usable(i) == false are skipped. Random 4-subsets almost never contain
// the origin when the point cloud is elongated and the origin is near its
// boundary (e.g. close to an edge-on quad), which is where this matters.
static bool SupportSearchTetra(const std::vector<vec3> &pts,
                               const std::function<bool(int)> &usable,
                               std::array<int, 4> *out, double *out_margin) {
  const int N = pts.size();
  auto Support = [&](const vec3 &d) {
    int best = -1;
    double bv = -std::numeric_limits<double>::infinity();
    for (int i = 0; i < N; i++) {
      const double v = yocto::dot(pts[i], d);
      if (v > bv && usable(i)) { bv = v; best = i; }
    }
    return best;
  };
  const vec3 dirs[4] = {vec3{1, 1, 1}, vec3{1, -1, -1}, vec3{-1, 1, -1}, vec3{-1, -1, 1}};
  std::array<int, 4> cur;
  for (int k = 0; k < 4; k++) {
    cur[k] = Support(yocto::normalize(dirs[k]));
    if (cur[k] < 0) return false;
  }
  auto Margin = [&](const std::array<int, 4> &t) {
    vec3 p[4] = {pts[t[0]], pts[t[1]], pts[t[2]], pts[t[3]]};
    return TetraMargin(p);
  };
  double cur_m = Margin(cur);
  for (int iter = 0; iter < 500; iter++) {
    // Face nearest the origin (smallest signed distance), and its outward normal.
    vec3 p[4] = {pts[cur[0]], pts[cur[1]], pts[cur[2]], pts[cur[3]]};
    double worst = std::numeric_limits<double>::infinity();
    vec3 out_n{0, 0, 0};
    for (int skip = 0; skip < 4; skip++) {
      vec3 f[3];
      for (int j = 0, k = 0; j < 4; j++) if (j != skip) f[k++] = p[j];
      vec3 n = yocto::cross(f[1] - f[0], f[2] - f[0]);
      const double ln = yocto::length(n);
      if (ln < 1e-300) continue;
      n /= ln;
      if (yocto::dot(n, p[skip] - f[0]) < 0) n = -n;
      const double dist = -yocto::dot(n, f[0]);
      if (dist < worst) { worst = dist; out_n = -n; }
    }
    if (yocto::length(out_n) == 0) break;
    const int sp = Support(out_n);
    if (sp < 0) break;
    std::array<int, 4> best_t = cur;
    double best_m = cur_m;
    for (int k = 0; k < 4; k++) {
      if (cur[k] == sp) continue;
      std::array<int, 4> t = cur;
      t[k] = sp;
      const double m = Margin(t);
      if (m > best_m) { best_m = m; best_t = t; }
    }
    if (best_m <= cur_m * (1 + 1e-12) + 1e-300) break;
    cur = best_t;
    cur_m = best_m;
  }
  *out = cur;
  *out_margin = cur_m;
  return cur_m > 0;
}

// Find best cage for a given triangle, pre-validating AuditAxis on tri
static bool FindBestCageForTriangle(
    const TriangleQ &tri,
    unsigned int *seed,
    LocalCertificate *out_cert,
    double *out_margin) {

  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  vec3 center = (c0 + c1 + c2) / 3.0;
  double clen = yocto::length(center);
  if (clen < 1e-12) return false;
  center = center / clen;

  std::vector<CandidateTriple> candidates;
  // (An exact model admits exact support ties, which the double screen must
  // not reject: a slightly negative error lets them through to the audit.)
  GenerateCandidatesForView(center, tri, 8, true, solid::kModelExact ? -1e-12 : 1e-13, &candidates);
  if (candidates.size() < 4) return false;

  std::vector<vec3> pts;
  for (const auto &cand : candidates) pts.push_back(cand.normalized_a);

  // Axis audits are exact and expensive; memoize them per candidate.
  std::vector<int8_t> audit_ok(candidates.size(), -1);
  auto Audited = [&](int idx) {
    if (audit_ok[idx] < 0) {
      ContactInfo cts[3] = {candidates[idx].contacts[0],
                            candidates[idx].contacts[1],
                            candidates[idx].contacts[2]};
      AxisCertificate ax;
      BigVecQ3 cent;
      BigRat del;
      audit_ok[idx] = AuditAxis(tri, cts, &ax, &cent, &del, nullptr) ? 1 : 0;
    }
    return audit_ok[idx] == 1;
  };

  double best_margin = 0.0;
  std::array<int, 4> best_tet = {-1, -1, -1, -1};
  int N = pts.size();
  // Score of a tetrahedron of candidates (positive iff usable).
  auto Score = [&](const std::array<int, 4> &t) -> double {
    vec3 tp[4] = {pts[t[0]], pts[t[1]], pts[t[2]], pts[t[3]]};
    if (g_axis_radius_objective) return TetraAxisRadius(tp);
    double m, bary[4];
    return TetrahedronOriginMargin(tp, &m, bary) ? m : -std::numeric_limits<double>::infinity();
  };

  // 0. Deterministic support-point search; candidates failing the exact
  // audit are excluded and the search rerun.
  {
    std::vector<int8_t> excluded(N, 0);
    for (int round = 0; round < 8; round++) {
      std::array<int, 4> tet;
      double margin = 0;
      if (!SupportSearchTetra(pts, [&](int i) { return !excluded[i]; }, &tet, &margin)) break;
      bool all_ok = true;
      for (int idx : tet) {
        if (!Audited(idx)) { excluded[idx] = 1; all_ok = false; }
      }
      if (all_ok) {
        const double m2 = Score(tet);
        if (m2 > best_margin) {
          best_margin = m2;
          best_tet = tet;
        }
        break;
      }
    }
  }

  // 0b. If that failed: brute force over all 4-subsets of the support
  // points in 256 directions (the hull's relevant extreme points), taking
  // the best tetrahedra in order until one passes the exact audit.
  if (best_margin <= 0 || g_axis_radius_objective) {
    std::vector<int> sup;
    {
      std::vector<int8_t> seen(N, 0);
      const int K = 256;
      for (int i = 0; i < K; i++) {
        const double z = 1 - 2 * (i + 0.5) / K, r = std::sqrt(std::max(0.0, 1 - z * z));
        const double ph = i * 2.399963229728653;
        const vec3 d{r * std::cos(ph), r * std::sin(ph), z};
        // Support point among candidates that pass the exact audit.
        for (;;) {
          int bi = -1;
          double bv = -std::numeric_limits<double>::infinity();
          for (int j = 0; j < N; j++) {
            if (audit_ok[j] == 0) continue;
            const double v = yocto::dot(pts[j], d);
            if (v > bv) { bv = v; bi = j; }
          }
          if (bi < 0) break;
          if (!Audited(bi)) continue;  // marks audit_ok[bi] = 0
          if (!seen[bi]) { seen[bi] = 1; sup.push_back(bi); }
          break;
        }
      }
    }
    const int S = sup.size();
    std::vector<std::pair<double, std::array<int, 4>>> top;
    for (int a = 0; a < S; a++)
      for (int b = a + 1; b < S; b++)
        for (int c = b + 1; c < S; c++)
          for (int d = c + 1; d < S; d++) {
            const vec3 tp[4] = {pts[sup[a]], pts[sup[b]], pts[sup[c]], pts[sup[d]]};
            const double m = g_axis_radius_objective ? TetraAxisRadius(tp) : TetraMargin(tp);
            if (m <= 0) continue;
            if (top.size() < 32 || m > top.back().first) {
              top.push_back({m, {sup[a], sup[b], sup[c], sup[d]}});
              std::sort(top.begin(), top.end(), [](const auto &x, const auto &y) { return x.first > y.first; });
              if (top.size() > 32) top.pop_back();
            }
          }
    for (const auto &[m, tet] : top) {
      if (Audited(tet[0]) && Audited(tet[1]) && Audited(tet[2]) && Audited(tet[3])) {
        const double m2 = Score(tet);
        if (m2 > best_margin) {
          best_margin = m2;
          best_tet = tet;
        }
        break;
      }
    }
  }

  // 1. Search for maximal margin cage via trials
  for (int trial = 0; trial < 25000; trial++) {
    int i0 = rand_r(seed) % N, i1 = rand_r(seed) % N, i2 = rand_r(seed) % N, i3 = rand_r(seed) % N;
    if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
    const double margin = Score({i0, i1, i2, i3});
    if (margin > best_margin) {
      if (Audited(i0) && Audited(i1) && Audited(i2) && Audited(i3)) {
        best_margin = margin;
        best_tet = {i0, i1, i2, i3};
      }
    }
  }

  // 2. Fallback to Wolfe algorithm if no positive-margin audited cage found
  if (best_margin <= 0) {
    std::array<int, 4> wolfe_tet;
    if (FindBalancedTetrahedron(pts, &wolfe_tet, false)) {
      vec3 tpts[4] = {pts[wolfe_tet[0]], pts[wolfe_tet[1]], pts[wolfe_tet[2]], pts[wolfe_tet[3]]};
      double margin;
      double bary[4];
      if (TetrahedronOriginMargin(tpts, &margin, bary) && margin > 0) {
        bool all_ok = true;
        for (int idx : wolfe_tet) all_ok = all_ok && Audited(idx);
        if (all_ok) {
          best_margin = margin;
          best_tet = wolfe_tet;
        }
      }
    }
  }

  if (best_margin <= 0) return false;

  for (int a = 0; a < 4; a++) {
    out_cert->axes[a].contacts[0] = candidates[best_tet[a]].contacts[0];
    out_cert->axes[a].contacts[1] = candidates[best_tet[a]].contacts[1];
    out_cert->axes[a].contacts[2] = candidates[best_tet[a]].contacts[2];
  }
  *out_margin = best_margin;
  return true;
}

// ---------------- Journal ----------------

// Journal lines (one record per line, space separated):
//   L <tri> <path> <sym> <72 ints: 4 axes x 3 contacts x
//                          (edge_start edge_finish edge_start2 edge_finish2 mix vertex)>
//   S <tri> <path>
// The root path is written as ".". A truncated final line is ignored.

static std::string PathToken(const std::string &path) {
  return path.empty() ? "." : path;
}

static std::string LeafLine(int tri, const std::string &path, const LocalCertificate &cert) {
  std::string s = StringPrintf("L %d %s %d", tri, PathToken(path).c_str(), cert.symmetry_index);
  for (int a = 0; a < 4; a++) {
    for (int k = 0; k < 3; k++) {
      const ContactInfo &c = cert.axes[a].contacts[k];
      StringAppendF(&s, " %d %d %d %d %d %d", c.edge_start, c.edge_finish,
                    c.edge_start2, c.edge_finish2, c.mix, c.vertex);
    }
  }
  s += "\n";
  return s;
}

struct JournalRecord {
  bool is_split = false;
  LocalCertificate cert; // contacts only (for leaves)
};

// Key: (triangle index, path).
using JournalMap = std::map<std::pair<int, std::string>, JournalRecord>;

static bool ParseJournalLine(const std::string &line, int *tri, std::string *path,
                             JournalRecord *rec) {
  std::vector<std::string> tok = Util::Tokens(line, [](char c) { return c == ' '; });
  if (tok.size() < 3) return false;
  *tri = atoi(tok[1].c_str());
  *path = tok[2] == "." ? "" : tok[2];
  for (char c : *path) if (c < '0' || c > '3') return false;
  if (tok[0] == "S") {
    if (tok.size() != 3) return false;
    rec->is_split = true;
    return true;
  }
  if (tok[0] != "L" || tok.size() != 4 + 72) return false;
  rec->is_split = false;
  rec->cert.symmetry_index = atoi(tok[3].c_str());
  int t = 4;
  for (int a = 0; a < 4; a++) {
    for (int k = 0; k < 3; k++) {
      ContactInfo &c = rec->cert.axes[a].contacts[k];
      c.edge_start = atoi(tok[t++].c_str());
      c.edge_finish = atoi(tok[t++].c_str());
      c.edge_start2 = atoi(tok[t++].c_str());
      c.edge_finish2 = atoi(tok[t++].c_str());
      c.mix = atoi(tok[t++].c_str());
      c.vertex = atoi(tok[t++].c_str());
    }
  }
  return true;
}

static JournalMap ReadJournal(const std::string &filename) {
  JournalMap m;
  if (!std::filesystem::exists(filename)) return m;
  std::string content = Util::ReadFile(filename);
  size_t pos = 0;
  int bad = 0;
  while (pos < content.size()) {
    size_t nl = content.find('\n', pos);
    // Without a newline, the last record was cut off mid-write.
    if (nl == std::string::npos) { bad++; break; }
    std::string line = content.substr(pos, nl - pos);
    pos = nl + 1;
    int tri;
    std::string path;
    JournalRecord rec;
    if (line.rfind("C ", 0) == 0) continue;  // cap leaf (informational)
    if (!ParseJournalLine(line, &tri, &path, &rec)) { bad++; continue; }
    // First record wins; a node is only decided once.
    m.emplace(std::make_pair(tri, path), rec);
  }
  if (bad) {
    std::cerr << "[journal] " << filename << ": ignored " << bad << " malformed/truncated lines\n";
  }
  return m;
}

// Import from an existing tree.X.json: keep splits and Tag 1 leaves.
static void ImportTreeNode(int tri, const TreeNode &node, const std::string &path,
                           JournalMap *m, int *leaves, int *dropped) {
  if (!node.children.empty()) {
    (*m)[{tri, path}].is_split = true;
    for (int c = 0; c < (int)node.children.size(); c++) {
      if (node.children[c])
        ImportTreeNode(tri, *node.children[c], path + (char)('0' + c), m, leaves, dropped);
    }
  } else if (node.direct_cert.has_value()) {
    JournalRecord rec;
    rec.cert = node.direct_cert.value();
    (*m)[{tri, path}] = rec;
    (*leaves)++;
  } else {
    (*dropped)++;
  }
}

// ---------------- Solver ----------------

struct WorkItem {
  int tri = 0;
  std::string path;
  TriangleQ triangle;
  std::optional<LocalCertificate> hint;
  // Number of consecutive ancestors that skipped the fresh cage search.
  int skips = 0;
};

class CodeSolver {
 public:
  CodeSolver(int code_idx, const rapidjson::Value &code_obj, const SolverOptions &opt)
      : code_idx_(code_idx), opt_(opt) {
    code_hex_ = code_obj["code_hex"].GetString();
    const auto &tri_arr = code_obj["triangles"].GetArray();
    for (rapidjson::SizeType t = 0; t < tri_arr.Size(); t++) {
      TriangleQ tq;
      for (int k = 0; k < 3; k++) {
        tq.corners[k] = BigVecQ3(tri_arr[t][k]["x"].GetString(),
                                 tri_arr[t][k]["y"].GetString(),
                                 tri_arr[t][k]["z"].GetString());
      }
      roots_.push_back(tq);
    }
    journal_path_ = StringPrintf("%s/code.%d.journal", opt.output_dir.c_str(), code_idx);
    tree_path_ = StringPrintf("%s/tree.%d.json", opt.output_dir.c_str(), code_idx);
  }

  // Returns true if every triangle of the code is fully certified.
  bool Run() {
    if (!opt_.force && !std::filesystem::exists(journal_path_) &&
        std::filesystem::exists(tree_path_)) {
      auto loaded = LoadCodeTreeJson(tree_path_);
      if (loaded && loaded->IsFullyCertified() && AllTag1(*loaded)) {
        printf("[Code %d] %s already fully certified with Tag 1 (%d leaves). Skipping.\n",
               code_idx_, tree_path_.c_str(), loaded->TotalLeaves());
        return true;
      }
      if (loaded && opt_.import_tree) {
        JournalMap m;
        int leaves = 0, dropped = 0;
        for (const auto &ct : loaded->triangles) {
          if (ct.root) ImportTreeNode(ct.triangle_index, *ct.root, "", &m, &leaves, &dropped);
        }
        std::string s;
        for (const auto &[key, rec] : m) {
          if (rec.is_split) s += StringPrintf("S %d %s\n", key.first, PathToken(key.second).c_str());
          else s += LeafLine(key.first, key.second, rec.cert);
        }
        CHECK(Util::WriteFile(journal_path_, s));
        printf("[Code %d] Imported %d Tag 1 leaves from %s (%d other leaves left pending).\n",
               code_idx_, leaves, tree_path_.c_str(), dropped);
      }
    }
    if (opt_.force && std::filesystem::exists(journal_path_)) {
      std::filesystem::rename(journal_path_, journal_path_ + ".old");
    }

    journal_ = ReadJournal(journal_path_);
    std::vector<WorkItem> replay_leaves;
    for (int t = 0; t < (int)roots_.size(); t++) {
      if (opt_.tri_id >= 0 && t != opt_.tri_id) continue;
      Replay(t, "", roots_[t], &replay_leaves);
    }
    int replayed = AuditReplayedLeaves(&replay_leaves);
    printf("[Code %d] Replayed %d journal leaves; %zu pending nodes.\n",
           code_idx_, replayed, queue_.size());
    fflush(stdout);

    journal_out_ = fopen(journal_path_.c_str(), "ab");
    CHECK(journal_out_ != nullptr) << journal_path_;

    auto start = std::chrono::steady_clock::now();
    std::vector<std::thread> threads;
    for (int i = 0; i < opt_.num_threads; i++) {
      threads.emplace_back([this, i]() { Worker(i); });
    }
    std::thread status([this, start]() { StatusLoop(start); });
    for (auto &th : threads) th.join();
    {
      std::lock_guard<std::mutex> l(mu_);
      done_ = true;
    }
    status_cv_.notify_all();
    status.join();
    fclose(journal_out_);
    journal_out_ = nullptr;

    if (cap_leaves_.load() > 0) printf("[Code %d] %lld cap leaves (left to the cap argument).\n", code_idx_, (long long)cap_leaves_.load());
    printf("[Code %d] Finished: %lld new leaves, %lld new splits, %lld failures.\n",
           code_idx_, (long long)new_leaves_.load(), (long long)new_splits_.load(),
           (long long)failures_.load());
    if (failures_.load() > 0) return false;
    if (opt_.tri_id >= 0) {
      printf("[Code %d] Only triangle %d was solved; not writing %s.\n",
             code_idx_, opt_.tri_id, tree_path_.c_str());
      return true;
    }
    return WriteTree();
  }

 private:
  static bool AllTag1(const CodeTree &ct) {
    std::function<bool(const TreeNode &)> rec = [&](const TreeNode &n) {
      if (!n.children.empty()) {
        for (const auto &c : n.children) if (!c || !rec(*c)) return false;
        return true;
      }
      return n.direct_cert.has_value() && !n.decomposed_cert.has_value();
    };
    for (const auto &t : ct.triangles) if (!t.root || !rec(*t.root)) return false;
    return true;
  }

  // Walk the journal from a node; queue pending nodes and collect the
  // journal leaves, which are re-audited (in parallel) before being
  // trusted.
  void Replay(int tri, const std::string &path, const TriangleQ &triangle,
              std::vector<WorkItem> *leaves) {
    if (InCap(triangle)) {
      cap_leaves_++;
      return;
    }
    auto it = journal_.find({tri, path});
    if (it == journal_.end()) {
      queue_.push_back({tri, path, triangle, std::nullopt});
      return;
    }
    if (it->second.is_split) {
      TriangleQ ch[4];
      triangle.Subdivide(ch);
      for (int c = 0; c < 4; c++) Replay(tri, path + (char)('0' + c), ch[c], leaves);
      return;
    }
    leaves->push_back({tri, path, triangle, it->second.cert});
  }

  // Re-audit journal leaves; failures go back to the queue (with their
  // contacts as a hint).
  int AuditReplayedLeaves(std::vector<WorkItem> *leaves) {
    std::atomic<size_t> next{0};
    std::atomic<int> good{0};
    std::vector<std::thread> threads;
    for (int i = 0; i < opt_.num_threads; i++) {
      threads.emplace_back([&]() {
        for (;;) {
          size_t idx = next.fetch_add(1);
          if (idx >= leaves->size()) return;
          WorkItem &item = (*leaves)[idx];
          LocalCertificate audited;
          std::string why;
          bool ok = ReauditCertificate(item.triangle, *item.hint, opt_.target_c,
                                       opt_.target_r, &audited, &why);
          if (ok && opt_.min_r > BigRat(0) && audited.r < opt_.min_r && (int)item.path.size() < opt_.max_depth) {
            ok = false;
            why = "r < min_r";
          }
          std::lock_guard<std::mutex> l(mu_);
          if (ok) {
            audited_[{item.tri, item.path}] = audited;
            good++;
          } else {
            fprintf(stderr, "[Code %d] journal leaf tri %d path %s failed re-audit (%s); requeued\n",
                    code_idx_, item.tri, PathToken(item.path).c_str(), why.c_str());
            journal_.erase({item.tri, item.path});
            queue_.push_back(item);
          }
        }
      });
    }
    for (auto &th : threads) th.join();
    return good.load();
  }

  void Append(const std::string &line) {
    // Called with mu_ held.
    fwrite(line.data(), 1, line.size(), journal_out_);
    fflush(journal_out_);
  }

  bool TryCertify(const WorkItem &item, unsigned int *seed, LocalCertificate *out,
                  std::optional<LocalCertificate> *next_hint, bool *skip_search,
                  std::string *why_out) {
    const int depth = item.path.size();
    std::string &why = *why_out;
    *skip_search = false;
    if (item.hint.has_value()) {
      BigRat cover(-1), delta(-1);
      if (ReauditCertificate(item.triangle, *item.hint, opt_.target_c, opt_.target_r, out, &why,
                             &cover, &delta)) {
        if (!opt_.best_cage) return true;
        // Keep the larger net margin of the hint and the best cage.
        LocalCertificate local, audited;
        double margin = 0;
        std::string why2;
        if (FindBestCageForTriangle(item.triangle, seed, &local, &margin) &&
            ReauditCertificate(item.triangle, local, opt_.target_c, opt_.target_r, &audited, &why2) &&
            audited.c > out->c)
          *out = audited;
        return true;
      }
      // If the parent's cage fails only because the variation delta is a
      // bit too large, one or two more splits (which roughly halve delta)
      // will fix it; skip the (expensive) fresh search. Never skip more
      // than twice in a row, since a cage with tiny cover never recovers.
      if (depth > 6 && item.skips < 2 && why.rfind("cover <= delta", 0) == 0 &&
          cover > BigRat(0) && cover * BigRat(4) >= delta) {
        *skip_search = true;
        return false;
      }
    }

    LocalCertificate local;
    double margin = 0;
    bool has_local = FindBestCageForTriangle(item.triangle, seed, &local, &margin);
    why = has_local ? "" : StringPrintf("no cage (margin %.3g)", margin);
    if (!has_local) {
      has_local = SynthesizeCertificate(item.triangle, depth, opt_.target_c, opt_.target_r,
                                        &local, false);
    }
    if (has_local) {
      if (ReauditCertificate(item.triangle, local, opt_.target_c, opt_.target_r, out, &why))
        return true;
      *next_hint = local;
    }
    return false;
  }

  // Whether every point of the triangle is within the cap: its corners
  // are, and the cap (a spherical disk of radius < 90 degrees) is convex
  // on the sphere, so the geodesic triangle is too.
  bool InCap(const TriangleQ &tri, int *index = nullptr) const {
    for (int ci = 0; ci < (int)opt_.caps.size(); ci++) {
      const auto &cap = opt_.caps[ci];
      const vec3 c{cap.c[0], cap.c[1], cap.c[2]};
      bool in = true;
      for (int k = 0; k < 3 && in; k++) {
        const vec3 v = yocto::normalize(vec3{tri.corners[k].x.ToDouble(), tri.corners[k].y.ToDouble(), tri.corners[k].z.ToDouble()});
        in = std::acos(std::clamp(yocto::dot(v, c), -1.0, 1.0)) <= cap.rho;
      }
      if (in) {
        if (index) *index = ci;
        return true;
      }
    }
    return false;
  }

  void Worker(int thread_idx) {
    for (;;) {
      WorkItem item;
      {
        std::unique_lock<std::mutex> l(mu_);
        cv_.wait(l, [this]() { return !queue_.empty() || active_ == 0; });
        if (queue_.empty()) {
          cv_.notify_all();
          return;
        }
        // LIFO keeps the frontier small (depth-first).
        item = std::move(queue_.back());
        queue_.pop_back();
        active_++;
      }

      unsigned int seed = 42 + 1000 * code_idx_ + 7919 * item.tri;
      for (char c : item.path) seed = seed * 31 + c;

      LocalCertificate audited;
      std::optional<LocalCertificate> next_hint = item.hint;
      bool skipped = false;
      const int depth = item.path.size();
      if (InCap(item.triangle)) {
        std::lock_guard<std::mutex> l(mu_);
        Append(StringPrintf("C %d %s\n", item.tri, PathToken(item.path).c_str()));
        cap_leaves_++;
        active_--;
        cv_.notify_all();
        continue;
      }
      std::string why;
      bool ok = TryCertify(item, &seed, &audited, &next_hint, &skipped, &why);
      if (ok && opt_.min_r > BigRat(0) && audited.r < opt_.min_r && depth < opt_.max_depth) {
        ok = false;
        next_hint = audited;
        why = "r < min_r";
      }

      std::vector<WorkItem> children;
      {
        std::lock_guard<std::mutex> l(mu_);
        if (ok) {
          Append(LeafLine(item.tri, item.path, audited));
          journal_[{item.tri, item.path}].cert = audited;
          audited_[{item.tri, item.path}] = audited;
          new_leaves_++;
          min_c_ = min_c_ == 0 ? audited.c.ToDouble() : std::min(min_c_, audited.c.ToDouble());
        } else if (depth >= opt_.max_depth) {
          failures_++;
          const auto &cc = item.triangle.corners;
          fprintf(stderr, "[Code %d] FAILED tri %d path %s at max depth %d near (%.10f %.10f %.10f): %s\n",
                  code_idx_, item.tri, item.path.c_str(), depth,
                  cc[0].x.ToDouble(), cc[0].y.ToDouble(), cc[0].z.ToDouble(), why.c_str());
        } else {
          Append(StringPrintf("S %d %s\n", item.tri, PathToken(item.path).c_str()));
          journal_[{item.tri, item.path}].is_split = true;
          new_splits_++;
          max_depth_seen_ = std::max(max_depth_seen_, depth + 1);
          TriangleQ ch[4];
          item.triangle.Subdivide(ch);
          // Push in reverse so child 0 is processed first.
          for (int c = 3; c >= 0; c--) {
            queue_.push_back({item.tri, item.path + (char)('0' + c), ch[c], next_hint,
                              skipped ? item.skips + 1 : 0});
          }
        }
        active_--;
      }
      cv_.notify_all();
    }
  }

  void StatusLoop(std::chrono::steady_clock::time_point start) {
    std::unique_lock<std::mutex> l(mu_);
    auto next_report = std::chrono::steady_clock::now() + std::chrono::seconds(60);
    while (!done_) {
      status_cv_.wait_until(l, next_report);
      if (done_) break;
      if (std::chrono::steady_clock::now() < next_report) continue;
      next_report += std::chrono::seconds(60);
      double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
      printf("[Code %d %.0fs] leaves +%lld, splits +%lld, pending %zu, active %d, max depth %d, min c %.3g, failures %lld\n",
             code_idx_, secs, (long long)new_leaves_.load(), (long long)new_splits_.load(),
             queue_.size(), active_, max_depth_seen_, min_c_, (long long)failures_.load());
      fflush(stdout);
    }
  }

  // Build the full tree from the (audited) journal records and save.
  bool WriteTree() {
    const JournalMap &m = journal_;
    CodeTree code_tree;
    code_tree.code_id = code_idx_;
    code_tree.code_hex = code_hex_;
    int total = 0;
    for (int t = 0; t < (int)roots_.size(); t++) {
      CodeTriangleTree ct;
      ct.triangle_index = t;
      ct.triangle = roots_[t];
      ct.root = Build(m, t, "", roots_[t], &total);
      if (!ct.root) {
        fprintf(stderr, "[Code %d] Triangle %d incomplete; not writing tree.\n", code_idx_, t);
        return false;
      }
      code_tree.triangles.push_back(std::move(ct));
    }
    CHECK(code_tree.IsFullyCertified());
    if (!SaveCodeTreeJson(code_tree, tree_path_)) {
      fprintf(stderr, "[Code %d] Failed to save %s\n", code_idx_, tree_path_.c_str());
      return false;
    }
    printf("[Code %d] SUCCESS: %d Tag 1 leaves across %zu triangles -> %s\n",
           code_idx_, total, roots_.size(), tree_path_.c_str());
    return true;
  }

  std::unique_ptr<TreeNode> Build(const JournalMap &m, int tri, const std::string &path,
                                  const TriangleQ &triangle, int *total) {
    // A triangle inside a cap is a cap leaf, whatever the journal has below
    // it (earlier runs without the cap split it down to max depth).
    int cap_index = -1;
    if (opt_.cap_r > BigRat(0) && InCap(triangle, &cap_index)) {
      auto node = std::make_unique<TreeNode>();
      node->path = path;
      node->explicit_triangle = triangle;
      node->cap = tubetree::CapLeaf{cap_index, opt_.cap_r};
      node->direct_bounds.direct_r_lower = opt_.cap_r;
      (*total)++;
      return node;
    }
    auto it = m.find({tri, path});
    if (it == m.end()) return nullptr;
    auto node = std::make_unique<TreeNode>();
    node->path = path;
    node->explicit_triangle = triangle;
    if (it->second.is_split) {
      TriangleQ ch[4];
      triangle.Subdivide(ch);
      node->children.resize(4);
      for (int c = 0; c < 4; c++) {
        node->children[c] = Build(m, tri, path + (char)('0' + c), ch[c], total);
        if (!node->children[c]) return nullptr;
      }
      return node;
    }
    auto ait = audited_.find({tri, path});
    if (ait == audited_.end()) return nullptr;
    const LocalCertificate &audited = ait->second;
    node->direct_cert = audited;
    node->direct_bounds.direct_r_lower = audited.r;
    node->direct_bounds.direct_c_lower = audited.c;
    (*total)++;
    return node;
  }

  const int code_idx_;
  const SolverOptions opt_;
  std::string code_hex_;
  std::vector<TriangleQ> roots_;
  std::string journal_path_, tree_path_;
  JournalMap journal_;
  FILE *journal_out_ = nullptr;

  std::mutex mu_;
  std::condition_variable cv_, status_cv_;
  std::map<std::pair<int, std::string>, LocalCertificate> audited_;
  std::vector<WorkItem> queue_;
  int active_ = 0;
  bool done_ = false;
  int max_depth_seen_ = 0;
  double min_c_ = 0;
  std::atomic<int64_t> new_leaves_{0}, new_splits_{0}, failures_{0}, cap_leaves_{0};
};

#ifndef TUBECODE_NO_MAIN
int main(int argc, char **argv) {
  SolverOptions opt;
  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--code" && i + 1 < argc) {
      opt.code_id = std::stoi(argv[++i]);
    } else if (arg == "--tri" && i + 1 < argc) {
      opt.tri_id = std::stoi(argv[++i]);
    } else if (arg == "--threads" && i + 1 < argc) {
      opt.num_threads = std::stoi(argv[++i]);
    } else if (arg == "--max_depth" && i + 1 < argc) {
      opt.max_depth = std::stoi(argv[++i]);
    } else if (arg == "--output_dir" && i + 1 < argc) {
      opt.output_dir = argv[++i];
    } else if (arg == "--force") {
      opt.force = true;
    } else if (arg == "--import") {
      opt.import_tree = true;
    } else if (arg == "--cap" && i + 1 < argc) {
      SolverOptions::Cap cap;
      CHECK(std::sscanf(argv[++i], "%lf,%lf,%lf,%lf", &cap.c[0], &cap.c[1], &cap.c[2], &cap.rho) == 4);
      const double n = std::sqrt(cap.c[0] * cap.c[0] + cap.c[1] * cap.c[1] + cap.c[2] * cap.c[2]);
      for (double &x : cap.c) x /= n;
      opt.caps.push_back(cap);
    } else if (arg == "--cap_r" && i + 1 < argc) {
      opt.cap_r = BigRat(std::string_view(argv[++i]));
    } else if (arg == "--min_r" && i + 1 < argc) {
      opt.min_r = BigRat(std::string_view(argv[++i]));
    } else if (arg == "--best_cage") {
      opt.best_cage = true;
    } else if (arg == "--axis_radius") {
      g_axis_radius_objective = true;
    } else {
      fprintf(stderr, "Unknown argument %s\n"
              "Usage: tubecode.exe [--code X [--tri T]] [--threads N] [--max_depth D] [--min_r R]\n"
              "                       [--output_dir DIR] [--force] [--import] [--axis_radius] [--best_cage]\n", arg.c_str());
      return 2;
    }
  }

  std::filesystem::create_directories(opt.output_dir);

  std::string bdd_content = Util::ReadFile(opt.bdd_json);
  rapidjson::Document doc;
  doc.Parse(bdd_content.c_str());
  CHECK(!doc.HasParseError() && doc.HasMember("codes"));

  const auto &codes = doc["codes"].GetArray();
  int num_codes = static_cast<int>(codes.Size());

  std::vector<int> todo;
  if (opt.code_id >= 0) {
    if (opt.code_id >= num_codes) {
      std::cerr << "Invalid code id " << opt.code_id << " (total " << num_codes << ")\n";
      return 1;
    }
    todo.push_back(opt.code_id);
  } else {
    for (int c = 0; c < num_codes; c++) todo.push_back(c);
  }

  // Codes are solved one at a time, each using all worker threads.
  int ok = 0, failed = 0;
  for (int c : todo) {
    CodeSolver solver(c, codes[c], opt);
    if (solver.Run()) ok++;
    else failed++;
  }
  printf("Synthesis finished: %d/%zu codes complete, %d incomplete.\n", ok, todo.size(), failed);
  return failed == 0 ? 0 : 1;
}
#endif
