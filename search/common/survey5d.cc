// survey5d: where do a solid's 5D solution tables spend their rows? Reads the
// per-code packs (pack5d --per_code: DIR/c<chart>/t<T>.pack) and reports
// where the leaves concentrate, to find the regions (degenerate views, ties,
// thin margins) where better mathematics would pay off most. Diagnostic
// only: it trusts the packs' structure and reads numbers in double
// precision.
//
// Pack format (pack5d.cc Write; Lean PackedSolutionTree.decodeTable):
//   rows,#intervals,{3 centers, 3 radii},#triangles,{3 corners x 3},rows...
// every rational as two tokens (zigzag numerator, denominator), every row
// ",tag,id,interval,..." with a tag-dependent length. A leaf's view is its
// triangle (corners in the projective chart: a view v scaled so that
// sum_c sign_c v_c = 1); its rotation is its Cayley box (chart coordinates
// x, y, z; |w| the Cayley norm, rotation angle 2 atan |w|).
//
// Reports, per chart: rows by tag; leaves per code triangle; the densest view
// cells (normalized view directions binned on a cube-map grid of --view_bin
// radians), with the leaves' Cayley norms and box sizes there; the leaves by
// Cayley norm (log bins); and the leaves by box size (the finest boxes are
// the densest spots). --csv writes one line per leaf (every --every-th):
// chart, code, tag, view direction, triangle diameter, Cayley center,
// radius, |w|.
//
// Usage: survey5d.exe --packs DIR [--charts 0,1,2,3] [--view_bin 0.02] [--top 25]
//          [--csv FILE] [--every 1] [--threads N]
//        survey5d.exe --tubes DIR [--view_bin 0.02] [--top 25] [--csv FILE] [--threads N]
//
// --tubes reads the identity-tube tables instead (export_codetrees_pack:
// DIR/manifest.txt and its packs): per table its rows, leaves, depths and
// certified radii, and over all tables the view cells with the most tube
// leaves (deep tube trees drag the 5D search's view triangles down with
// them: solve5d refines the view of a box containing the identity while the
// tube goes deeper). --csv: one line per tube leaf (table, tag, view,
// triangle diameter, depth, r, c, delta).

#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <map>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

#include "base/logging.h"

namespace {

// A memory-mapped-ish token reader over the whole file (read in one piece).
struct Tokens {
  std::string data;
  size_t pos = 0;
  bool Done() const { return pos >= data.size() || data[pos] == '\n'; }
  // The next token as a string view (digits; '-' allowed).
  std::pair<const char *, size_t> Next() {
    if (pos < data.size() && data[pos] == ',') pos++;
    const size_t start = pos;
    while (pos < data.size() && data[pos] != ',' && data[pos] != '\n') pos++;
    return {data.data() + start, pos - start};
  }
  long long Int() {
    auto [p, n] = Next();
    CHECK(n > 0 && n < 19) << "integer token of length " << n << " at " << pos;
    long long v = 0;
    bool neg = false;
    size_t i = 0;
    if (p[0] == '-') { neg = true; i = 1; }
    for (; i < n; i++) v = v * 10 + (p[i] - '0');
    return neg ? -v : v;
  }
  // A token as a double (any length).
  double Dbl() {
    auto [p, n] = Next();
    if (n < 18) {
      double v = 0;
      for (size_t i = 0; i < n; i++) v = v * 10 + (p[i] - '0');
      return v;
    }
    return std::strtod(std::string(p, n).c_str(), nullptr);
  }
  // A decimal token as mantissa * 10^exponent (any length: exact corners can
  // have hundreds of digits, beyond double's range).
  static std::pair<double, int> Big(const char *p, size_t n) {
    const size_t k = std::min<size_t>(n, 17);
    double m = 0;
    for (size_t i = 0; i < k; i++) m = m * 10 + (p[i] - '0');
    return {m, (int)(n - k)};
  }
  // A zigzag rational (two tokens): zz = 2 num (num >= 0) or -2 num - 1.
  double Rat() {
    auto [zp, zn] = Next();
    auto [dp, dn] = Next();
    // Lean zigzagInt: odd n is -(n + 1) / 2.
    const bool neg = (zp[zn - 1] - '0') % 2 == 1;
    auto [zm, ze] = Big(zp, zn);
    auto [dm, de] = Big(dp, dn);
    if (dm == 0) return 0;
    if (ze == 0 && neg) zm += 1;  // exact for short tokens; negligible otherwise
    const double v = (zm / 2) / dm * std::pow(10.0, ze - de);
    return neg ? -v : v;
  }
  void Skip(int k) { for (int i = 0; i < k; i++) Next(); }
};

struct Leaf {
  int code, tag, tri;
  std::array<float, 3> c, r;
};

struct Pack {
  int chart = 0, code = 0;
  std::vector<std::array<double, 6>> iv;
  std::vector<std::array<double, 9>> tris;
  std::vector<Leaf> leaves;
  std::map<int, int64_t> by_tag;
  int64_t rows = 0;
};

const char *TagName(int tag) {
  switch (tag) {
    case 1: return "cayleySplit";
    case 2: return "viewSplit";
    case 4: return "certificate";
    case 6: return "tube";
    case 7: return "radiusPrune";
    case 8: return "fundamentalPrune";
    case 9: return "mixedCertificate";
    case 10: return "codeRoot";
    case 11: return "regionRelax";
    case 12: return "cayleySplitAt";
    case 13: return "symmetryPrune";
    case 14: return "halfTurnPrune";
    case 15: return "tieLeaf";
    case 16: return "capLeaf";
    default: return "?";
  }
}

bool IsLeafTag(int tag) { return tag == 4 || tag == 6 || tag == 7 || tag == 8 || tag == 9 || tag >= 13; }

void ReadPack(const std::string &path, Pack *pk) {
  Tokens t;
  {
    std::ifstream f(path, std::ios::binary);
    CHECK(f.good()) << path;
    f.seekg(0, std::ios::end);
    t.data.resize(f.tellg());
    f.seekg(0);
    f.read(t.data.data(), t.data.size());
  }
  pk->rows = t.Int();
  const long long niv = t.Int();
  pk->iv.resize(niv);
  for (auto &v : pk->iv)
    for (int k = 0; k < 6; k++) v[k] = t.Rat();
  const long long ntri = t.Int();
  pk->tris.resize(ntri);
  for (auto &v : pk->tris)
    for (int k = 0; k < 9; k++) v[k] = t.Rat();
  int64_t read = 0;
  while (!t.Done()) {
    const int tag = t.Int();
    pk->by_tag[tag]++;
    read++;
    t.Int();  // id
    const int iv = t.Int();
    int region = -1;
    switch (tag) {
      case 1: t.Skip(3); t.Int(); region = t.Int(); break;           // k0 k1 axis root region
      case 2: t.Skip(4); t.Int(); region = t.Int(); break;           // k0..k3 root region
      case 12: t.Skip(5); t.Int(); region = t.Int(); break;          // k0 k1 axis cut(2) root region
      case 4: t.Int(); region = t.Int(); t.Skip(28); break;          // root region body
      case 9: t.Int(); region = t.Int(); t.Skip(120); break;
      case 6: {                                                      // 0 r(2) t len digits root region
        t.Skip(4);
        const int len = t.Int();
        t.Skip(len);
        t.Int();
        region = t.Int();
        break;
      }
      case 7: t.Int(); region = t.Int(); break;                      // root region
      case 8: case 13: case 14: case 16: t.Int(); t.Int(); region = t.Int(); break;
      case 15: t.Skip(4); t.Int(); region = t.Int(); break;          // normal rho(2) node root region
      case 11: t.Skip(2); region = t.Int(); t.Int(); break;          // content root exact outer
      case 10: { const int n = t.Int(); t.Skip(n); break; }
      default: LOG(FATAL) << path << ": unknown tag " << tag << " at row " << read;
    }
    if (IsLeafTag(tag)) {
      CHECK(iv >= 0 && iv < (int)pk->iv.size() && region >= 0 && region < (int)pk->tris.size()) << path;
      Leaf l;
      l.code = pk->code;
      l.tag = tag;
      l.tri = region;
      for (int k = 0; k < 3; k++) { l.c[k] = pk->iv[iv][k]; l.r[k] = std::abs(pk->iv[iv][3 + k]); }
      pk->leaves.push_back(l);
    }
  }
  CHECK(read == pk->rows) << path << ": read " << read << " rows, header says " << pk->rows;
}

// A tube leaf (export_codetrees_pack: tag 1 certificate, 2 decomposed
// certificate, 4 empty (a cap leaf)).
struct TubeLeaf {
  int tag, depth;
  std::array<double, 9> tri;
  double r = -1, c = 0, delta = 0;
};

struct TubeTable {
  std::string name;
  int code = 0, tri = 0;
  int64_t rows = 0;
  std::vector<TubeLeaf> leaves;
};

void ReadTubePack(const std::string &path, TubeTable *tt) {
  Tokens t;
  {
    std::ifstream f(path, std::ios::binary);
    CHECK(f.good()) << path;
    f.seekg(0, std::ios::end);
    t.data.resize(f.tellg());
    f.seekg(0);
    f.read(t.data.data(), t.data.size());
  }
  // Header: rows, symmetryIndex, table r, the base triangle's 9 corners.
  tt->rows = t.Int();
  t.Int();
  t.Rat();
  std::array<double, 9> base;
  for (double &x : base) x = t.Rat();
  // An axis: 21 small integers and B.
  auto skip_axis = [&]() { t.Skip(21); t.Rat(); };
  int64_t read = 0;
  while (!t.Done()) {
    const int tag = t.Int();
    read++;
    t.Int();  // id
    t.Int();  // root
    const int len = t.Int();
    std::array<double, 9> tri = base;
    for (int k = 0; k < len; k++) {
      const int d = t.Int();
      // tubetree::TriangleQ::Subdivide.
      std::array<double, 9> m;
      for (int c = 0; c < 3; c++) {
        m[c] = (tri[c] + tri[3 + c]) / 2;          // m01
        m[3 + c] = (tri[3 + c] + tri[6 + c]) / 2;  // m12
        m[6 + c] = (tri[6 + c] + tri[c]) / 2;      // m20
      }
      std::array<double, 9> n;
      auto set = [&](int i, const double *src) { for (int c = 0; c < 3; c++) n[3 * i + c] = src[c]; };
      switch (d) {
        case 0: set(0, &tri[0]); set(1, &m[0]); set(2, &m[6]); break;
        case 1: set(0, &m[0]); set(1, &tri[3]); set(2, &m[3]); break;
        case 2: set(0, &m[6]); set(1, &m[3]); set(2, &tri[6]); break;
        default: set(0, &m[0]); set(1, &m[3]); set(2, &m[6]); break;
      }
      tri = n;
    }
    switch (tag) {
      case 0: t.Skip(4); t.Rat(); break;  // children, rLower
      case 4: tt->leaves.push_back({.tag = 4, .depth = len, .tri = tri}); break;
      case 1: case 2: {
        t.Int();  // symmetryIndex
        for (int a = 0; a < 4; a++) skip_axis();
        TubeLeaf l{.tag = tag, .depth = len, .tri = tri};
        l.c = t.Rat();
        l.delta = t.Rat();
        l.r = t.Rat();
        if (tag == 2) {
          skip_axis();
          for (int k = 0; k < 8; k++) t.Rat();
        }
        tt->leaves.push_back(l);
        break;
      }
      default: LOG(FATAL) << path << ": unknown tube tag " << tag << " at row " << read;
    }
  }
  CHECK(read == tt->rows) << path << ": read " << read << " rows, header says " << tt->rows;
}

std::array<double, 3> Centroid(const std::array<double, 9> &t) {
  std::array<double, 3> v{};
  for (int i = 0; i < 3; i++)
    for (int c = 0; c < 3; c++) v[c] += t[3 * i + c] / 3;
  const double n = std::sqrt(v[0] * v[0] + v[1] * v[1] + v[2] * v[2]);
  for (double &x : v) x /= n;
  return v;
}

double Diameter(const std::array<double, 9> &t) {
  // Angular diameter of the triangle's corners (normalized).
  std::array<std::array<double, 3>, 3> u;
  for (int i = 0; i < 3; i++) {
    double n = 0;
    for (int c = 0; c < 3; c++) n += t[3 * i + c] * t[3 * i + c];
    n = std::sqrt(n);
    for (int c = 0; c < 3; c++) u[i][c] = t[3 * i + c] / n;
  }
  double d = 0;
  for (int i = 0; i < 3; i++)
    for (int j = i + 1; j < 3; j++) {
      double dot = 0;
      for (int c = 0; c < 3; c++) dot += u[i][c] * u[j][c];
      d = std::max(d, std::acos(std::clamp(dot, -1.0, 1.0)));
    }
  return d;
}

double CayleyNorm(const Leaf &l) {
  return std::sqrt((double)l.c[0] * l.c[0] + (double)l.c[1] * l.c[1] + (double)l.c[2] * l.c[2]);
}

std::vector<int> ParseInts(const std::string &s) {
  std::vector<int> r;
  size_t p = 0;
  while (p < s.size()) {
    size_t q = s.find(',', p);
    if (q == std::string::npos) q = s.size();
    r.push_back(std::stoi(s.substr(p, q - p)));
    p = q + 1;
  }
  return r;
}

// A cube-map bin of the normalized view direction v, of view_bin radians.
int64_t ViewCell(const std::array<double, 3> &v, double view_bin) {
  int face = 0;
  double m = 0;
  for (int c = 0; c < 3; c++) if (std::abs(v[c]) > m) { m = std::abs(v[c]); face = c; }
  const int sgn = v[face] > 0 ? 0 : 1;
  const int a = (face + 1) % 3, b = (face + 2) % 3;
  const int64_t ia = (int64_t)std::floor(std::atan(v[a] / m) / view_bin);
  const int64_t ib = (int64_t)std::floor(std::atan(v[b] / m) / view_bin);
  return ((int64_t)(2 * face + sgn) << 40) ^ ((ia + 100000) << 20) ^ (ib + 100000);
}

void SurveyTubes(const std::string &dir, double view_bin, int top, FILE *out, int threads) {
  std::vector<TubeTable> tables;
  {
    std::ifstream f(dir + "/manifest.txt");
    CHECK(f.good()) << dir << "/manifest.txt";
    std::string name, rows, r;
    int code, tri;
    while (f >> name >> code >> tri >> rows >> r) tables.push_back({.name = name, .code = code, .tri = tri});
  }
  std::atomic<int> nextk{0};
  std::vector<std::thread> pool;
  for (int th = 0; th < std::min<int>(threads, tables.size()); th++)
    pool.emplace_back([&]() {
      for (int k; (k = nextk++) < (int)tables.size();) ReadTubePack(dir + "/" + tables[k].name, &tables[k]);
    });
  for (auto &th : pool) th.join();

  int64_t rows = 0, leaves = 0;
  for (const TubeTable &tt : tables) { rows += tt.rows; leaves += tt.leaves.size(); }
  printf("=== %zu tube tables, %lld rows, %lld leaves\n", tables.size(), (long long)rows, (long long)leaves);
  printf("  %-22s %5s %9s %9s %5s %9s %9s %9s\n", "table (t = line)", "code", "rows", "leaves", "depth",
         "min r", "median r", "min tri");
  for (int k = 0; k < (int)tables.size(); k++) {
    const TubeTable &tt = tables[k];
    std::vector<double> rs;
    int depth = 0;
    double dmin = 1e9;
    for (const TubeLeaf &l : tt.leaves) {
      if (l.r >= 0) rs.push_back(l.r);
      depth = std::max(depth, l.depth);
      dmin = std::min(dmin, Diameter(l.tri));
    }
    std::sort(rs.begin(), rs.end());
    printf("  t%-3d %-17s %5d %9lld %9zu %5d %9.2e %9.2e %9.2e\n", k, tt.name.c_str(), tt.code, (long long)tt.rows,
           tt.leaves.size(), depth, rs.empty() ? -1.0 : rs[0], rs.empty() ? -1.0 : rs[rs.size() / 2], dmin);
  }

  struct Cell {
    int64_t n = 0;
    int depth = 0;
    double rmin = 1e9, cmin = 1e9, dmin = 1e9;
    std::array<double, 3> v{};
    std::map<int, int64_t> tables;
  };
  std::unordered_map<int64_t, Cell> cells;
  std::map<int, int64_t> rbins;
  for (int k = 0; k < (int)tables.size(); k++) {
    for (const TubeLeaf &l : tables[k].leaves) {
      const auto v = Centroid(l.tri);
      const double d = Diameter(l.tri);
      Cell &cl = cells[ViewCell(v, view_bin)];
      cl.n++;
      cl.depth = std::max(cl.depth, l.depth);
      if (l.r >= 0) cl.rmin = std::min(cl.rmin, l.r);
      if (l.r >= 0) cl.cmin = std::min(cl.cmin, l.c);
      cl.dmin = std::min(cl.dmin, d);
      cl.tables[k]++;
      for (int c = 0; c < 3; c++) cl.v[c] += v[c];
      rbins[l.r > 0 ? (int)std::floor(std::log2(l.r)) : -99]++;
      if (out != nullptr)
        fprintf(out, "%d,%d,%.9f,%.9f,%.9f,%.3e,%d,%.6e,%.6e,%.6e\n", k, l.tag, v[0], v[1], v[2], d, l.depth, l.r,
                l.c, l.delta);
    }
  }
  std::vector<std::pair<int64_t, const Cell *>> top_cells;
  for (const auto &[k, c] : cells) top_cells.push_back({c.n, &c});
  std::sort(top_cells.begin(), top_cells.end(), [](auto &x, auto &y) { return x.first > y.first; });
  printf("densest view cells (%.3f rad; %zu cells with tube leaves):\n", view_bin, cells.size());
  printf("  %10s %6s  %-28s %5s %9s %9s %9s  %s\n", "leaves", "%", "view (mean)", "depth", "min r", "min c",
         "min tri", "tables");
  int64_t cum = 0;
  for (int k = 0; k < std::min<int>(top, top_cells.size()); k++) {
    const Cell &c = *top_cells[k].second;
    cum += c.n;
    const double n = std::sqrt(c.v[0] * c.v[0] + c.v[1] * c.v[1] + c.v[2] * c.v[2]);
    std::string ts;
    for (auto [t, m] : c.tables) ts += " t" + std::to_string(t) + ":" + std::to_string(m);
    printf("  %10lld %5.1f%%  (%8.5f,%8.5f,%8.5f) %5d %9.2e %9.2e %9.2e %s\n", (long long)c.n, 100.0 * c.n / leaves,
           c.v[0] / n, c.v[1] / n, c.v[2] / n, c.depth, c.rmin, c.cmin, c.dmin, ts.c_str());
  }
  printf("  (top %d cells: %.1f%% of the tube leaves)\n", std::min<int>(top, top_cells.size()),
         100.0 * cum / std::max<int64_t>(1, leaves));
  printf("tube leaves by certified radius r, log2 bins (-99: cap leaves):\n");
  for (auto [b, n] : rbins) printf("  r in [2^%3d, 2^%3d)  %12lld  %5.1f%%\n", b, b + 1, (long long)n, 100.0 * n / leaves);
}

}  // namespace

int main(int argc, char **argv) {
  std::string dir, csv, tubes;
  std::vector<int> charts = {0, 1, 2, 3};
  double view_bin = 0.02;
  int top = 25, every = 1, threads = std::max(1u, std::thread::hardware_concurrency());
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a;
      return argv[++i];
    };
    if (a == "--packs") dir = next();
    else if (a == "--tubes") tubes = next();
    else if (a == "--charts") charts = ParseInts(next());
    else if (a == "--view_bin") view_bin = std::stod(next());
    else if (a == "--top") top = std::stoi(next());
    else if (a == "--csv") csv = next();
    else if (a == "--every") every = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(dir.empty() != tubes.empty()) << "exactly one of --packs DIR, --tubes DIR";
  FILE *out = nullptr;
  if (!tubes.empty()) {
    if (!csv.empty()) {
      out = fopen(csv.c_str(), "w");
      CHECK(out != nullptr) << csv;
      fprintf(out, "table,tag,vx,vy,vz,tri_diam,depth,r,c,delta\n");
    }
    SurveyTubes(tubes, view_bin, top, out, threads);
    if (out != nullptr) fclose(out);
    return 0;
  }
  if (!csv.empty()) {
    out = fopen(csv.c_str(), "w");
    CHECK(out != nullptr) << csv;
    fprintf(out, "chart,code,tag,vx,vy,vz,tri_diam,cx,cy,cz,rx,ry,rz,w\n");
  }

  for (int chart : charts) {
    // The packs of this chart, by code triangle.
    std::vector<std::pair<int, std::string>> files;
    const std::string cdir = dir + "/c" + std::to_string(chart);
    if (!std::filesystem::exists(cdir)) continue;
    for (const auto &e : std::filesystem::directory_iterator(cdir)) {
      const std::string name = e.path().filename().string();
      if (name.size() > 6 && name[0] == 't' && name.ends_with(".pack"))
        files.push_back({std::stoi(name.substr(1, name.size() - 6)), e.path().string()});
    }
    std::sort(files.begin(), files.end());
    // Largest first, for load balance.
    std::vector<int> order(files.size());
    for (int k = 0; k < (int)files.size(); k++) order[k] = k;
    std::sort(order.begin(), order.end(), [&](int a, int b) {
      return std::filesystem::file_size(files[a].second) > std::filesystem::file_size(files[b].second);
    });
    std::vector<Pack> packs(files.size());
    std::atomic<int> nextk{0};
    std::vector<std::thread> pool;
    for (int th = 0; th < std::min<int>(threads, files.size()); th++)
      pool.emplace_back([&]() {
        for (int k; (k = nextk++) < (int)order.size();) {
          Pack &pk = packs[order[k]];
          pk.chart = chart;
          pk.code = files[order[k]].first;
          ReadPack(files[order[k]].second, &pk);
        }
      });
    for (auto &th : pool) th.join();

    int64_t rows = 0, leaves = 0;
    std::map<int, int64_t> by_tag;
    for (const Pack &pk : packs) {
      rows += pk.rows;
      leaves += pk.leaves.size();
      for (auto [tag, n] : pk.by_tag) by_tag[tag] += n;
    }
    printf("\n=== chart %d: %zu packs, %lld rows, %lld leaves\n", chart, packs.size(), (long long)rows,
           (long long)leaves);
    if (rows == 0) continue;
    printf("rows by tag:\n");
    for (auto [tag, n] : by_tag) printf("  %-17s %12lld  %5.1f%%\n", TagName(tag), (long long)n, 100.0 * n / rows);
    printf("leaves by code triangle (top %d):\n", top);
    std::vector<std::pair<int64_t, int>> bycode;
    for (const Pack &pk : packs) bycode.push_back({(int64_t)pk.leaves.size(), pk.code});
    std::sort(bycode.rbegin(), bycode.rend());
    for (int k = 0; k < std::min<int>(top, bycode.size()); k++)
      printf("  t%-4d %12lld  %5.1f%%\n", bycode[k].second, (long long)bycode[k].first,
             100.0 * bycode[k].first / std::max<int64_t>(1, leaves));

    // View cells: cube-map bins of the normalized view direction.
    struct Cell { int64_t n = 0; double wmin = 1e9, wmax = 0, rmin = 1e9, dmin = 1e9; std::array<double, 3> v{}; };
    std::unordered_map<int64_t, Cell> cells;
    std::map<int, int64_t> wbins, rbins;
    for (const Pack &pk : packs) {
      int64_t idx = 0;
      for (const Leaf &l : pk.leaves) {
        const auto v = Centroid(pk.tris[l.tri]);
        const double d = Diameter(pk.tris[l.tri]);
        const double w = CayleyNorm(l);
        const double r = std::max({(double)l.r[0], (double)l.r[1], (double)l.r[2]});
        Cell &cl = cells[ViewCell(v, view_bin)];
        cl.n++;
        cl.wmin = std::min(cl.wmin, w);
        cl.wmax = std::max(cl.wmax, w);
        cl.rmin = std::min(cl.rmin, r);
        cl.dmin = std::min(cl.dmin, d);
        for (int c = 0; c < 3; c++) cl.v[c] += v[c];
        wbins[w > 0 ? (int)std::floor(std::log2(w)) : -99]++;
        rbins[r > 0 ? (int)std::floor(std::log2(r)) : -99]++;
        if (out != nullptr && idx++ % every == 0)
          fprintf(out, "%d,%d,%d,%.6f,%.6f,%.6f,%.3e,%.6e,%.6e,%.6e,%.3e,%.3e,%.3e,%.6e\n", chart, pk.code, l.tag,
                  v[0], v[1], v[2], d, l.c[0], l.c[1], l.c[2], l.r[0], l.r[1], l.r[2], w);
      }
    }
    std::vector<std::pair<int64_t, const Cell *>> top_cells;
    for (const auto &[k, c] : cells) top_cells.push_back({c.n, &c});
    std::sort(top_cells.begin(), top_cells.end(), [](auto &x, auto &y) { return x.first > y.first; });
    printf("densest view cells (%.3f rad; %zu cells with leaves):\n", view_bin, cells.size());
    printf("  %12s %6s  %-28s %-21s %9s %9s\n", "leaves", "%", "view (mean)", "|w| range", "min box", "min tri");
    int64_t cum = 0;
    for (int k = 0; k < std::min<int>(top, top_cells.size()); k++) {
      const Cell &c = *top_cells[k].second;
      cum += c.n;
      const double n = std::sqrt(c.v[0] * c.v[0] + c.v[1] * c.v[1] + c.v[2] * c.v[2]);
      printf("  %12lld %5.1f%%  (%8.5f,%8.5f,%8.5f)  [%8.2e,%8.2e]  %9.2e %9.2e\n", (long long)c.n,
             100.0 * c.n / leaves, c.v[0] / n, c.v[1] / n, c.v[2] / n, c.wmin, c.wmax, c.rmin, c.dmin);
    }
    printf("  (top %d cells: %.1f%% of the leaves)\n", std::min<int>(top, top_cells.size()), 100.0 * cum / leaves);
    printf("leaves by Cayley norm |w| (rotation angle 2 atan|w|), log2 bins:\n");
    for (auto [b, n] : wbins) printf("  |w| in [2^%3d, 2^%3d)  %12lld  %5.1f%%\n", b, b + 1, (long long)n, 100.0 * n / leaves);
    printf("leaves by Cayley box half-width, log2 bins:\n");
    for (auto [b, n] : rbins) printf("  r in [2^%3d, 2^%3d)  %12lld  %5.1f%%\n", b, b + 1, (long long)n, 100.0 * n / leaves);
  }
  if (out != nullptr) fclose(out);
  return 0;
}
