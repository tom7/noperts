// Packs 5D search journals into a Lean global table for one chart
// (PackedSolutionTree.decodeTable: count, intervals, triangles, rows).
//
// Full table (--all): row 0 is codeRoot over every code triangle (tag 10),
// with each job's tree below it; every job must be complete (no deferred
// leaves). Single job (--t T): row 0 is the job's root node; such a table is
// not a Table.Valid chart table, but each row can be checked with Lean's
// row checker (check_global_rows in Noperthedron) during development.
//
// Rows follow the tree in breadth-first order (Lean needs children after
// their parents). Certificate leaves rebuild their contact pool from the
// recorded cone_samples to produce the exact Lean certificate; --exact_check
// also confirms each with exact5d before writing.
//
// Usage: pack5d.exe --chart C (--all | --t T) [--journals jobs] [--out FILE]
//                   [--trees_dir trees_r1] [--bdd codebdd229.json] [--exact_check]

#include <cstdio>
#include <deque>
#include <format>
#include <fstream>
#include <map>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "cert5d.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"

namespace {

std::string Zigzag(const BigRat &r) {
  const BigInt num = r.Numerator();
  const BigInt den = r.Denominator();
  const BigInt zz = (num >= BigInt(0)) ? (num * 2) : ((BigInt(0) - num) * 2 - 1);
  return zz.ToString() + "," + den.ToString();
}

class Packer {
 public:
  Packer(const tubeatlas5d::TubeAtlas &atlas, int chart, bool exact_check)
      : atlas_(atlas), chart_(chart), exact_check_(exact_check) {}

  int Interval(const geom5d::BoxQ &b) {
    std::string key;
    for (int a = 0; a < 3; a++) key += b.lo[a].ToString() + " " + b.hi[a].ToString() + " ";
    auto [it, fresh] = interval_ids_.emplace(key, (int)intervals_.size());
    if (fresh) {
      std::string s;
      for (int a = 0; a < 3; a++) s += "," + Zigzag((b.lo[a] + b.hi[a]) / BigRat(2));
      for (int a = 0; a < 3; a++) s += "," + Zigzag((b.hi[a] - b.lo[a]) / BigRat(2));
      intervals_.push_back(s);
    }
    return it->second;
  }

  int Triangle(const exact5d::TriangleQ &t) {
    std::string s;
    for (int i = 0; i < 3; i++) for (int c = 0; c < 3; c++) s += "," + Zigzag(t[i][c]);
    auto [it, fresh] = triangle_ids_.emplace(s, (int)triangles_.size());
    if (fresh) triangles_.push_back(s);
    return it->second;
  }

  // Appends the rows of job t's tree; returns the id of its root row.
  int AddJob(int t, const std::vector<rows5d::Record> &leaves, int first_id) {
    const solve5d::Node root = solve5d::RootNode(atlas_, {.t = t, .chart = chart_});
    auto built = rows5d::BuildTree(leaves);
    CHECK(std::holds_alternative<rows5d::Tree>(built))
        << "job t=" << t << " chart=" << chart_ << ": " << std::get<std::string>(built);
    const rows5d::Tree &tree = std::get<rows5d::Tree>(built);
    std::map<std::string, const rows5d::Split *> split_at;
    for (const auto &s : tree.splits) split_at[s.path] = &s;
    std::map<std::string, const rows5d::Leaf *> leaf_at;
    for (const auto &r : tree.leaves) leaf_at[r.path] = &r.leaf;

    // Breadth-first ids.
    std::vector<std::string> order = {""};
    std::unordered_map<std::string, int> id_of = {{"", first_id}};
    for (size_t q = 0; q < order.size(); q++) {
      auto it = split_at.find(order[q]);
      if (it == split_at.end()) continue;
      for (const std::string &c : ChildPaths(*it->second)) {
        id_of[c] = first_id + (int)order.size();
        order.push_back(c);
      }
    }
    for (const std::string &p : order) {
      const exact5d::TriangleQ tri = rows5d::NodeTriangle(root.tri, p);
      const geom5d::BoxQ box = rows5d::NodeBox(root.box, p);
      const int iv = Interval(box);
      const int id = id_of[p];
      std::string row;
      if (auto it = split_at.find(p); it != split_at.end()) {
        const rows5d::Split &s = *it->second;
        const auto kids = ChildPaths(s);
        if (s.view) {
          row = std::format(",2,{},{},{},{},{},{},0,{}", id, iv, id_of[kids[0]], id_of[kids[1]],
                            id_of[kids[2]], id_of[kids[3]], Triangle(tri));
        } else {
          row = std::format(",1,{},{},{},{},{},0,{}", id, iv, id_of[kids[0]], id_of[kids[1]],
                            s.axis + 2, Triangle(tri));
        }
      } else {
        row = LeafRow(t, p, *leaf_at.at(p), id, iv, tri, box);
      }
      rows_.push_back(row);
    }
    return first_id;
  }

  void AddCodeRoot(const std::vector<int> &children) {
    std::string row = std::format(",10,0,{},{}", Interval(geom5d::RootBox(chart_)), children.size());
    for (int c : children) row += std::format(",{}", c);
    rows_.insert(rows_.begin(), row);
  }

  void Write(const std::string &path) const {
    std::ofstream f(path, std::ios::binary);
    CHECK(f.good()) << path;
    f << rows_.size() << "," << intervals_.size();
    for (const auto &s : intervals_) f << s;
    f << "," << triangles_.size();
    for (const auto &s : triangles_) f << s;
    for (const auto &r : rows_) f << r;
    f << "\n";
  }

  size_t NumRows() const { return rows_.size(); }

 private:
  static std::vector<std::string> ChildPaths(const rows5d::Split &s) {
    if (s.view) return {s.path + '0', s.path + '1', s.path + '2', s.path + '3'};
    return {s.path + rows5d::BoxStep(s.axis, false), s.path + rows5d::BoxStep(s.axis, true)};
  }

  std::string LeafRow(int t, const std::string &path, const rows5d::Leaf &leaf, int id, int iv,
                      const exact5d::TriangleQ &tri, const geom5d::BoxQ &box) {
    const int tri_id = Triangle(tri);
    return std::visit(
        [&](const auto &l) -> std::string {
          using T = std::decay_t<decltype(l)>;
          if constexpr (std::is_same_v<T, rows5d::CertLeaf>) {
            contacts5d::PoolParams params;
            params.cone_samples = l.cone_samples;
            const auto pool = contacts5d::BuildContactPool(geom5d::ToDouble(tri), params);
            CHECK(l.triple < (int)pool.triples.size()) << "stale triple index at " << path;
            const cert5d::Single s{.triple = l.triple, .inner = l.inner};
            const exact5d::GlobalBox g = cert5d::ExactGlobalBox(pool, s, tri, box, chart_);
            if (exact_check_) CHECK(exact5d::Valid(g)) << "certificate fails exactly at " << path;
            const auto &c = g.certificate;
            std::string r = std::format(",4,{},{},0,{}", id, iv, tri_id);
            for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                                    &c.mix, &c.index, &c.nonzero_witness}) {
              for (int m = 0; m < 3; m++) r += std::format(",{}", (*arr)[m]);
            }
            r += "," + Zigzag(c.B);
            for (int m = 0; m < 3; m++) r += std::format(",{}", g.inner_index[m]);
            r += "," + Zigzag(g.ball_multiplier);
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::MixedLeaf>) {
            contacts5d::PoolParams params;
            params.cone_samples = l.cone_samples;
            const auto pool = contacts5d::BuildContactPool(geom5d::ToDouble(tri), params);
            std::vector<int> triples;
            std::vector<std::array<int, 3>> inner;
            std::vector<BigRat> weights;
            for (const auto &c : l.components) {
              CHECK(c.triple < (int)pool.triples.size()) << "stale triple index at " << path;
              triples.push_back(c.triple);
              inner.push_back(c.inner);
              weights.push_back(c.weight);
            }
            const exact5d::MixedBox m = cert5d::ExactMixedBox(pool, triples, inner, weights, tri, box, chart_);
            if (exact_check_) CHECK(exact5d::Valid(m)) << "mixture fails exactly at " << path;
            std::string r = std::format(",9,{},{},0,{}", id, iv, tri_id);
            for (int k = 0; k < 4; k++) r += "," + Zigzag(m.weight[k]);
            for (int k = 0; k < 4; k++) {
              const auto &c = m.component[k].certificate;
              for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                                      &c.mix, &c.index, &c.nonzero_witness}) {
                for (int i = 0; i < 3; i++) r += std::format(",{}", (*arr)[i]);
              }
              r += "," + Zigzag(c.B);
              for (int i = 0; i < 3; i++) r += std::format(",{}", m.component[k].inner_index[i]);
              r += "," + Zigzag(m.component[k].ball_multiplier);
            }
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) {
            const std::string view = rows5d::ViewPath(path);
            std::string r = std::format(",6,{},{},0,{},{},{}", id, iv, Zigzag(l.r), t, view.size());
            for (char c : view) r += std::format(",{}", c - '0');
            r += std::format(",0,{}", tri_id);
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) {
            return std::format(",7,{},{},0,{}", id, iv, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) {
            return std::format(",8,{},{},{},0,{}", id, iv, l.direction > 0 ? 1 : 0, tri_id);
          } else {
            LOG(FATAL) << "deferred leaf " << path << " (job t=" << t
                       << "): finish the search before packing";
            return "";
          }
        },
        leaf);
  }

  const tubeatlas5d::TubeAtlas &atlas_;
  int chart_;
  bool exact_check_;
  std::vector<std::string> rows_;
  std::vector<std::string> intervals_, triangles_;
  std::unordered_map<std::string, int> interval_ids_, triangle_ids_;
};

}  // namespace

int main(int argc, char **argv) {
  int chart = -1, single = -1;
  bool all = false, exact_check = false;
  std::string journals = "jobs", out, trees_dir = "trees_r1", bdd = "codebdd229.json";
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--chart") chart = std::stoi(next());
    else if (a == "--t") single = std::stoi(next());
    else if (a == "--all") all = true;
    else if (a == "--journals") journals = next();
    else if (a == "--out") out = next();
    else if (a == "--trees_dir") trees_dir = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--exact_check") exact_check = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(chart >= 0 && chart <= 2) << "--chart 0..2";
  CHECK(all != (single >= 0)) << "exactly one of --all, --t";
  if (out.empty()) out = all ? std::format("chart{}.pack", chart) : std::format("chart{}.t{}.pack", chart, single);

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  Packer packer(atlas, chart, exact_check);
  auto leaves_of = [&](int t) {
    const auto j = rows5d::ReadJournal(std::format("{}/c{}/t{}.journal", journals, chart, t));
    CHECK(!j.leaves.empty()) << "no journal for t=" << t << " chart=" << chart;
    return j.leaves;
  };
  if (all) {
    std::vector<int> roots;
    int next_id = 1;  // row 0 is the code root
    for (int t = 0; t < atlas.NumTriangles(); t++) {
      const size_t before = packer.NumRows();
      roots.push_back(packer.AddJob(t, leaves_of(t), next_id));
      next_id += packer.NumRows() - before;
    }
    packer.AddCodeRoot(roots);
  } else {
    packer.AddJob(single, leaves_of(single), 0);
  }
  packer.Write(out);
  printf("wrote %s: %zu rows\n", out.c_str(), packer.NumRows());
  return 0;
}
