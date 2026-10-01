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
// recorded cone_samples to produce the exact Lean certificate. Certificates
// are moved onto dyadic outer view triangles (Lean regionRelax, tag 11)
// wherever they hold exactly there; --exact_check also confirms the ones
// kept on their exact triangle.
//
// Usage: pack5d.exe --chart C (--all | --t T) [--journals jobs] [--out FILE]
//                   [--trees_dir trees_r1] [--bdd codebdd229.json] [--exact_check]
//                   [--threads 8]

#include <atomic>
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
#include "threadutil.h"
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
  //
  // Certificate leaves are checked over geom5d::OuterDyadicTriangle of their
  // view triangle (Lean Row.regionRelax), which is much cheaper in Lean than
  // the exact triangle. A regionRelax row goes at the top of each maximal
  // subtree that has no view splits and no tube leaves, contains a
  // certificate, and whose certificates all hold exactly over the outer
  // triangle (checked here with exact5d, at about the cost of building them).
  int AddJob(int t, const std::vector<rows5d::Record> &leaves, int first_id) {
    const solve5d::Node root = solve5d::RootNode(atlas_, {.t = t, .chart = chart_});
    auto built = rows5d::BuildTree(leaves);
    CHECK(std::holds_alternative<rows5d::Tree>(built))
        << "job t=" << t << " chart=" << chart_ << ": " << std::get<std::string>(built);
    const rows5d::Tree &tree = std::get<rows5d::Tree>(built);
    std::unordered_map<std::string, const rows5d::Split *> split_at;
    for (const auto &s : tree.splits) split_at[s.path] = &s;
    std::unordered_map<std::string, const rows5d::Leaf *> leaf_at;
    for (const auto &r : tree.leaves) leaf_at[r.path] = &r.leaf;

    // Nodes in breadth-first order, with their parents, boxes and views.
    struct N {
      std::string path;
      int parent = -1;
      const rows5d::Split *split = nullptr;
      const rows5d::Leaf *leaf = nullptr;
      std::vector<int> kids;
      int view = 0;  // index into views
      geom5d::BoxQ box;
    };
    struct View {
      exact5d::TriangleQ exact, outer;
    };
    std::vector<N> nodes;
    std::vector<View> views = {{root.tri, geom5d::OuterDyadicTriangle(root.tri)}};
    nodes.push_back({.path = "", .view = 0, .box = root.box});
    for (size_t q = 0; q < nodes.size(); q++) {
      auto it = split_at.find(nodes[q].path);
      if (it == split_at.end()) {
        nodes[q].leaf = leaf_at.at(nodes[q].path);
        continue;
      }
      const rows5d::Split &s = *it->second;
      nodes[q].split = &s;
      const auto kids = ChildPaths(s);
      for (int k = 0; k < (int)kids.size(); k++) {
        N c{.path = kids[k], .parent = (int)q};
        if (s.view) {
          const exact5d::TriangleQ tri = geom5d::SplitTriangle(views[nodes[q].view].exact, k);
          c.view = views.size();
          views.push_back({tri, geom5d::OuterDyadicTriangle(tri)});
          c.box = nodes[q].box;
        } else {
          c.view = nodes[q].view;
          c.box = k == 0 ? geom5d::LowerHalf(nodes[q].box, s.axis)
                         : geom5d::UpperHalf(nodes[q].box, s.axis);
        }
        nodes[q].kids.push_back(nodes.size());
        nodes.push_back(std::move(c));
      }
    }

    // Certificate leaves, built over the outer triangle (and checked), or
    // over the exact one if that fails. Grouped by view to share the pool.
    struct Built {
      bool outer_ok = false;
      std::string body;  // the row after its triangle index
    };
    std::vector<Built> built_rows(nodes.size());
    std::map<int, std::vector<int>> cert_by_view;
    for (int n = 0; n < (int)nodes.size(); n++) {
      if (nodes[n].leaf != nullptr && IsCertificate(*nodes[n].leaf)) {
        cert_by_view[nodes[n].view].push_back(n);
      }
    }
    std::vector<const std::vector<int> *> groups;
    for (const auto &[v, g] : cert_by_view) groups.push_back(&g);
    std::atomic<int64_t> relax_failures = 0;
    ParallelComp(groups.size(), [&](int64_t gi) {
      const std::vector<int> &group = *groups[gi];
      const View &view = views[nodes[group[0]].view];
      std::map<int, contacts5d::ContactPool> pools;  // by cone_samples
      auto pool_for = [&](int cone_samples) -> const contacts5d::ContactPool & {
        auto it = pools.find(cone_samples);
        if (it == pools.end()) {
          contacts5d::PoolParams params;
          params.cone_samples = cone_samples;
          it = pools.emplace(cone_samples,
                             contacts5d::BuildContactPool(geom5d::ToDouble(view.exact), params))
                   .first;
        }
        return it->second;
      };
      for (int n : group) {
        Built &b = built_rows[n];
        bool ok = false;
        b.body = CertBody(nodes[n].path, *nodes[n].leaf, view.outer, nodes[n].box, pool_for,
                          /*check=*/true, &ok);
        if (ok) {
          b.outer_ok = true;
          continue;
        }
        relax_failures++;
        b.body = CertBody(nodes[n].path, *nodes[n].leaf, view.exact, nodes[n].box, pool_for,
                          exact_check_, &ok);
        CHECK(ok) << "certificate fails exactly at " << nodes[n].path;
      }
    }, threads_);
    if (relax_failures > 0) {
      printf("t=%d: %lld certificates fail over the outer triangle; kept exact\n", t,
             (long long)relax_failures.load());
    }

    // Relaxable subtrees, bottom-up (children come after parents).
    std::vector<char> relaxable(nodes.size(), 0), has_cert(nodes.size(), 0);
    for (int n = (int)nodes.size() - 1; n >= 0; n--) {
      const N &node = nodes[n];
      if (node.split != nullptr) {
        bool r = !node.split->view, c = false;
        for (int k : node.kids) r = r && relaxable[k], c = c || has_cert[k];
        relaxable[n] = r;
        has_cert[n] = c;
      } else if (IsCertificate(*node.leaf)) {
        relaxable[n] = built_rows[n].outer_ok;
        has_cert[n] = 1;
      } else {
        // Prune rows do not depend on their region.
        relaxable[n] = std::holds_alternative<rows5d::RadiusPruneLeaf>(*node.leaf) ||
                       std::holds_alternative<rows5d::FundamentalPruneLeaf>(*node.leaf);
      }
    }
    auto relax_point = [&](int n) {
      return relaxable[n] && has_cert[n] && (n == 0 || !relaxable[nodes[n].parent]);
    };

    // Ids: breadth-first, with a relax point's regionRelax row just before
    // its content row.
    std::vector<int> id_of(nodes.size()), content_id(nodes.size());
    std::vector<char> relaxed(nodes.size(), 0);  // region uses the outer triangle
    int next = first_id;
    for (int n = 0; n < (int)nodes.size(); n++) {
      id_of[n] = next++;
      content_id[n] = relax_point(n) ? next++ : id_of[n];
      relaxed[n] = relax_point(n) || (n > 0 && relaxed[nodes[n].parent]);
    }
    for (int n = 0; n < (int)nodes.size(); n++) {
      const N &node = nodes[n];
      const View &view = views[node.view];
      const int iv = Interval(node.box);
      if (relax_point(n)) {
        rows_.push_back(std::format(",11,{},{},{},0,{},{}", id_of[n], iv, content_id[n],
                                    Triangle(view.exact), Triangle(view.outer)));
        relax_rows_++;
      }
      const int id = content_id[n];
      const int region = Triangle(relaxed[n] ? view.outer : view.exact);
      std::string row;
      if (node.split != nullptr) {
        const std::vector<int> &k = node.kids;
        if (node.split->view) {
          row = std::format(",2,{},{},{},{},{},{},0,{}", id, iv, id_of[k[0]], id_of[k[1]],
                            id_of[k[2]], id_of[k[3]], region);
        } else {
          row = std::format(",1,{},{},{},{},{},0,{}", id, iv, id_of[k[0]], id_of[k[1]],
                            node.split->axis + 2, region);
        }
      } else if (IsCertificate(*node.leaf)) {
        // Each certificate is used over the triangle it was built for.
        CHECK(relaxed[n] == built_rows[n].outer_ok) << node.path;
        const char *tag = std::holds_alternative<rows5d::CertLeaf>(*node.leaf) ? "4" : "9";
        row = std::format(",{},{},{},0,{}", tag, id, iv, region) + built_rows[n].body;
      } else {
        row = OtherLeafRow(t, node.path, *node.leaf, id, iv, region);
      }
      rows_.push_back(row);
    }
    return first_id;
  }

  int64_t RelaxRows() const { return relax_rows_; }
  void SetThreads(int threads) { threads_ = threads; }

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

  static bool IsCertificate(const rows5d::Leaf &leaf) {
    return std::holds_alternative<rows5d::CertLeaf>(leaf) ||
           std::holds_alternative<rows5d::MixedLeaf>(leaf);
  }

  // The part of a certificate leaf's row after its triangle index, built
  // over `tri`. With `check`, *ok says whether it holds exactly (exact5d);
  // otherwise *ok is true.
  template <class PoolFor>
  std::string CertBody(const std::string &path, const rows5d::Leaf &leaf,
                       const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                       const PoolFor &pool_for, bool check, bool *ok) const {
    if (const auto *l = std::get_if<rows5d::CertLeaf>(&leaf)) {
      const auto &pool = pool_for(l->cone_samples);
      CHECK(l->triple < (int)pool.triples.size()) << "stale triple index at " << path;
      const cert5d::Single s{.triple = l->triple, .inner = l->inner};
      const exact5d::GlobalBox g = cert5d::ExactGlobalBox(pool, s, tri, box, chart_);
      *ok = !check || exact5d::Valid(g);
      const auto &c = g.certificate;
      std::string r;
      for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                              &c.mix, &c.index, &c.nonzero_witness}) {
        for (int m = 0; m < 3; m++) r += std::format(",{}", (*arr)[m]);
      }
      r += "," + Zigzag(c.B);
      for (int m = 0; m < 3; m++) r += std::format(",{}", g.inner_index[m]);
      r += "," + Zigzag(g.ball_multiplier);
      return r;
    }
    const auto &l = std::get<rows5d::MixedLeaf>(leaf);
    const auto &pool = pool_for(l.cone_samples);
    std::vector<int> triples;
    std::vector<std::array<int, 3>> inner;
    std::vector<BigRat> weights;
    for (const auto &c : l.components) {
      CHECK(c.triple < (int)pool.triples.size()) << "stale triple index at " << path;
      triples.push_back(c.triple);
      inner.push_back(c.inner);
      weights.push_back(c.weight);
    }
    const exact5d::MixedBox m =
        cert5d::ExactMixedBox(pool, triples, inner, weights, tri, box, chart_);
    *ok = !check || exact5d::Valid(m);
    std::string r;
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
  }

  // Rows of the other leaves (tube, radius prune, fundamental prune).
  std::string OtherLeafRow(int t, const std::string &path, const rows5d::Leaf &leaf, int id,
                           int iv, int tri_id) const {
    return std::visit(
        [&](const auto &l) -> std::string {
          using T = std::decay_t<decltype(l)>;
          if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) {
            const std::string view = rows5d::ViewPath(path);
            std::string r =
                std::format(",6,{},{},0,{},{},{}", id, iv, Zigzag(l.r), t, view.size());
            for (char c : view) r += std::format(",{}", c - '0');
            r += std::format(",0,{}", tri_id);
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) {
            return std::format(",7,{},{},0,{}", id, iv, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) {
            return std::format(",8,{},{},{},0,{}", id, iv, l.direction > 0 ? 1 : 0, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::DeferredLeaf>) {
            LOG(FATAL) << "deferred leaf " << path << " (job t=" << t
                       << "): finish the search before packing";
            return "";
          } else {
            LOG(FATAL) << "certificate leaf " << path << " has no built row";
            return "";
          }
        },
        leaf);
  }

  const tubeatlas5d::TubeAtlas &atlas_;
  int chart_;
  bool exact_check_;
  int threads_ = 8;
  int64_t relax_rows_ = 0;
  std::vector<std::string> rows_;
  std::vector<std::string> intervals_, triangles_;
  std::unordered_map<std::string, int> interval_ids_, triangle_ids_;
};

}  // namespace

int main(int argc, char **argv) {
  int chart = -1, single = -1, threads = 8;
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
    else if (a == "--threads") threads = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(chart >= 0 && chart <= 2) << "--chart 0..2";
  CHECK(all != (single >= 0)) << "exactly one of --all, --t";
  if (out.empty()) out = all ? std::format("chart{}.pack", chart) : std::format("chart{}.t{}.pack", chart, single);

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  Packer packer(atlas, chart, exact_check);
  packer.SetThreads(threads);
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
  printf("wrote %s: %zu rows (%lld regionRelax)\n", out.c_str(), packer.NumRows(),
         (long long)packer.RelaxRows());
  return 0;
}
