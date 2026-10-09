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
// Per code (--per_code DIR): one pack per job, DIR/c<C>/t<T>.pack, each like
// a --t pack (row 0 is the job's root). Lean's decodeCodeTables concatenates
// them behind a codeRoot row into the chart table, so a re-searched code
// only needs its own pack (and check) redone: packs newer than their journal
// are skipped unless --force.
//
// Usage: pack5d.exe --chart C (--all | --t T | --per_code DIR) [--journals jobs]
//                   [--out FILE] [--trees_dir trees_r2] [--bdd codebdd.json]
//                   [--exact_check] [--threads 8] [--force]

#include <atomic>
#include <algorithm>
#include <mutex>
#include <filesystem>
#include <chrono>
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

// Current and peak resident memory, from /proc/self/status.
std::string MemoryString() {
  std::ifstream f("/proc/self/status");
  std::string line, rss = "?", hwm = "?";
  while (std::getline(f, line)) {
    auto gb = [&](std::string *out) {
      *out = std::format("{:.1f}G", std::stod(line.substr(line.find(':') + 1)) / (1 << 20));
    };
    if (line.rfind("VmRSS:", 0) == 0) gb(&rss);
    if (line.rfind("VmHWM:", 0) == 0) gb(&hwm);
  }
  return std::format("rss {}, peak {}", rss, hwm);
}

std::string Zigzag(const BigRat &r) {
  const BigInt num = r.Numerator();
  const BigInt den = r.Denominator();
  const BigInt zz = (num >= BigInt(0)) ? (num * 2) : ((BigInt(0) - num) * 2 - 1);
  return zz.ToString() + "," + den.ToString();
}

// Tie nodes (dh_tie_lean.py's nodes.txt: "<normal> <t> <path> <index>"): a tie
// leaf row cites the deepest listed node on its view path (Lean Row.tieLeaf).
std::map<std::string, int> g_tie_nodes;
void LoadTieNodes(const std::string &file) {
  std::ifstream in(file);
  CHECK(in.good()) << file;
  int n, t, k;
  std::string path;
  while (in >> n >> t >> path >> k) g_tie_nodes[std::format("{} {} {}", n, t, path == "." ? "" : path)] = k;
}
int TieNode(int n, int t, const std::string &view) {
  for (int len = (int)view.size(); len >= 0; len--) {
    const auto it = g_tie_nodes.find(std::format("{} {} {}", n, t, view.substr(0, len)));
    if (it != g_tie_nodes.end()) return it->second;
  }
  LOG(FATAL) << "no tie node for normal " << n << " t " << t << " view " << view << " (--tie_nodes)";
  return -1;
}

class Packer {
 public:
  Packer(const tubeatlas5d::TubeAtlas &atlas, int chart, bool exact_check)
      : atlas_(atlas), chart_(chart), exact_check_(exact_check) {}

  // The pack encoding of an interval or a triangle (also its dedup key).
  static std::string IntervalString(const geom5d::BoxQ &b) {
    std::string s;
    for (int a = 0; a < 3; a++) s += "," + Zigzag((b.lo[a] + b.hi[a]) / BigRat(2));
    for (int a = 0; a < 3; a++) s += "," + Zigzag((b.hi[a] - b.lo[a]) / BigRat(2));
    return s;
  }
  static std::string TriangleString(const exact5d::TriangleQ &t) {
    std::string s;
    for (int i = 0; i < 3; i++) for (int c = 0; c < 3; c++) s += "," + Zigzag(t[i][c]);
    return s;
  }

  // Table indices, numbered in order of first use.
  int IntervalId(const std::string &s) {
    auto [it, fresh] = interval_ids_.emplace(s, (int)intervals_.size());
    if (fresh) intervals_.push_back(s);
    return it->second;
  }
  int TriangleId(const std::string &s) {
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
  //
  // View triangles and boxes are interned: the search often splits the box
  // before the view, so one view triangle recurs under many boxes and one
  // box under many views (chart 0, t=102: 16.4M nodes, 2.35M view nodes,
  // 118,800 distinct triangles, 226,641 distinct boxes). Each distinct one
  // is computed and encoded once, and certificates over the same triangle
  // share contact pools.
  //
  // The exact arithmetic (view triangles with ~1000-bit corners, their outer
  // triangles, boxes, encodings, certificates) runs in parallel; only the
  // table numbering is sequential, in row order.
  int AddJob(int t, const rows5d::Tree &tree, int first_id) {
    const solve5d::Node root = solve5d::RootNode(atlas_, {.t = t, .chart = chart_});
    // The view triangles' projective root (Lean's region root), per job.
    const int view_root = atlas_.Root(t);

    // Distinct view triangles and boxes, each derived from its parent.
    struct Tri {
      int parent = -1, child = 0, depth = 0;
      exact5d::TriangleQ exact, outer;
      std::string exact_str, outer_str;
    };
    struct Box {
      int parent = -1, axis = 0, eighths = 4, depth = 0;
      bool upper = false;
      geom5d::BoxQ box;
      std::string str;
    };
    std::vector<Tri> tris(1);
    std::vector<Box> boxes(1);
    tris[0].exact = root.tri;
    boxes[0].box = root.box;
    std::unordered_map<int64_t, int> tri_key, box_key;
    auto intern_tri = [&](int parent, int child) {
      auto [it, fresh] = tri_key.emplace((int64_t)parent * 4 + child, (int)tris.size());
      if (fresh) tris.push_back({.parent = parent, .child = child, .depth = tris[parent].depth + 1});
      return it->second;
    };
    auto intern_box = [&](int parent, int axis, int eighths, bool upper) {
      const int64_t key = (int64_t)parent * 64 + axis * 16 + eighths * 2 + (upper ? 1 : 0);
      auto [it, fresh] = box_key.emplace(key, (int)boxes.size());
      if (fresh) {
        boxes.push_back({.parent = parent, .axis = axis, .eighths = eighths,
                         .depth = boxes[parent].depth + 1, .upper = upper});
      }
      return it->second;
    };

    // Nodes in breadth-first order (so a node's children are contiguous and
    // come after it). A node's path is its split's or leaf record's.
    struct N {
      const rows5d::Split *split = nullptr;
      const rows5d::Record *leaf = nullptr;
      int parent = -1;
      int first_kid = 0;
      int tri = 0, box = 0;
      uint8_t child = 0, num_kids = 0;
      const std::string &Path() const { return split != nullptr ? split->path : leaf->path; }
    };
    std::vector<N> nodes(1);
    {
      std::unordered_map<std::string_view, const rows5d::Split *> split_at;
      split_at.reserve(tree.splits.size());
      for (const auto &s : tree.splits) split_at[s.path] = &s;
      std::unordered_map<std::string_view, const rows5d::Record *> leaf_at;
      leaf_at.reserve(tree.leaves.size());
      for (const auto &r : tree.leaves) leaf_at[r.path] = &r;
      auto resolve = [&](std::string_view path, N *n) {
        if (auto it = split_at.find(path); it != split_at.end()) {
          n->split = it->second;
        } else {
          auto jt = leaf_at.find(path);
          CHECK(jt != leaf_at.end()) << "no node at " << path << " (job t=" << t << ")";
          n->leaf = jt->second;
        }
      };
      resolve("", &nodes[0]);
      for (size_t q = 0; q < nodes.size(); q++) {
        if (nodes[q].split == nullptr) continue;
        const rows5d::Split &s = *nodes[q].split;
        const int tri = nodes[q].tri, box = nodes[q].box;
        const auto kids = rows5d::ChildPaths(s);
        nodes[q].first_kid = nodes.size();
        nodes[q].num_kids = kids.size();
        for (int k = 0; k < (int)kids.size(); k++) {
          N c{.parent = (int)q, .child = (uint8_t)k};
          if (s.view) {
            c.tri = intern_tri(tri, k);
            c.box = box;
          } else {
            c.tri = tri;
            c.box = intern_box(box, s.axis, s.eighths, k == 1);
          }
          resolve(kids[k], &c);
          nodes.push_back(c);
        }
      }
    }
    std::unordered_map<int64_t, int>().swap(tri_key);
    std::unordered_map<int64_t, int>().swap(box_key);

    const auto job_start = std::chrono::steady_clock::now();
    auto phase = [&](const std::string &what) {
      if (nodes.size() < 1000000) return;
      printf("  t=%d: %s (%.0fs; %s)\n", t, what.c_str(),
             std::chrono::duration<double>(std::chrono::steady_clock::now() - job_start).count(),
             MemoryString().c_str());
      fflush(stdout);
    };
    phase(std::format("{} nodes, {} distinct view triangles, {} distinct boxes", nodes.size(),
                      tris.size(), boxes.size()));

    // Calls f(i) for every i < n, in parallel, after every i' of smaller depth.
    auto by_depth = [&](size_t n, auto depth_of, const auto &f) {
      std::vector<std::vector<int>> levels;
      for (size_t i = 0; i < n; i++) {
        const int d = depth_of(i);
        if (d >= (int)levels.size()) levels.resize(d + 1);
        levels[d].push_back(i);
      }
      for (const auto &level : levels) {
        ParallelComp(level.size(), [&](int64_t k) { f(level[k]); }, threads_);
      }
    };
    by_depth(boxes.size(), [&](size_t b) { return boxes[b].depth; }, [&](int b) {
      Box &box = boxes[b];
      if (box.parent >= 0) {
        const geom5d::BoxQ &p = boxes[box.parent].box;
        if (box.eighths == 4) {
          box.box = box.upper ? geom5d::UpperHalf(p, box.axis) : geom5d::LowerHalf(p, box.axis);
        } else {
          box.box = box.upper ? geom5d::UpperAt(p, box.axis, box.eighths)
                              : geom5d::LowerAt(p, box.axis, box.eighths);
        }
      }
      box.str = IntervalString(box.box);
    });
    by_depth(tris.size(), [&](size_t v) { return tris[v].depth; }, [&](int v) {
      Tri &tri = tris[v];
      if (tri.parent >= 0) tri.exact = geom5d::SplitTriangle(tris[tri.parent].exact, tri.child);
      tri.outer = geom5d::OuterDyadicTriangle(tri.exact);
      tri.exact_str = TriangleString(tri.exact);
      tri.outer_str = TriangleString(tri.outer);
    });
    phase("boxes and view triangles done");

    // Certificate leaves, built over the outer triangle (and checked), or
    // over the exact one if that fails. Grouped by triangle to share the
    // contact pool, in chunks for load balance. Each chunk's row bodies (the
    // row after its triangle index) go into one buffer.
    struct BodyRef {
      int chunk = -1;
      uint32_t offset = 0, length = 0;
    };
    std::vector<BodyRef> body_ref(nodes.size());
    std::vector<char> outer_ok(nodes.size(), 0);
    std::vector<std::string> body_buf;
    {
      std::vector<std::vector<int>> by_tri(tris.size());
      for (int n = 0; n < (int)nodes.size(); n++) {
        if (nodes[n].leaf != nullptr && IsCertificate(nodes[n].leaf->leaf)) {
          by_tri[nodes[n].tri].push_back(n);
        }
      }
      struct Chunk {
        int tri;
        size_t lo, hi;  // into by_tri[tri]
      };
      constexpr size_t kChunk = 4096;
      std::vector<Chunk> chunks;
      for (int v = 0; v < (int)tris.size(); v++) {
        for (size_t lo = 0; lo < by_tri[v].size(); lo += kChunk) {
          chunks.push_back({v, lo, std::min(by_tri[v].size(), lo + kChunk)});
        }
      }
      body_buf.resize(chunks.size());
      std::atomic<int64_t> relax_failures = 0;
      ParallelComp(chunks.size(), [&](int64_t ci) {
        const Chunk &chunk = chunks[ci];
        const Tri &tri = tris[chunk.tri];
        std::map<int, contacts5d::ContactPool> pools;  // by cone_samples
        auto pool_for = [&](int cone_samples) -> const contacts5d::ContactPool & {
          auto it = pools.find(cone_samples);
          if (it == pools.end()) {
            contacts5d::PoolParams params;
            params.cone_samples = cone_samples;
            it = pools.emplace(cone_samples,
                               contacts5d::BuildContactPool(geom5d::ToDouble(tri.exact), params))
                     .first;
          }
          return it->second;
        };
        std::string &buf = body_buf[ci];
        for (size_t i = chunk.lo; i < chunk.hi; i++) {
          const int n = by_tri[chunk.tri][i];
          const N &node = nodes[n];
          const geom5d::BoxQ &box = boxes[node.box].box;
          bool ok = false;
          std::string body = CertBody(node.Path(), node.leaf->leaf, tri.outer, view_root, box,
                                      pool_for, /*check=*/true, &ok);
          if (ok) {
            outer_ok[n] = 1;
          } else {
            relax_failures++;
            body = CertBody(node.Path(), node.leaf->leaf, tri.exact, view_root, box, pool_for,
                            exact_check_, &ok);
            CHECK(ok) << "certificate fails exactly at " << node.Path();
          }
          body_ref[n] = {(int)ci, (uint32_t)buf.size(), (uint32_t)body.size()};
          buf += body;
        }
      }, threads_);
      if (relax_failures > 0) {
        printf("t=%d: %lld certificates fail over the outer triangle; kept exact\n", t,
               (long long)relax_failures.load());
      }
    }
    phase("certificates built");

    // Relaxable subtrees, bottom-up (children come after parents).
    std::vector<char> relaxable(nodes.size(), 0), has_cert(nodes.size(), 0);
    for (int n = (int)nodes.size() - 1; n >= 0; n--) {
      const N &node = nodes[n];
      if (node.split != nullptr) {
        bool r = !node.split->view, c = false;
        for (int k = node.first_kid; k < node.first_kid + node.num_kids; k++) {
          r = r && relaxable[k];
          c = c || has_cert[k];
        }
        relaxable[n] = r;
        has_cert[n] = c;
      } else if (IsCertificate(node.leaf->leaf)) {
        relaxable[n] = outer_ok[n];
        has_cert[n] = 1;
      } else {
        // Prune rows do not depend on their region.
        relaxable[n] = std::holds_alternative<rows5d::RadiusPruneLeaf>(node.leaf->leaf) ||
                       std::holds_alternative<rows5d::FundamentalPruneLeaf>(node.leaf->leaf) ||
                       std::holds_alternative<rows5d::IcoPruneLeaf>(node.leaf->leaf);
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
    // Table numbers in row order (first use), each distinct box and
    // triangle looked up once.
    std::vector<int> box_iv(boxes.size(), -1), tri_exact(tris.size(), -1),
        tri_outer(tris.size(), -1);
    auto iv_id = [&](int b) {
      if (box_iv[b] < 0) box_iv[b] = IntervalId(boxes[b].str);
      return box_iv[b];
    };
    auto exact_id = [&](int v) {
      if (tri_exact[v] < 0) tri_exact[v] = TriangleId(tris[v].exact_str);
      return tri_exact[v];
    };
    auto outer_id = [&](int v) {
      if (tri_outer[v] < 0) tri_outer[v] = TriangleId(tris[v].outer_str);
      return tri_outer[v];
    };
    std::vector<int> iv_of(nodes.size()), tri_of(nodes.size());
    for (int n = 0; n < (int)nodes.size(); n++) {
      const int v = nodes[n].tri;
      iv_of[n] = iv_id(nodes[n].box);
      if (relax_point(n)) {
        exact_id(v);
        outer_id(v);
        relax_rows_++;
      }
      tri_of[n] = relaxed[n] ? outer_id(v) : exact_id(v);
    }
    phase("table ids done");

    // Rows in parallel, in chunks of consecutive nodes.
    constexpr int kRowChunk = 65536;
    const int num_chunks = (nodes.size() + kRowChunk - 1) / kRowChunk;
    std::vector<std::string> out(num_chunks);
    std::atomic<int64_t> rows = 0;
    ParallelComp(num_chunks, [&](int64_t ci) {
      std::string &row = out[ci];
      const int hi = std::min<int>(nodes.size(), (ci + 1) * kRowChunk);
      for (int n = ci * kRowChunk; n < hi; n++) {
        const N &node = nodes[n];
        const int iv = iv_of[n];
        if (relax_point(n)) {
          row += std::format(",11,{},{},{},{},{},{}", id_of[n], iv, content_id[n], view_root,
                             tri_exact[node.tri], tri_outer[node.tri]);
          rows++;
        }
        rows++;
        const int id = content_id[n];
        const int region = tri_of[n];
        if (node.split != nullptr) {
          const int k = node.first_kid;
          if (node.split->view) {
            row += std::format(",2,{},{},{},{},{},{},{},{}", id, iv, id_of[k], id_of[k + 1],
                               id_of[k + 2], id_of[k + 3], view_root, region);
          } else if (node.split->eighths == 4) {
            row += std::format(",1,{},{},{},{},{},{},{}", id, iv, id_of[k], id_of[k + 1],
                               node.split->axis + 2, view_root, region);
          } else {
            // Lean cayleySplitAt.
            const geom5d::BoxQ &box = boxes[node.box].box;
            row += std::format(",12,{},{},{},{},{},{},{},{}", id, iv, id_of[k], id_of[k + 1],
                               node.split->axis + 2,
                               Zigzag(geom5d::CutPoint(box, node.split->axis, node.split->eighths)),
                               view_root, region);
          }
        } else if (IsCertificate(node.leaf->leaf)) {
          // Each certificate is used over the triangle it was built for.
          CHECK(relaxed[n] == outer_ok[n]) << node.Path();
          const char *tag = std::holds_alternative<rows5d::CertLeaf>(node.leaf->leaf) ? "4" : "9";
          const BodyRef &b = body_ref[n];
          row += std::format(",{},{},{},{},{}", tag, id, iv, view_root, region);
          row.append(body_buf[b.chunk], b.offset, b.length);
        } else {
          row += OtherLeafRow(t, node.Path(), node.leaf->leaf, id, iv, view_root, region);
        }
      }
    }, threads_);
    phase("rows done");
    num_rows_ += rows.load();
    for (auto &chunk : out) rows_.push_back(std::move(chunk));
    return first_id;
  }

  int64_t RelaxRows() const { return relax_rows_; }
  void SetThreads(int threads) { threads_ = threads; }

  void AddCodeRoot(const std::vector<int> &children) {
    std::string row = std::format(",10,0,{},{}", IntervalId(IntervalString(geom5d::RootBox(chart_))),
                                  children.size());
    for (int c : children) row += std::format(",{}", c);
    rows_.insert(rows_.begin(), row);
    num_rows_++;
  }

  void Write(const std::string &path) const {
    std::ofstream f(path, std::ios::binary);
    CHECK(f.good()) << path;
    f << num_rows_ << "," << intervals_.size();
    for (const auto &s : intervals_) f << s;
    f << "," << triangles_.size();
    for (const auto &s : triangles_) f << s;
    for (const auto &r : rows_) f << r;
    f << "\n";
  }

  size_t NumRows() const { return num_rows_; }

 private:
  static bool IsCertificate(const rows5d::Leaf &leaf) {
    return std::holds_alternative<rows5d::CertLeaf>(leaf) ||
           std::holds_alternative<rows5d::MixedLeaf>(leaf);
  }

  // The part of a certificate leaf's row after its triangle index, built
  // over `tri`. With `check`, *ok says whether it holds exactly (exact5d);
  // otherwise *ok is true.
  template <class PoolFor>
  std::string CertBody(const std::string &path, const rows5d::Leaf &leaf,
                       const exact5d::TriangleQ &tri, int root, const geom5d::BoxQ &box,
                       const PoolFor &pool_for, bool check, bool *ok) const {
    if (const auto *l = std::get_if<rows5d::CertLeaf>(&leaf)) {
      const auto &pool = pool_for(l->cone_samples);
      CHECK(l->triple < (int)pool.triples.size()) << "stale triple index at " << path;
      const cert5d::Single s{.triple = l->triple, .inner = l->inner};
      const exact5d::GlobalBox g = cert5d::ExactGlobalBox(pool, s, tri, box, chart_, root);
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
        cert5d::ExactMixedBox(pool, triples, inner, weights, tri, box, chart_, root);
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
  // (root: the region's projective root; the tube row's first 0 is its
  // symmetry index.)
  std::string OtherLeafRow(int t, const std::string &path, const rows5d::Leaf &leaf, int id,
                           int iv, int root, int tri_id) const {
    return std::visit(
        [&](const auto &l) -> std::string {
          using T = std::decay_t<decltype(l)>;
          if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) {
            const std::string view = rows5d::ViewPath(path);
            std::string r =
                std::format(",6,{},{},0,{},{},{}", id, iv, Zigzag(l.r), t, view.size());
            for (char c : view) r += std::format(",{}", c - '0');
            r += std::format(",{},{}", root, tri_id);
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) {
            return std::format(",7,{},{},{},{}", id, iv, root, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::IcoPruneLeaf>) {
            // Lean Row.icoPrune (tag 13): neighbor index.
            return std::format(",13,{},{},{},{},{}", id, iv, l.neighbor, root, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) {
            return std::format(",8,{},{},{},{},{}", id, iv, l.direction > 0 ? 1 : 0, root, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::CapLeaf>) {
            // Lean Row.capLeaf (tag 16): the cap theorem's domain.
            return std::format(",16,{},{},{},{},{}", id, iv, l.cap, root, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::TieLeaf>) {
            // Lean Row.tieLeaf (tag 15): pinning normal, tie tube radius, tie node;
            // depends on the view triangle, so never relaxed.
            const int node = TieNode(l.normal, t, rows5d::ViewPath(path));
            return std::format(",15,{},{},{},{},{},{},{}", id, iv, l.normal, Zigzag(l.rho), node, root, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::HalfTurnPruneLeaf>) {
            // Lean Row.halfTurnPrune (tag 14): group element index (icoEntry);
            // depends on the view triangle, so never relaxed.
            return std::format(",14,{},{},{},{},{}", id, iv, l.element, root, tri_id);
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
  // The rows, concatenated in chunks (each row starts with ',').
  std::vector<std::string> rows_;
  size_t num_rows_ = 0;
  std::vector<std::string> intervals_, triangles_;
  std::unordered_map<std::string, int> interval_ids_, triangle_ids_;
};

}  // namespace

namespace {

// Reads a job's journal and builds its tree.
rows5d::Tree ReadTree(const std::string &journals, int chart, int t) {
  const auto j = rows5d::ReadJournal(std::format("{}/c{}/t{}.journal", journals, chart, t));
  CHECK(!j.leaves.empty()) << "no journal for t=" << t << " chart=" << chart;
  auto built = rows5d::BuildTree(j.leaves);
  CHECK(std::holds_alternative<rows5d::Tree>(built))
      << "job t=" << t << " chart=" << chart << ": " << std::get<std::string>(built);
  return std::move(std::get<rows5d::Tree>(built));
}

// Packs each job (t in `jobs`) to its own file under out_dir, skipping
// packs newer than their journal unless `force`. Large jobs go one at a
// time with all threads; the rest run concurrently, one thread each.
void PackPerCode(const tubeatlas5d::TubeAtlas &atlas, int chart, bool exact_check,
                 const std::string &journals, const std::string &out_dir,
                 const std::vector<int> &jobs, bool force, int threads) {
  namespace fs = std::filesystem;
  fs::create_directories(std::format("{}/c{}", out_dir, chart));
  struct Job {
    int t;
    uintmax_t journal_bytes;
  };
  std::vector<Job> todo;
  for (int t : jobs) {
    const fs::path journal = std::format("{}/c{}/t{}.journal", journals, chart, t);
    const fs::path pack = std::format("{}/c{}/t{}.pack", out_dir, chart, t);
    CHECK(fs::exists(journal)) << "no journal " << journal;
    if (!force && fs::exists(pack) && fs::last_write_time(pack) > fs::last_write_time(journal)) {
      continue;
    }
    todo.push_back({t, fs::file_size(journal)});
  }
  std::sort(todo.begin(), todo.end(),
            [](const Job &a, const Job &b) { return a.journal_bytes > b.journal_bytes; });
  printf("%zu of %zu code packs to write\n", todo.size(), jobs.size());
  fflush(stdout);
  std::mutex out_mu;
  std::atomic<int> done = 0;
  auto pack_one = [&](const Job &job, int job_threads) {
    const rows5d::Tree tree = ReadTree(journals, chart, job.t);
    Packer packer(atlas, chart, exact_check);
    packer.SetThreads(job_threads);
    packer.AddJob(job.t, tree, 0);
    const std::string path = std::format("{}/c{}/t{}.pack", out_dir, chart, job.t);
    // Write then rename, so a pack that exists is complete.
    packer.Write(path + ".tmp");
    fs::rename(path + ".tmp", path);
    std::lock_guard<std::mutex> l(out_mu);
    printf("[%d/%zu] wrote %s: %zu rows (%lld regionRelax)\n", ++done, todo.size(),
           path.c_str(), packer.NumRows(), (long long)packer.RelaxRows());
    fflush(stdout);
  };
  // Journals above this size get all threads to themselves.
  constexpr uintmax_t kLarge = 20'000'000;
  size_t k = 0;
  for (; k < todo.size() && todo[k].journal_bytes > kLarge; k++) pack_one(todo[k], threads);
  ParallelComp(todo.size() - k, [&](int64_t i) { pack_one(todo[k + i], 1); }, threads);
}

}  // namespace

int main(int argc, char **argv) {
  int chart = -1, single = -1, threads = 8;
  bool all = false, exact_check = false, force = false;
  std::string journals = "jobs", out, trees_dir = "trees_r2", bdd = "codebdd.json", per_code;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--chart") chart = std::stoi(next());
    else if (a == "--t") single = std::stoi(next());
    else if (a == "--all") all = true;
    else if (a == "--per_code") per_code = next();
    else if (a == "--journals") journals = next();
    else if (a == "--out") out = next();
    else if (a == "--trees_dir") trees_dir = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--exact_check") exact_check = true;
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--force") force = true;
    else if (a == "--tie_nodes") LoadTieNodes(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(chart >= 0 && chart <= 3) << "--chart 0..3";

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  if (!per_code.empty()) {
    CHECK(!all) << "--per_code packs every job (or the --t job)";
    std::vector<int> jobs;
    if (single >= 0) {
      jobs.push_back(single);
    } else {
      for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back(t);
    }
    PackPerCode(atlas, chart, exact_check, journals, per_code, jobs, force, threads);
    return 0;
  }
  CHECK(all != (single >= 0)) << "exactly one of --all, --t, --per_code";
  if (out.empty()) out = all ? std::format("chart{}.pack", chart) : std::format("chart{}.t{}.pack", chart, single);

  Packer packer(atlas, chart, exact_check);
  packer.SetThreads(threads);
  // Journals are read and turned into trees in parallel.
  std::vector<int> jobs;
  if (all) {
    for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back(t);
  } else {
    jobs.push_back(single);
  }
  std::vector<rows5d::Tree> trees(jobs.size());
  ParallelComp(jobs.size(), [&](int64_t k) { trees[k] = ReadTree(journals, chart, jobs[k]); },
               threads);
  printf("read %zu job trees\n", trees.size());
  fflush(stdout);
  if (all) {
    std::vector<int> roots;
    int next_id = 1;  // row 0 is the code root
    for (size_t k = 0; k < jobs.size(); k++) {
      const size_t before = packer.NumRows();
      roots.push_back(packer.AddJob(jobs[k], trees[k], next_id));
      next_id += packer.NumRows() - before;
      printf("[%zu/%zu jobs] t=%d: %zu rows (total %zu)\n", k + 1, jobs.size(), jobs[k],
             packer.NumRows() - before, packer.NumRows());
      fflush(stdout);
      rows5d::Tree().splits.swap(trees[k].splits);
      std::vector<rows5d::Record>().swap(trees[k].leaves);
    }
    packer.AddCodeRoot(roots);
  } else {
    packer.AddJob(single, trees[0], 0);
  }
  packer.Write(out);
  printf("wrote %s: %zu rows (%lld regionRelax)\n", out.c_str(), packer.NumRows(),
         (long long)packer.RelaxRows());
  return 0;
}
