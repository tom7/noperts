// Incremental improvement of identity-tube trees (written by tubecode):
// larger certified radii where the 5D search needs them, without touching
// anything else, so that every node's rLower (the minimum certificate radius
// over its subtree, which the 5D search's "tu" rows cite) can only grow and
// existing 5D journals stay valid.
//
// Two steps, both exact (the same audit as tubecode and Lean's
// Box.ViewValid):
//
//  1. Fine radii. A leaf's radius r only has to satisfy
//     r^2 (1 + c^2) <= 4 c^2 (Lean's angle_bound); tubecode rounds it down
//     to a coarse list (1/1000, 1/2000, 1/4000, ...), losing up to 2x. Every
//     leaf gets MaxTubeRadius(c) instead, if larger.
//  2. Refinement. Each leaf below its goal is subdivided (up to --levels
//     levels). The parent's cage is valid on each child, and its variation
//     delta roughly halves per level; where the margin is thin, delta is what
//     eats the cage margin (c = cover - delta), so this alone lifts tiny radii.
//     A fresh cage search runs only where the inherited cage fails or falls
//     short. A refined subtree replaces the leaf only if its minimum radius
//     is larger than the leaf's (and, among options, the fewest nodes win).
//     A leaf's goal is max(--goal, MaxTubeRadius(--goal_frac * cover)),
//     where cover = c + delta is its cage's cover radius: refinement only
//     shrinks delta, so 2 * cover bounds the radius any refinement of that
//     cage can reach, and --goal_frac says how close to go.
//
// Output: <out_dir>/tree.<code>.json (the native format), and a regenerated
// <out_dir>/code.<code>.journal so tubecode can resume from it. The input
// directory is not modified.
//
// Usage: tuberefine.exe --code X [--in_dir trees_r2] [--out_dir trees_r3]
//          [--goal 1/50000] [--goal_frac 0] [--levels 4] [--threads 16] [--tri T]
//        tuberefine.exe --test

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <filesystem>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#define TUBECODE_NO_MAIN
#include "tubecode.cc"

namespace {

// The largest r on a grid of about four significant digits with
// r^2 (1 + c^2) <= 4 c^2, checked exactly. Zero for c <= 0.
BigRat MaxTubeRadius(const BigRat &c) {
  if (c <= BigRat(0)) return BigRat(0);
  const BigRat lhs_factor = BigRat(1) + c * c, rhs = BigRat(4) * c * c;
  const double approx = 2.0 * c.ToDouble() / std::sqrt(1.0 + c.ToDouble() * c.ToDouble());
  // Denominator 10^k with about four significant digits in the numerator.
  int k = std::max(0, 4 - (int)std::floor(std::log10(approx)));
  const BigInt den = BigInt::Pow(BigInt(10), k);
  int64_t num = (int64_t)std::floor(approx * std::pow(10.0, k));
  for (; num > 0; num--) {
    const BigRat r(BigInt(num), den);
    if (r * r * lhs_factor <= rhs) return r;
  }
  return BigRat(0);
}

// A candidate certificate for a triangle: the cage re-audited there, with
// the fine radius.
std::optional<LocalCertificate> AuditCage(const TriangleQ &tri, const LocalCertificate &cage) {
  LocalCertificate out;
  if (!ReauditCertificate(tri, cage, BigRat(0), BigRat(0), &out)) return std::nullopt;
  const BigRat fine = MaxTubeRadius(out.c);
  if (fine > out.r) out.r = fine;
  return out;
}

struct Refined {
  std::unique_ptr<TreeNode> node;
  BigRat min_r{0};
  int leaves = 0;
};

Refined LeafOf(const std::string &path, const LocalCertificate &cert) {
  Refined r;
  r.node = std::make_unique<TreeNode>();
  r.node->path = path;
  r.node->direct_cert = cert;
  r.node->direct_bounds.direct_r_lower = cert.r;
  r.node->direct_bounds.direct_c_lower = cert.c;
  r.min_r = cert.r;
  r.leaves = 1;
  return r;
}

// Best certificate for `tri` within `levels` further subdivisions, starting
// from the inherited cage `hint`: a leaf if its radius reaches `goal` (or
// splitting does not help), otherwise the split with the largest minimum
// radius. min_r is 0 if nothing certifies.
Refined Refine(const TriangleQ &tri, const std::string &path, const LocalCertificate &hint,
               const BigRat &goal, int levels, unsigned int *seed) {
  std::optional<LocalCertificate> leaf = AuditCage(tri, hint);
  if (!leaf.has_value() || leaf->r < goal) {
    LocalCertificate fresh;
    double margin = 0.0;
    if (FindBestCageForTriangle(tri, seed, &fresh, &margin)) {
      std::optional<LocalCertificate> f = AuditCage(tri, fresh);
      if (f.has_value() && (!leaf.has_value() || f->r > leaf->r)) leaf = f;
    }
  }
  if (leaf.has_value() && (leaf->r >= goal || levels == 0)) return LeafOf(path, *leaf);
  if (levels == 0) return Refined{};

  const LocalCertificate &cage = leaf.has_value() ? *leaf : hint;
  TriangleQ ch[4];
  tri.Subdivide(ch);
  Refined split;
  split.node = std::make_unique<TreeNode>();
  split.node->path = path;
  split.node->children.resize(4);
  for (int c = 0; c < 4; c++) {
    Refined child = Refine(ch[c], path + (char)('0' + c), cage, goal, levels - 1, seed);
    if (child.min_r <= BigRat(0)) {
      // A child that cannot be certified makes the split useless.
      return leaf.has_value() ? LeafOf(path, *leaf) : Refined{};
    }
    split.min_r = c == 0 ? child.min_r : BigRat::Min(split.min_r, child.min_r);
    split.leaves += child.leaves;
    split.node->children[c] = std::move(child.node);
  }
  if (leaf.has_value() && leaf->r >= split.min_r) return LeafOf(path, *leaf);
  return split;
}

// The leaves of a tree with their triangles (tubetree subdivision order).
struct LeafRef {
  TreeNode *node;
  TriangleQ tri;
};
void CollectLeaves(TreeNode *node, const TriangleQ &tri, std::vector<LeafRef> *out) {
  if (node->children.empty()) {
    out->push_back({node, tri});
    return;
  }
  TriangleQ ch[4];
  tri.Subdivide(ch);
  for (int c = 0; c < 4; c++) CollectLeaves(node->children[c].get(), ch[c], out);
}

// Journal lines (tubecode's format) for a tree.
void JournalLines(int tri, const TreeNode &node, std::string *out) {
  if (!node.children.empty()) {
    *out += StringPrintf("S %d %s\n", tri, PathToken(node.path).c_str());
    for (const auto &c : node.children) JournalLines(tri, *c, out);
  } else {
    *out += LeafLine(tri, node.path, *node.direct_cert);
  }
}

BigRat MinRadius(const TreeNode &node) {
  if (node.children.empty()) return node.GetCertifiedRadius();
  BigRat m = MinRadius(*node.children[0]);
  for (int c = 1; c < 4; c++) m = BigRat::Min(m, MinRadius(*node.children[c]));
  return m;
}

void Test() {
  // MaxTubeRadius satisfies the bound, is near the real maximum, and is at
  // least the coarse grid's choice.
  for (const char *cs : {"1/1000000000", "3/1000000000", "443/10000000", "1/1000", "1/3", "2"}) {
    const BigRat c(cs);
    const BigRat r = MaxTubeRadius(c);
    CHECK(r * r * (BigRat(1) + c * c) <= BigRat(4) * c * c) << cs;
    const double exact = 2 * c.ToDouble() / std::sqrt(1 + c.ToDouble() * c.ToDouble());
    CHECK(r.ToDouble() > exact * (1 - 2e-4)) << cs << " " << r.ToString() << " " << exact;
  }
  CHECK(MaxTubeRadius(BigRat(0)) == BigRat(0));
  CHECK(MaxTubeRadius(BigRat(-1)) == BigRat(0));
  printf("tuberefine tests PASSED\n");
}

}  // namespace

int main(int argc, char **argv) {
  int code = -1, levels = 4, threads = 16, only_tri = -1;
  std::string in_dir = "trees_r2", out_dir = "trees_r3";
  BigRat goal("1/50000"), goal_frac(0);
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--test") {
      Test();
      return 0;
    } else if (a == "--code") code = std::stoi(next());
    else if (a == "--tri") only_tri = std::stoi(next());
    else if (a == "--in_dir") in_dir = next();
    else if (a == "--out_dir") out_dir = next();
    else if (a == "--goal") goal = BigRat(std::string_view(next()));
    else if (a == "--goal_frac") goal_frac = BigRat(std::string_view(next()));
    else if (a == "--levels") levels = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(code >= 0) << "--code required";
  CHECK(std::filesystem::absolute(in_dir) != std::filesystem::absolute(out_dir))
      << "--out_dir must differ from --in_dir";
  const std::string in_path = StringPrintf("%s/tree.%d.json", in_dir.c_str(), code);
  std::unique_ptr<CodeTree> tree = LoadCodeTreeJson(in_path);
  CHECK(tree != nullptr) << in_path;
  CHECK(tree->IsFullyCertified()) << in_path;

  for (auto &ct : tree->triangles) {
    if (only_tri >= 0 && ct.triangle_index != only_tri) continue;
    std::vector<LeafRef> leaves;
    CollectLeaves(ct.root.get(), ct.triangle, &leaves);
    const BigRat before = MinRadius(*ct.root);

    // 1. Fine radii (r depends only on the stored c).
    int finer = 0;
    for (auto &l : leaves) {
      CHECK(l.node->direct_cert.has_value()) << "only Tag 1 leaves are supported";
      LocalCertificate &cert = *l.node->direct_cert;
      const BigRat fine = MaxTubeRadius(cert.c);
      if (fine > cert.r) {
        cert.r = fine;
        l.node->direct_bounds.direct_r_lower = fine;
        finer++;
      }
    }
    const BigRat after_fine = MinRadius(*ct.root);

    // 2. Refine the leaves below the goal, in parallel.
    std::vector<int> todo;
    std::vector<BigRat> goals(leaves.size());
    for (int i = 0; i < (int)leaves.size(); i++) {
      const LocalCertificate &cert = *leaves[i].node->direct_cert;
      goals[i] = BigRat::Max(goal, MaxTubeRadius(goal_frac * (cert.c + cert.delta)));
      if (cert.r < goals[i]) todo.push_back(i);
    }
    printf("[code %d tri %d] %zu leaves; %d finer radii; min r %s -> %s; refining %zu below their goals (>= %s)\n",
           code, ct.triangle_index, leaves.size(), finer, before.ToString().c_str(),
           after_fine.ToString().c_str(), todo.size(), goal.ToString().c_str());
    fflush(stdout);
    std::vector<Refined> results(todo.size());
    std::atomic<size_t> next{0};
    std::atomic<int> done{0}, improved{0};
    std::mutex print_mu;
    std::vector<std::thread> pool;
    for (int th = 0; th < threads; th++) {
      pool.emplace_back([&]() {
        for (;;) {
          const size_t j = next.fetch_add(1);
          if (j >= todo.size()) return;
          const LeafRef &l = leaves[todo[j]];
          unsigned int seed = 7 + 1000 * code;
          for (char c : l.node->path) seed = seed * 31 + c;
          results[j] = Refine(l.tri, l.node->path, *l.node->direct_cert, goals[todo[j]], levels,
                              &seed);
          if (results[j].min_r > l.node->direct_cert->r) improved++;
          const int d = ++done;
          if (d % 100 == 0) {
            std::lock_guard<std::mutex> g(print_mu);
            printf("  %d/%zu refined, %d improved\n", d, todo.size(), improved.load());
            fflush(stdout);
          }
        }
      });
    }
    for (auto &t : pool) t.join();

    // Replace improved leaves (only strict improvements: rLower is monotone).
    int replaced = 0, new_leaves = 0;
    for (size_t j = 0; j < todo.size(); j++) {
      TreeNode *node = leaves[todo[j]].node;
      Refined &r = results[j];
      if (!(r.min_r > node->direct_cert->r)) continue;
      replaced++;
      new_leaves += r.leaves;
      *node = std::move(*r.node);
    }
    printf("[code %d tri %d] replaced %d leaves by %d; min r now %s\n", code, ct.triangle_index,
           replaced, new_leaves, MinRadius(*ct.root).ToString().c_str());
    fflush(stdout);
  }

  CHECK(tree->IsFullyCertified());
  std::filesystem::create_directories(out_dir);
  const std::string out_path = StringPrintf("%s/tree.%d.json", out_dir.c_str(), code);
  CHECK(SaveCodeTreeJson(*tree, out_path)) << out_path;
  std::string journal;
  for (const auto &ct : tree->triangles) JournalLines(ct.triangle_index, *ct.root, &journal);
  CHECK(Util::WriteFile(StringPrintf("%s/code.%d.journal", out_dir.c_str(), code), journal));
  printf("wrote %s\n", out_path.c_str());
  return 0;
}
