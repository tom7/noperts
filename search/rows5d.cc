#include "rows5d.h"

#include <algorithm>
#include <format>
#include <map>
#include <set>
#include <sstream>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "util.h"

namespace rows5d {

bool IsViewStep(char c) { return c >= '0' && c <= '3'; }
bool IsBoxStep(char c) { return c >= 'a' && c <= 'f'; }
int BoxAxis(char c) { return (c - 'a') / 2; }
bool BoxUpper(char c) { return ((c - 'a') % 2) == 1; }
char BoxStep(int axis, bool upper) { return (char)('a' + 2 * axis + (upper ? 1 : 0)); }

std::string ViewPath(std::string_view path) {
  std::string v;
  for (char c : path) {
    if (IsViewStep(c)) v += c;
  }
  return v;
}

exact5d::TriangleQ NodeTriangle(const exact5d::TriangleQ &root, std::string_view path) {
  exact5d::TriangleQ t = root;
  for (char c : path) {
    if (IsViewStep(c)) t = geom5d::SplitTriangle(t, c - '0');
  }
  return t;
}

geom5d::BoxQ NodeBox(const geom5d::BoxQ &root, std::string_view path) {
  geom5d::BoxQ b = root;
  for (char c : path) {
    if (IsBoxStep(c)) b = BoxUpper(c) ? geom5d::UpperHalf(b, BoxAxis(c)) : geom5d::LowerHalf(b, BoxAxis(c));
  }
  return b;
}

static std::string PathToken(std::string_view p) { return p.empty() ? "." : std::string(p); }

std::string FormatRecord(const Record &r) {
  const std::string p = PathToken(r.path);
  return std::visit(
      [&](const auto &leaf) -> std::string {
        using T = std::decay_t<decltype(leaf)>;
        if constexpr (std::is_same_v<T, CertLeaf>) {
          return std::format("ce {} {} {} {} {} {}", p, leaf.cone_samples, leaf.triple,
                             leaf.inner[0], leaf.inner[1], leaf.inner[2]);
        } else if constexpr (std::is_same_v<T, TubeLeaf>) {
          return std::format("tu {} {}", p, leaf.r.ToString());
        } else if constexpr (std::is_same_v<T, RadiusPruneLeaf>) {
          return std::format("pr {}", p);
        } else if constexpr (std::is_same_v<T, FundamentalPruneLeaf>) {
          return std::format("pf {} {}", p, leaf.direction > 0 ? "+" : "-");
        } else {
          return std::format("df {}", p);
        }
      },
      r.leaf);
}

std::string FormatDone(std::string_view path) { return std::format("done {}", PathToken(path)); }

static bool ValidPath(std::string_view p) {
  return std::all_of(p.begin(), p.end(), [](char c) { return IsViewStep(c) || IsBoxStep(c); });
}

Journal ParseJournal(std::string_view text) {
  std::map<std::string, Leaf> leaves;
  Journal j;
  std::istringstream in{std::string(text)};
  std::string line;
  while (std::getline(in, line)) {
    if (in.eof() && !text.empty() && text.back() != '\n') break;  // truncated last line
    std::istringstream ss(line);
    std::string tag, tok;
    if (!(ss >> tag >> tok)) continue;
    const std::string path = tok == "." ? "" : tok;
    CHECK(ValidPath(path)) << "bad path in journal line: " << line;
    std::optional<Leaf> leaf;
    if (tag == "ce") {
      CertLeaf c;
      CHECK(ss >> c.cone_samples >> c.triple >> c.inner[0] >> c.inner[1] >> c.inner[2]) << line;
      leaf = c;
    } else if (tag == "tu") {
      std::string r;
      CHECK(ss >> r) << line;
      leaf = TubeLeaf{BigRat(std::string_view(r))};
    } else if (tag == "pr") {
      leaf = RadiusPruneLeaf{};
    } else if (tag == "pf") {
      std::string d;
      CHECK(ss >> d && (d == "+" || d == "-")) << line;
      leaf = FundamentalPruneLeaf{d == "+" ? 1 : -1};
    } else if (tag == "df") {
      leaf = DeferredLeaf{};
    } else if (tag == "done") {
      j.done.push_back(path);
      continue;
    } else {
      LOG(FATAL) << "unknown journal line: " << line;
    }
    // The latest record wins along a path: a new leaf replaces any earlier
    // leaf at the same node, at an ancestor (e.g. a deferred subtree that was
    // later solved), or below it (a subtree replaced by a coarser leaf).
    for (size_t len = 0; len < path.size(); len++) leaves.erase(path.substr(0, len));
    for (auto it = leaves.lower_bound(path); it != leaves.end() && it->first.starts_with(path);) {
      it = leaves.erase(it);
    }
    leaves[path] = *leaf;
  }
  for (const auto &[p, leaf] : leaves) j.leaves.push_back(Record{p, leaf});
  return j;
}

Journal ReadJournal(const std::string &filename) {
  std::string text;
  if (!Util::ExistsFile(filename)) return {};
  text = Util::ReadFile(filename);
  return ParseJournal(text);
}

std::variant<Tree, std::string> BuildTree(const std::vector<Record> &leaves,
                                          std::string_view root) {
  // Collect leaves under root and all their proper prefixes (at or below root).
  std::map<std::string, const Record *> leaf_at;
  for (const Record &r : leaves) {
    if (r.path.size() < root.size() || r.path.compare(0, root.size(), root) != 0) continue;
    leaf_at[r.path] = &r;
  }
  if (leaf_at.empty()) return std::string("no leaves under the root");
  // Internal nodes: proper prefixes of leaf paths (from root).
  std::map<std::string, char> next_step;  // internal node -> a following step
  for (const auto &[p, r] : leaf_at) {
    for (size_t len = root.size(); len < p.size(); len++) {
      const std::string prefix = p.substr(0, len);
      if (leaf_at.count(prefix)) return std::format("leaf {} has descendants", PathToken(prefix));
      const char step = p[len];
      auto it = next_step.find(prefix);
      if (it == next_step.end()) {
        next_step[prefix] = step;
      } else {
        const bool same_kind = IsViewStep(it->second) ? IsViewStep(step)
                                                       : (IsBoxStep(step) && BoxAxis(step) == BoxAxis(it->second));
        if (!same_kind) return std::format("mixed splits at {}", PathToken(prefix));
      }
    }
  }
  Tree tree;
  // Every child of every internal node must be a leaf or internal.
  for (const auto &[node, step] : next_step) {
    Split s;
    s.path = node;
    s.view = IsViewStep(step);
    s.axis = s.view ? 0 : BoxAxis(step);
    std::vector<std::string> children;
    if (s.view) {
      for (char c = '0'; c <= '3'; c++) children.push_back(node + c);
    } else {
      children.push_back(node + BoxStep(s.axis, false));
      children.push_back(node + BoxStep(s.axis, true));
    }
    for (const auto &c : children) {
      if (!leaf_at.count(c) && !next_step.count(c)) return std::format("missing child {}", PathToken(c));
    }
    tree.splits.push_back(s);
  }
  if (!leaf_at.count(std::string(root)) && !next_step.count(std::string(root))) {
    return std::string("root is neither a leaf nor a split");
  }
  for (const auto &[p, r] : leaf_at) tree.leaves.push_back(*r);
  return tree;
}

}  // namespace rows5d
