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
bool IsCutStep(char c) { return c >= 'A' && c <= 'F'; }
int BoxAxis(char c) { return IsCutStep(c) ? (c - 'A') / 2 : (c - 'a') / 2; }
bool BoxUpper(char c) { return (IsCutStep(c) ? (c - 'A') % 2 : (c - 'a') % 2) == 1; }
char BoxStep(int axis, bool upper) { return (char)('a' + 2 * axis + (upper ? 1 : 0)); }
std::string CutStep(int axis, bool upper, int eighths) {
  CHECK(eighths >= 1 && eighths <= 7) << eighths;
  if (eighths == 4) return std::string(1, BoxStep(axis, upper));
  return std::string{(char)('A' + 2 * axis + (upper ? 1 : 0)), (char)('0' + eighths)};
}

std::optional<std::vector<Step>> ParseSteps(std::string_view path) {
  std::vector<Step> steps;
  steps.reserve(path.size());
  for (size_t i = 0; i < path.size();) {
    const char c = path[i];
    Step s{.offset = i};
    if (IsViewStep(c)) {
      s.view = true;
      s.child = c - '0';
    } else if (IsBoxStep(c)) {
      s.axis = BoxAxis(c);
      s.child = BoxUpper(c) ? 1 : 0;
    } else if (IsCutStep(c) && i + 1 < path.size() && path[i + 1] >= '1' && path[i + 1] <= '7' &&
               path[i + 1] != '4') {
      s.length = 2;
      s.axis = BoxAxis(c);
      s.child = BoxUpper(c) ? 1 : 0;
      s.eighths = path[i + 1] - '0';
    } else {
      return std::nullopt;
    }
    i += s.length;
    steps.push_back(s);
  }
  return steps;
}

static std::vector<Step> Steps(std::string_view path) {
  auto s = ParseSteps(path);
  CHECK(s.has_value()) << "bad path " << path;
  return *s;
}

std::string ViewPath(std::string_view path) {
  std::string v;
  for (const Step &s : Steps(path)) {
    if (s.view) v += (char)('0' + s.child);
  }
  return v;
}

exact5d::TriangleQ NodeTriangle(const exact5d::TriangleQ &root, std::string_view path) {
  exact5d::TriangleQ t = root;
  for (const Step &s : Steps(path)) {
    if (s.view) t = geom5d::SplitTriangle(t, s.child);
  }
  return t;
}

static geom5d::BoxQ ChildBox(const geom5d::BoxQ &b, int axis, int eighths, bool upper) {
  if (eighths == 4) return upper ? geom5d::UpperHalf(b, axis) : geom5d::LowerHalf(b, axis);
  return upper ? geom5d::UpperAt(b, axis, eighths) : geom5d::LowerAt(b, axis, eighths);
}

geom5d::BoxQ NodeBox(const geom5d::BoxQ &root, std::string_view path) {
  geom5d::BoxQ b = root;
  for (const Step &s : Steps(path)) {
    if (!s.view) b = ChildBox(b, s.axis, s.eighths, s.child == 1);
  }
  return b;
}

std::vector<std::string> ChildPaths(const Split &s) {
  if (s.view) return {s.path + '0', s.path + '1', s.path + '2', s.path + '3'};
  return {s.path + CutStep(s.axis, false, s.eighths), s.path + CutStep(s.axis, true, s.eighths)};
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
        } else if constexpr (std::is_same_v<T, MixedLeaf>) {
          std::string out = std::format("mx {} {} {}", p, leaf.cone_samples, leaf.components.size());
          for (const auto &c : leaf.components) {
            out += std::format(" {} {} {} {} {}", c.triple, c.inner[0], c.inner[1], c.inner[2],
                               c.weight.ToString());
          }
          return out;
        } else if constexpr (std::is_same_v<T, TubeLeaf>) {
          return std::format("tu {} {}", p, leaf.r.ToString());
        } else if constexpr (std::is_same_v<T, RadiusPruneLeaf>) {
          return std::format("pr {}", p);
        } else if constexpr (std::is_same_v<T, FundamentalPruneLeaf>) {
          return std::format("pf {} {}", p, leaf.direction > 0 ? "+" : "-");
        } else if constexpr (std::is_same_v<T, IcoPruneLeaf>) {
          return std::format("pi {} {}", p, leaf.neighbor);
        } else if constexpr (std::is_same_v<T, HalfTurnPruneLeaf>) {
          return std::format("ph {} {}", p, leaf.element);
        } else if constexpr (std::is_same_v<T, TieLeaf>) {
          return std::format("tl {} {} {}", p, leaf.normal, leaf.rho.ToString());
        } else {
          return std::format("df {}", p);
        }
      },
      r.leaf);
}

std::string FormatDone(std::string_view path) { return std::format("done {}", PathToken(path)); }

static bool ValidPath(std::string_view p) { return ParseSteps(p).has_value(); }

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
    } else if (tag == "mx") {
      MixedLeaf m;
      int k = 0;
      CHECK(ss >> m.cone_samples >> k && k >= 1 && k <= 4) << line;
      for (int i = 0; i < k; i++) {
        MixedLeaf::Component c;
        std::string w;
        CHECK(ss >> c.triple >> c.inner[0] >> c.inner[1] >> c.inner[2] >> w) << line;
        c.weight = BigRat(std::string_view(w));
        m.components.push_back(c);
      }
      leaf = m;
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
    } else if (tag == "pi") {
      IcoPruneLeaf l;
      CHECK(ss >> l.neighbor && l.neighbor >= 0) << line;
      leaf = l;
    } else if (tag == "tl") {
      TieLeaf l;
      std::string r;
      CHECK(ss >> l.normal >> r) << line;
      l.rho = BigRat(std::string_view(r));
      leaf = l;
    } else if (tag == "ph") {
      HalfTurnPruneLeaf l;
      CHECK(ss >> l.element && l.element >= 0) << line;
      leaf = l;
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
  // Internal nodes: proper prefixes of leaf paths (from root), at step
  // boundaries, with the split their next step implies.
  std::map<std::string, Split> split_at;
  for (const auto &[p, r] : leaf_at) {
    for (const Step &st : Steps(std::string_view(p).substr(root.size()))) {
      const std::string prefix = p.substr(0, root.size() + st.offset);
      if (leaf_at.count(prefix)) return std::format("leaf {} has descendants", PathToken(prefix));
      const Split s{.path = prefix, .view = st.view, .axis = st.view ? 0 : st.axis,
                    .eighths = st.view ? 4 : st.eighths};
      auto it = split_at.find(prefix);
      if (it == split_at.end()) {
        split_at[prefix] = s;
      } else if (it->second.view != s.view || it->second.axis != s.axis ||
                 it->second.eighths != s.eighths) {
        return std::format("mixed splits at {}", PathToken(prefix));
      }
    }
  }
  Tree tree;
  // Every child of every internal node must be a leaf or internal.
  for (const auto &[node, s] : split_at) {
    for (const auto &c : ChildPaths(s)) {
      if (!leaf_at.count(c) && !split_at.count(c)) return std::format("missing child {}", PathToken(c));
    }
    tree.splits.push_back(s);
  }
  if (!leaf_at.count(std::string(root)) && !split_at.count(std::string(root))) {
    return std::string("root is neither a leaf nor a split");
  }
  for (const auto &[p, r] : leaf_at) tree.leaves.push_back(*r);
  return tree;
}

}  // namespace rows5d
