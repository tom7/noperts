#include "rows5d.h"

#include <cstdio>
#include <string>
#include <variant>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "solid.h"

using namespace rows5d;

int main() {
  // Path helpers.
  CHECK(ViewPath("0a1fc3") == "013");
  CHECK(BoxAxis('a') == 0 && !BoxUpper('a') && BoxAxis('f') == 2 && BoxUpper('f'));
  CHECK(BoxStep(1, true) == 'd');
  const geom5d::BoxQ root = geom5d::RootBox(0);
  const geom5d::BoxQ b = NodeBox(root, "0b2e");
  CHECK(b.lo[0] == BigRat(0) && b.hi[0] == BigRat(1));                    // x upper half
  // z lower half (of [-1/3, 1/3] in chart 0 with the fivefold narrowing)
  CHECK(b.lo[2] == (solid::kFivefold ? BigRat(-1, 3) : BigRat(-1)) && b.hi[2] == BigRat(0));
  // Cut steps: a letter and an eighths digit ('4' is written as a box step).
  CHECK(CutStep(0, false, 3) == "A3" && CutStep(2, true, 7) == "F7" && CutStep(1, true, 4) == "d");
  CHECK(ViewPath("A31D52") == "12");
  CHECK(!ParseSteps("A4").has_value() && !ParseSteps("A").has_value() && !ParseSteps("A8").has_value());
  {
    const auto steps = *ParseSteps("2B3a");
    CHECK(steps.size() == 3 && steps[1].offset == 1 && steps[1].length == 2 && steps[1].child == 1 &&
          steps[1].eighths == 3 && steps[2].offset == 3);
    // x range [lo, hi] of the root; B3 is [lo + 3/8 (hi - lo), hi].
    const geom5d::BoxQ c = NodeBox(root, "B3");
    CHECK(c.lo[0] == root.lo[0] + (root.hi[0] - root.lo[0]) * BigRat(3, 8) && c.hi[0] == root.hi[0]);
    const geom5d::BoxQ d = NodeBox(root, "E5");
    CHECK(d.lo[2] == root.lo[2] && d.hi[2] == root.lo[2] + (root.hi[2] - root.lo[2]) * BigRat(5, 8));
  }

  // Records round-trip through the journal format.
  std::string text;
  const std::vector<Record> recs = {
      {"", CertLeaf{8, 12, {1, 2, 3}}},
      {"1a", TubeLeaf{BigRat(1, 1000000000)}},
      {"1b", RadiusPruneLeaf{}},
      {"2c3", FundamentalPruneLeaf{-1}},
      {"3", DeferredLeaf{}},
  };
  for (const auto &r : recs) text += FormatRecord(r) + "\n";
  text += FormatDone("1") + "\n";
  CHECK(FormatRecord(recs[0]) == "ce . 8 12 1 2 3");
  CHECK(FormatRecord(recs[1]) == "tu 1a 1/1000000000");
  CHECK(FormatRecord(recs[3]) == "pf 2c3 -");
  const Journal j = ParseJournal(text + "ce 0 8 1 2 3");  // truncated last line ignored
  CHECK(j.done.size() == 1 && j.done[0] == "1");
  // The root leaf "" is an ancestor of the later leaves, so it is replaced.
  CHECK(j.leaves.size() == 4) << j.leaves.size();
  CHECK(std::holds_alternative<TubeLeaf>(j.leaves[0].leaf));
  CHECK(std::get<TubeLeaf>(j.leaves[0].leaf).r == BigRat(1, 1000000000));

  // A deferred subtree later solved deeper.
  const Journal j2 = ParseJournal("df 3\nce 30 8 1 0 0 0\nce 31 8 1 0 0 0\n");
  CHECK(j2.leaves.size() == 2);

  // Tree reconstruction.
  std::vector<Record> leaves;
  for (char v : std::string("012")) leaves.push_back({std::string(1, v), RadiusPruneLeaf{}});
  leaves.push_back({"3a", RadiusPruneLeaf{}});
  leaves.push_back({"3b0", RadiusPruneLeaf{}});
  leaves.push_back({"3b1", RadiusPruneLeaf{}});
  leaves.push_back({"3b2", RadiusPruneLeaf{}});
  leaves.push_back({"3b3", RadiusPruneLeaf{}});
  auto t = BuildTree(leaves);
  CHECK(std::holds_alternative<Tree>(t)) << std::get<std::string>(t);
  const Tree &tree = std::get<Tree>(t);
  CHECK(tree.splits.size() == 3);  // "", "3", "3b"
  CHECK(tree.splits[0].path == "" && tree.splits[0].view);
  CHECK(tree.splits[1].path == "3" && !tree.splits[1].view && tree.splits[1].axis == 0);
  CHECK(tree.leaves.size() == 8);
  // Errors: a missing child, mixed split kinds.
  auto missing = leaves;
  missing.pop_back();
  CHECK(std::holds_alternative<std::string>(BuildTree(missing)));
  auto mixed = leaves;
  mixed.push_back({"3c", RadiusPruneLeaf{}});
  CHECK(std::holds_alternative<std::string>(BuildTree(mixed)));
  // A subtree under a root.
  auto sub = BuildTree(leaves, "3");
  CHECK(std::holds_alternative<Tree>(sub));
  CHECK(std::get<Tree>(sub).leaves.size() == 5);

  // Trees with cuts.
  {
    std::vector<Record> cl = {{"A3", RadiusPruneLeaf{}}, {"B3C6", RadiusPruneLeaf{}},
                              {"B3D60", RadiusPruneLeaf{}}, {"B3D61", RadiusPruneLeaf{}},
                              {"B3D62", RadiusPruneLeaf{}}, {"B3D63", RadiusPruneLeaf{}}};
    auto ct = BuildTree(cl);
    CHECK(std::holds_alternative<Tree>(ct)) << std::get<std::string>(ct);
    const Tree &tr = std::get<Tree>(ct);
    CHECK(tr.splits.size() == 3);
    CHECK(tr.splits[0].path == "" && !tr.splits[0].view && tr.splits[0].axis == 0 &&
          tr.splits[0].eighths == 3);
    CHECK(tr.splits[1].path == "B3" && tr.splits[1].axis == 1 && tr.splits[1].eighths == 6);
    CHECK(tr.splits[2].path == "B3D6" && tr.splits[2].view);
    CHECK(ChildPaths(tr.splits[1]) == std::vector<std::string>({"B3C6", "B3D6"}));
    // A cut and a midpoint split of the same axis at one node are mixed.
    cl.push_back({"a", RadiusPruneLeaf{}});
    CHECK(std::holds_alternative<std::string>(BuildTree(cl)));
    // Journals accept cut paths.
    const Journal jc = ParseJournal("pr A3\npr B3\n");
    CHECK(jc.leaves.size() == 2 && jc.leaves[1].path == "B3");
  }

  printf("rows5d tests PASSED\n");
  return 0;
}
