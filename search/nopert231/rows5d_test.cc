#include "rows5d.h"

#include <cstdio>
#include <string>
#include <variant>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

using namespace rows5d;

int main() {
  // Path helpers.
  CHECK(ViewPath("0a1fc3") == "013");
  CHECK(BoxAxis('a') == 0 && !BoxUpper('a') && BoxAxis('f') == 2 && BoxUpper('f'));
  CHECK(BoxStep(1, true) == 'd');
  const geom5d::BoxQ root = geom5d::RootBox(0);
  const geom5d::BoxQ b = NodeBox(root, "0b2e");
  CHECK(b.lo[0] == BigRat(0) && b.hi[0] == BigRat(1));                    // x upper half
  CHECK(b.lo[2] == BigRat(-1, 3) && b.hi[2] == BigRat(0));                // z lower half

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

  printf("rows5d tests PASSED\n");
  return 0;
}
