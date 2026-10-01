// Search results for one 5D job (a code triangle t and a chart), and the
// journal they are stored in.
//
// A node is named by its split path from the job's root (the code triangle
// and the chart's root box): '0'..'3' take that view child
// (ProjectiveView.split), and 'a'/'b', 'c'/'d', 'e'/'f' take the lower/upper
// half of the box in x, y, z (AtlasInterval.lowerHalf/upperHalf). The
// journal records only leaves; a node is a split exactly when longer leaf
// paths extend it, and the next character says which kind, so the tree (and
// Lean's rows) can be rebuilt from the leaves alone.
//
// Journal lines (text):
//   ce <path> <cone_samples> <triple> <in0> <in1> <in2>   projectiveGlobal (ballMultiplier 0)
//   tu <path> <r>                 symmetryTube with radius r (exact rational)
//   pr <path>                     radiusPrune
//   pf <path> <+|->               fundamentalPrune (direction positive/negative)
//   df <path>                     deferred: an unresolved subtree (not packable)
//   done <path>                   the subtree at <path> is complete: every leaf
//                                 below it is in the journal (written after them)
// The root path is written as ".". Integers are decimal. A truncated last
// line is ignored.

#ifndef _NOPERT229_ROWS5D_H
#define _NOPERT229_ROWS5D_H

#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "bignum/big.h"
#include "geom5d.h"

namespace rows5d {

// Split path characters.
bool IsViewStep(char c);
bool IsBoxStep(char c);
// For a box step: the axis (0..2) and whether it is the upper half.
int BoxAxis(char c);
bool BoxUpper(char c);
char BoxStep(int axis, bool upper);
// The view digits of a path, in order (the path in the tube table).
std::string ViewPath(std::string_view path);
// The node's exact triangle and box from the job root.
exact5d::TriangleQ NodeTriangle(const exact5d::TriangleQ &root, std::string_view path);
geom5d::BoxQ NodeBox(const geom5d::BoxQ &root, std::string_view path);

struct CertLeaf {
  int cone_samples = 0;
  int triple = 0;
  std::array<int, 3> inner{};
};
struct TubeLeaf {
  BigRat r;
};
struct RadiusPruneLeaf {};
struct FundamentalPruneLeaf {
  int direction = 1;  // +1 positive, -1 negative
};
struct DeferredLeaf {};
using Leaf = std::variant<CertLeaf, TubeLeaf, RadiusPruneLeaf, FundamentalPruneLeaf, DeferredLeaf>;

struct Record {
  std::string path;
  Leaf leaf;
};

std::string FormatRecord(const Record &r);
std::string FormatDone(std::string_view path);

// A parsed journal: leaves in path order and completed subtree roots. The
// latest record wins along a path (a leaf replaces earlier leaves at the same
// node, its ancestors, or its descendants), so a deferred subtree that is
// later solved, or a subtree redone more coarsely, reads correctly.
struct Journal {
  std::vector<Record> leaves;
  std::vector<std::string> done;
};
Journal ParseJournal(std::string_view text);
Journal ReadJournal(const std::string &filename);  // empty if missing

// The tree implied by a set of leaves: for every internal node, its kind and
// children. Fails (returns an error) if the leaves do not form a complete
// tree under `root` (a missing child, a leaf with descendants, or mixed split
// kinds at one node).
struct Split {
  std::string path;
  bool view = true;  // view split (4 children) or box split
  int axis = 0;      // for a box split
};
struct Tree {
  std::vector<Split> splits;     // preorder
  std::vector<Record> leaves;    // in path order
};
std::variant<Tree, std::string> BuildTree(const std::vector<Record> &leaves,
                                          std::string_view root = "");

}  // namespace rows5d

#endif
