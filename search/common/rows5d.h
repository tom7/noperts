// Search results for one 5D job (a code triangle t and a chart), and the
// journal they are stored in.
//
// A node is named by its split path from the job's root (the code triangle
// and the chart's root box): '0'..'3' take that view child
// (ProjectiveView.split), and 'a'/'b', 'c'/'d', 'e'/'f' take the lower/upper
// half of the box in x, y, z (AtlasInterval.lowerHalf/upperHalf). A cut at
// another point is two characters: 'A'/'B', 'C'/'D', 'E'/'F' take the part
// below/above the cut in x, y, z, followed by a digit '1'..'7', the cut's
// position in eighths of the range (AtlasInterval.lowerAt/upperAt; Lean's
// cayleySplitAt). The journal records only leaves; a node is a split exactly when longer leaf
// paths extend it, and the next character says which kind, so the tree (and
// Lean's rows) can be rebuilt from the leaves alone.
//
// Journal lines (text):
//   ce <path> <cone_samples> <triple> <in0> <in1> <in2>   projectiveGlobal (ballMultiplier 0)
//   mx <path> <cone_samples> <K> {<triple> <in0> <in1> <in2> <weight>}^K
//                                 projectiveMixedGlobal; exact weights summing to 1
//   tu <path> <r>                 symmetryTube with radius r (exact rational)
//   pr <path>                     radiusPrune
//   pf <path> <+|->               fundamentalPrune (direction positive/negative; fivefold solids)
//   pi <path> <n>                 icosahedral prune by symmetry neighbor n (symmetry-neighbors.h;
//                                 exact5d::IcoPruneValid); for the Septopert, the C3 cell prune
//                                 by c3Mat (n + 1)
//   ph <path> <g>                 half-turn prune by group element g (ico-group.h;
//                                 exact5d::HalfTurnPruneValid; centrally symmetric solids); for
//                                 the Septopert, the mirror prune by Q_g = mirrorQMat g (mirror-q.h)
//   cl <path> <c>                 cap leaf: the box lies in cap c's certified domain (capcert.cc)
//   tl <path> <n> <rho>           tie leaf: pinning normal n (tie-normals.h), tie tube radius rho
//                                 (exact5d::TieLeafValid; tietube.cc certifies the tube)
//   df <path>                     deferred: an unresolved subtree (not packable)
//   done <path>                   the subtree at <path> is complete: every leaf
//                                 below it is in the journal (written after them)
// The root path is written as ".". Integers are decimal. A truncated last
// line is ignored.

#ifndef _NOPERT_ROWS5D_H
#define _NOPERT_ROWS5D_H

#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "bignum/big.h"
#include "geom5d.h"

namespace rows5d {

// Split path characters (a cut step is a cut letter and an eighths digit).
bool IsViewStep(char c);
bool IsBoxStep(char c);
bool IsCutStep(char c);
// For a box or cut step letter: the axis (0..2) and whether it is the upper
// part.
int BoxAxis(char c);
bool BoxUpper(char c);
char BoxStep(int axis, bool upper);
std::string CutStep(int axis, bool upper, int eighths);

// One parsed step of a path.
struct Step {
  size_t offset = 0, length = 1;  // its characters in the path
  bool view = false;
  int child = 0;    // view: 0..3; box: 0 lower, 1 upper
  int axis = 0;     // box
  int eighths = 4;  // box: the cut position; 4 is the midpoint (one char)
};
// The steps of a path, or nullopt if it is malformed.
std::optional<std::vector<Step>> ParseSteps(std::string_view path);
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
struct MixedLeaf {
  int cone_samples = 0;
  struct Component {
    int triple = 0;
    std::array<int, 3> inner{};
    BigRat weight;
  };
  std::vector<Component> components;  // 1..4
};
struct TubeLeaf {
  BigRat r;
};
struct RadiusPruneLeaf {};
struct FundamentalPruneLeaf {
  int direction = 1;  // +1 positive, -1 negative
};
struct DeferredLeaf {};
struct IcoPruneLeaf {
  int neighbor = 0;
};
struct HalfTurnPruneLeaf {
  int element = 0;
};
struct TieLeaf {
  int normal = 0;
  BigRat rho;
};
struct CapLeaf {
  int cap = 0;
};
using Leaf = std::variant<CertLeaf, MixedLeaf, TubeLeaf, RadiusPruneLeaf, FundamentalPruneLeaf, DeferredLeaf,
                          IcoPruneLeaf, HalfTurnPruneLeaf, TieLeaf, CapLeaf>;

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
  int eighths = 4;   // for a box split: the cut (4 = midpoint, cayleySplit)
};
// The children's paths, in order (view children 0..3; lower, then upper).
std::vector<std::string> ChildPaths(const Split &s);
struct Tree {
  std::vector<Split> splits;     // preorder
  std::vector<Record> leaves;    // in path order
};
std::variant<Tree, std::string> BuildTree(const std::vector<Record> &leaves,
                                          std::string_view root = "");

}  // namespace rows5d

#endif
