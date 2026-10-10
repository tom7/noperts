module

public import Pipeline.AtlasProjectiveSolutionTree

@[expose] public section

/-!
# Four-row exclusion of Cayley chart 3

In the fivefold max-trace fundamental domain, chart 3 is empty.  Splitting
once at `z = 0` makes the two adjacent-symmetry advantages uniformly
positive. The executable checks this tiny table natively, like the other
charts, without any array-backed generated data; `Tests/FundamentalChart3`
also checks it with the kernel for each solid.
-/

open Noperts Noperts.Pipeline

namespace Noperts.Pipeline.FundamentalChart3

variable [IcosahedralSolid] [CodeTriangleCover]

open AtlasProjectiveSolutionTree AtlasProjectiveView
open Noperts.Atlas.ProjectiveView

def root : AtlasProjectiveSolutionTree.Interval :=
  AtlasFundamentalPrune.restrictedRootInterval 3
def lower : AtlasProjectiveSolutionTree.Interval := root.lowerHalf 4
def upper : AtlasProjectiveSolutionTree.Interval := root.upperHalf 4

def region : AtlasProjectiveSolutionTree.Region :=
  .triangle 0 upperWedgeTriangle

def getRowKernel : ℕ → AtlasProjectiveSolutionTree.Row
  | 0 => .viewRoot 0 1 root
  | 1 => .cayleySplit 1 2 3 4 root region
  | 2 => .fundamentalPrune 2
      { interval := lower, chart := 3, direction := .negative } region
  | 3 => .fundamentalPrune 3
      { interval := upper, chart := 3, direction := .positive } region
  | _ => default

def table : AtlasProjectiveSolutionTree.Table where
  chart := 3
  get := getRowKernel
  size := 4

end Noperts.Pipeline.FundamentalChart3

end
