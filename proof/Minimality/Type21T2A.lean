module

public import Minimality.Type21TA
public import Minimality.SilS0XC

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-! Phase 1: the quad-diagonal views s02 s24 s36 s56 (one edge-on facet, C resp. G) through the
type-free interface `s0x_seg_rupert`; Phase 2: the complete line lists (all realizable facing patterns). -/

/-- The eight facets of type 21 as a type-free facet family. -/
noncomputable def h21t2_sfac (T : Facets21 x) : S0xFac 8 h21S x where
  f := (fac8 T).f
  N := (fac8 T).N
  hN := (fac8 T).hN
  zero := (fac8 T).zero
  neg := (fac8 T).neg

def h21t2_dSeg5 : List (S0xSeg 7 8 5) := [
  ⟨0, 2, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- s02 CvE-F-
  ⟨0, 2, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- s02 C^E-F-
  ⟨0, 2, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s02 CvE+F+
  ⟨0, 2, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- s02 C^E+F+
  ⟨2, 4, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- s24 GvB-F-
  ⟨2, 4, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- s24 G^B-F-
  ⟨2, 4, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- s24 GvB+F+
  ⟨2, 4, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- s24 G^B+F+
  ⟨3, 6, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- s36 GvA-B-
  ⟨3, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s36 G^A-B-
  ⟨3, 6, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- s36 GvA+B+
  ⟨3, 6, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- s36 G^A+B+
  ⟨5, 6, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- s56 CvA-E-
  ⟨5, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s56 C^A-E-
  ⟨5, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- s56 CvA+E+
  ⟨5, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩  -- s56 C^A+E+
]

def h21t2_dSeg6 : List (S0xSeg 7 8 6) := [
  ⟨0, 2, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- s02 CvE+F-
  ⟨0, 2, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- s02 C^E+F-
  ⟨0, 2, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- s02 CvE-F+
  ⟨0, 2, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- s02 C^E-F+
  ⟨2, 4, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- s24 GvB+F-
  ⟨2, 4, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- s24 G^B+F-
  ⟨2, 4, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- s24 GvB-F+
  ⟨2, 4, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- s24 G^B-F+
  ⟨3, 6, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- s36 GvA+B-
  ⟨3, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- s36 G^A+B-
  ⟨3, 6, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- s36 GvA-B+
  ⟨3, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- s36 G^A-B+
  ⟨5, 6, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- s56 CvA+E-
  ⟨5, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- s56 C^A+E-
  ⟨5, 6, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- s56 CvA-E+
  ⟨5, 6, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩  -- s56 C^A-E+
]

def h21t2_lin3 : List (h21b_LinSpec 3) := [
  ⟨0, 2, ![false, true, false, false, false, false, false, false], ![0, 1, 5]⟩,  -- LAC 01000000
  ⟨0, 2, ![false, false, false, true, false, false, false, false], ![0, 4, 6]⟩,  -- LAC 00010000
  ⟨0, 2, ![true, true, true, false, true, true, true, true], ![0, 4, 6]⟩,  -- LAC 11101111
  ⟨0, 2, ![true, false, true, true, true, true, true, true], ![0, 1, 5]⟩,  -- LAC 10111111
  ⟨0, 5, ![false, true, false, false, false, false, false, false], ![0, 1, 5]⟩,  -- LAF 01000000
  ⟨0, 5, ![false, false, false, false, true, false, false, false], ![1, 3, 4]⟩,  -- LAF 00001000
  ⟨0, 5, ![true, true, true, true, false, true, true, true], ![1, 3, 4]⟩,  -- LAF 11110111
  ⟨0, 5, ![true, false, true, true, true, true, true, true], ![0, 1, 5]⟩,  -- LAF 10111111
  ⟨0, 6, ![false, false, false, true, false, false, false, false], ![0, 4, 6]⟩,  -- LAG 00010000
  ⟨0, 6, ![false, false, false, false, true, false, false, false], ![1, 3, 4]⟩,  -- LAG 00001000
  ⟨0, 6, ![true, true, true, true, false, true, true, true], ![1, 3, 4]⟩,  -- LAG 11110111
  ⟨0, 6, ![true, true, true, false, true, true, true, true], ![0, 4, 6]⟩,  -- LAG 11101111
  ⟨1, 3, ![true, false, false, false, false, false, false, false], ![0, 1, 4]⟩,  -- LBD 10000000
  ⟨1, 3, ![false, true, true, true, true, true, true, true], ![0, 1, 4]⟩,  -- LBD 01111111
  ⟨1, 4, ![true, false, false, false, false, false, false, false], ![0, 1, 4]⟩,  -- LBE 10000000
  ⟨1, 4, ![false, false, false, false, false, true, false, false], ![1, 3, 5]⟩,  -- LBE 00000100
  ⟨1, 4, ![true, true, true, true, true, false, true, true], ![1, 3, 5]⟩,  -- LBE 11111011
  ⟨1, 4, ![false, true, true, true, true, true, true, true], ![0, 1, 4]⟩,  -- LBE 01111111
  ⟨1, 7, ![false, false, false, false, false, true, false, false], ![1, 3, 5]⟩,  -- LBH 00000100
  ⟨1, 7, ![true, true, true, true, true, false, true, true], ![1, 3, 5]⟩,  -- LBH 11111011
  ⟨2, 5, ![false, true, false, false, false, false, false, false], ![0, 1, 5]⟩,  -- LCF 01000000
  ⟨2, 5, ![true, true, true, true, true, true, true, false], ![2, 3, 5]⟩,  -- LCF 11111110
  ⟨2, 5, ![false, false, false, false, false, false, false, true], ![2, 3, 5]⟩,  -- LCF 00000001
  ⟨2, 5, ![true, false, true, true, true, true, true, true], ![0, 1, 5]⟩,  -- LCF 10111111
  ⟨2, 6, ![false, false, false, true, false, false, false, false], ![0, 4, 6]⟩,  -- LCG 00010000
  ⟨2, 6, ![true, true, true, true, true, true, true, false], ![2, 3, 5]⟩,  -- LCG 11111110
  ⟨2, 6, ![false, false, false, false, false, false, false, true], ![2, 3, 5]⟩,  -- LCG 00000001
  ⟨2, 6, ![true, true, true, false, true, true, true, true], ![0, 4, 6]⟩,  -- LCG 11101111
  ⟨3, 4, ![true, false, false, false, false, false, false, false], ![0, 1, 4]⟩,  -- LDE 10000000
  ⟨3, 4, ![false, true, true, true, true, true, true, true], ![0, 1, 4]⟩,  -- LDE 01111111
  ⟨4, 7, ![false, false, false, false, false, true, false, false], ![1, 3, 5]⟩,  -- LEH 00000100
  ⟨4, 7, ![true, true, true, true, true, false, true, true], ![1, 3, 5]⟩,  -- LEH 11111011
  ⟨5, 6, ![false, false, false, false, true, false, false, false], ![1, 3, 4]⟩,  -- LFG 00001000
  ⟨5, 6, ![true, true, true, true, true, true, true, false], ![2, 3, 5]⟩,  -- LFG 11111110
  ⟨5, 6, ![false, false, false, false, false, false, false, true], ![2, 3, 5]⟩,  -- LFG 00000001
  ⟨5, 6, ![true, true, true, true, false, true, true, true], ![1, 3, 4]⟩  -- LFG 11110111
]

def h21t2_lin4 : List (h21b_LinSpec 4) := [
  ⟨0, 1, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LAB 00001100
  ⟨0, 1, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LAB 11001100
  ⟨0, 1, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LAB 00110011
  ⟨0, 1, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LAB 11110011
  ⟨0, 2, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LAC 11000000
  ⟨0, 2, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LAC 10010000
  ⟨0, 2, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LAC 01000100
  ⟨0, 2, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LAC 10111011
  ⟨0, 2, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LAC 01101111
  ⟨0, 2, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LAC 00111111
  ⟨0, 4, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LAE 01000100
  ⟨0, 4, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LAE 11001100
  ⟨0, 4, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LAE 00110011
  ⟨0, 4, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LAE 10111011
  ⟨0, 5, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LAF 11000000
  ⟨0, 5, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LAF 10001000
  ⟨0, 5, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LAF 01000100
  ⟨0, 5, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LAF 00001100
  ⟨0, 5, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LAF 11110011
  ⟨0, 5, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LAF 10111011
  ⟨0, 5, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LAF 01110111
  ⟨0, 5, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LAF 00111111
  ⟨0, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LAG 10010000
  ⟨0, 6, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LAG 10001000
  ⟨0, 6, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LAG 00001100
  ⟨0, 6, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LAG 11110011
  ⟨0, 6, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LAG 01110111
  ⟨0, 6, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LAG 01101111
  ⟨0, 7, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LAH 01000100
  ⟨0, 7, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LAH 00001100
  ⟨0, 7, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LAH 11110011
  ⟨0, 7, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LAH 10111011
  ⟨1, 2, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LBC 10010000
  ⟨1, 2, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LBC 11111010
  ⟨1, 2, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LBC 00000101
  ⟨1, 2, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LBC 01101111
  ⟨1, 3, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LBD 11000000
  ⟨1, 3, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LBD 00100000
  ⟨1, 3, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LBD 10010000
  ⟨1, 3, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LBD 10001000
  ⟨1, 3, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LBD 01110111
  ⟨1, 3, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LBD 01101111
  ⟨1, 3, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- LBD 11011111
  ⟨1, 3, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LBD 00111111
  ⟨1, 4, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LBE 11000000
  ⟨1, 4, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LBE 10010000
  ⟨1, 4, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LBE 10001000
  ⟨1, 4, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LBE 01000100
  ⟨1, 4, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LBE 00001100
  ⟨1, 4, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LBE 11111010
  ⟨1, 4, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LBE 00000101
  ⟨1, 4, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LBE 11110011
  ⟨1, 4, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LBE 10111011
  ⟨1, 4, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LBE 01110111
  ⟨1, 4, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LBE 01101111
  ⟨1, 4, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LBE 00111111
  ⟨1, 5, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LBF 10001000
  ⟨1, 5, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LBF 11001100
  ⟨1, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LBF 00110011
  ⟨1, 5, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LBF 01110111
  ⟨1, 6, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LBG 00100000
  ⟨1, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LBG 10010000
  ⟨1, 6, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LBG 10001000
  ⟨1, 6, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LBG 00001100
  ⟨1, 6, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LBG 11001100
  ⟨1, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LBG 11111010
  ⟨1, 6, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LBG 00000101
  ⟨1, 6, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LBG 00110011
  ⟨1, 6, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LBG 11110011
  ⟨1, 6, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LBG 01110111
  ⟨1, 6, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LBG 01101111
  ⟨1, 6, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- LBG 11011111
  ⟨1, 7, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LBH 00100000
  ⟨1, 7, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LBH 01000100
  ⟨1, 7, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LBH 00001100
  ⟨1, 7, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LBH 11111010
  ⟨1, 7, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LBH 00000101
  ⟨1, 7, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LBH 11110011
  ⟨1, 7, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LBH 10111011
  ⟨1, 7, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- LBH 11011111
  ⟨2, 3, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LCD 11000000
  ⟨2, 3, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LCD 11001100
  ⟨2, 3, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LCD 00000010
  ⟨2, 3, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LCD 11111101
  ⟨2, 3, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LCD 00111111
  ⟨2, 4, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LCE 11000000
  ⟨2, 4, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LCE 10010000
  ⟨2, 4, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LCE 01000100
  ⟨2, 4, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LCE 11001100
  ⟨2, 4, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LCE 00000010
  ⟨2, 4, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LCE 11111010
  ⟨2, 4, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LCE 00000101
  ⟨2, 4, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LCE 11111101
  ⟨2, 4, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LCE 00110011
  ⟨2, 4, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LCE 10111011
  ⟨2, 4, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LCE 01101111
  ⟨2, 4, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LCE 00111111
  ⟨2, 5, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LCF 11000000
  ⟨2, 5, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LCF 01000100
  ⟨2, 5, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LCF 11111010
  ⟨2, 5, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LCF 00000101
  ⟨2, 5, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LCF 10111011
  ⟨2, 5, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LCF 00111111
  ⟨2, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LCG 10010000
  ⟨2, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LCG 11111010
  ⟨2, 6, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LCG 00000101
  ⟨2, 6, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LCG 01101111
  ⟨2, 7, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LCH 01000100
  ⟨2, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LCH 11001100
  ⟨2, 7, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LCH 00000010
  ⟨2, 7, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LCH 11111101
  ⟨2, 7, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LCH 10111011
  ⟨3, 4, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LDE 11000000
  ⟨3, 4, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LDE 10010000
  ⟨3, 4, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LDE 10001000
  ⟨3, 4, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LDE 00000010
  ⟨3, 4, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LDE 11111101
  ⟨3, 4, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LDE 01110111
  ⟨3, 4, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LDE 01101111
  ⟨3, 4, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LDE 00111111
  ⟨3, 5, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LDF 11000000
  ⟨3, 5, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LDF 10001000
  ⟨3, 5, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LDF 01110111
  ⟨3, 5, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LDF 00111111
  ⟨3, 6, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LDG 00100000
  ⟨3, 6, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LDG 10001000
  ⟨3, 6, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LDG 00110011
  ⟨3, 6, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LDG 01110111
  ⟨3, 6, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- LDG 11011111
  ⟨3, 7, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LDH 00100000
  ⟨3, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LDH 11001100
  ⟨3, 7, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LDH 00000010
  ⟨3, 7, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LDH 11111101
  ⟨3, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LDH 00110011
  ⟨3, 7, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- LDH 11011111
  ⟨4, 5, ![true, true, false, false, false, false, false, false], ![0, 4, 1, 5]⟩,  -- LEF 11000000
  ⟨4, 5, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LEF 11001100
  ⟨4, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LEF 00110011
  ⟨4, 5, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- LEF 00111111
  ⟨4, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- LEG 10010000
  ⟨4, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LEG 11111010
  ⟨4, 6, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LEG 00000101
  ⟨4, 6, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- LEG 01101111
  ⟨4, 7, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- LEH 01000100
  ⟨4, 7, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LEH 00001100
  ⟨4, 7, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- LEH 00000010
  ⟨4, 7, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LEH 11111010
  ⟨4, 7, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LEH 00000101
  ⟨4, 7, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- LEH 11111101
  ⟨4, 7, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LEH 11110011
  ⟨4, 7, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- LEH 10111011
  ⟨5, 6, ![true, false, false, false, true, false, false, false], ![0, 1, 3, 4]⟩,  -- LFG 10001000
  ⟨5, 6, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LFG 00001100
  ⟨5, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- LFG 11111010
  ⟨5, 6, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- LFG 00000101
  ⟨5, 6, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LFG 11110011
  ⟨5, 6, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- LFG 01110111
  ⟨6, 7, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- LGH 00100000
  ⟨6, 7, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- LGH 00001100
  ⟨6, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LGH 11001100
  ⟨6, 7, ![true, true, true, true, false, false, true, true], ![1, 4, 3, 5]⟩,  -- LGH 11110011
  ⟨6, 7, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩  -- LGH 11011111
]

def h21t2_lin5 : List (h21b_LinSpec 5) := [
  ⟨0, 1, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LAB 00110000
  ⟨0, 1, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LAB 11110000
  ⟨0, 1, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LAB 00110010
  ⟨0, 1, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LAB 11110010
  ⟨0, 1, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LAB 00001101
  ⟨0, 1, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LAB 11001101
  ⟨0, 1, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LAB 00001111
  ⟨0, 1, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LAB 11001111
  ⟨0, 2, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LAC 01100000
  ⟨0, 2, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LAC 00110000
  ⟨0, 2, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LAC 11000100
  ⟨0, 2, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LAC 01001100
  ⟨0, 2, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LAC 00010010
  ⟨0, 2, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LAC 00110010
  ⟨0, 2, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LAC 11001101
  ⟨0, 2, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LAC 11101101
  ⟨0, 2, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LAC 10110011
  ⟨0, 2, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LAC 00111011
  ⟨0, 2, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LAC 11001111
  ⟨0, 2, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LAC 10011111
  ⟨0, 3, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LAD 01100000
  ⟨0, 3, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LAD 11110000
  ⟨0, 3, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LAD 00001010
  ⟨0, 3, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LAD 10011010
  ⟨0, 3, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LAD 01100101
  ⟨0, 3, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LAD 11110101
  ⟨0, 3, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LAD 00001111
  ⟨0, 3, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LAD 10011111
  ⟨0, 4, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LAE 00010010
  ⟨0, 4, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LAE 00110010
  ⟨0, 4, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LAE 10011010
  ⟨0, 4, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LAE 10111010
  ⟨0, 4, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LAE 01000101
  ⟨0, 4, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LAE 01100101
  ⟨0, 4, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LAE 11001101
  ⟨0, 4, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LAE 11101101
  ⟨0, 5, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LAF 01100000
  ⟨0, 5, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LAF 11000100
  ⟨0, 5, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LAF 10001100
  ⟨0, 5, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LAF 00001010
  ⟨0, 5, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LAF 01100101
  ⟨0, 5, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LAF 11110101
  ⟨0, 5, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LAF 01110011
  ⟨0, 5, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LAF 00111011
  ⟨0, 5, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LAF 00001111
  ⟨0, 5, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LAF 10011111
  ⟨0, 6, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LAG 00110000
  ⟨0, 6, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LAG 10001100
  ⟨0, 6, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LAG 01001100
  ⟨0, 6, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LAG 00010010
  ⟨0, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LAG 00110010
  ⟨0, 6, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LAG 00001010
  ⟨0, 6, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LAG 11110101
  ⟨0, 6, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LAG 11001101
  ⟨0, 6, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LAG 11101101
  ⟨0, 6, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LAG 10110011
  ⟨0, 6, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LAG 01110011
  ⟨0, 6, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LAG 11001111
  ⟨0, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LAH 01100000
  ⟨0, 7, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LAH 00110000
  ⟨0, 7, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LAH 11000100
  ⟨0, 7, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LAH 10001100
  ⟨0, 7, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LAH 00010010
  ⟨0, 7, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LAH 00110010
  ⟨0, 7, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LAH 11110010
  ⟨0, 7, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LAH 00001010
  ⟨0, 7, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LAH 10111010
  ⟨0, 7, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LAH 01000101
  ⟨0, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LAH 11110101
  ⟨0, 7, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LAH 00001101
  ⟨0, 7, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LAH 11001101
  ⟨0, 7, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LAH 11101101
  ⟨0, 7, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LAH 10110011
  ⟨0, 7, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LAH 01110011
  ⟨0, 7, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LAH 00111011
  ⟨0, 7, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LAH 11001111
  ⟨0, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LAH 10011111
  ⟨1, 2, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LBC 11110000
  ⟨1, 2, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LBC 10011000
  ⟨1, 2, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LBC 11110010
  ⟨1, 2, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LBC 10011010
  ⟨1, 2, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LBC 01100101
  ⟨1, 2, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LBC 00001101
  ⟨1, 2, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LBC 01100111
  ⟨1, 2, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LBC 00001111
  ⟨1, 3, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LBD 01100000
  ⟨1, 3, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LBD 11010000
  ⟨1, 3, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LBD 00110000
  ⟨1, 3, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LBD 11001000
  ⟨1, 3, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LBD 10011000
  ⟨1, 3, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LBD 10001100
  ⟨1, 3, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LBD 11011100
  ⟨1, 3, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LBD 00110010
  ⟨1, 3, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LBD 10011010
  ⟨1, 3, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LBD 11011110
  ⟨1, 3, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LBD 00100001
  ⟨1, 3, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LBD 01100101
  ⟨1, 3, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LBD 11001101
  ⟨1, 3, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LBD 01100111
  ⟨1, 3, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LBD 00110111
  ⟨1, 3, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LBD 11001111
  ⟨1, 3, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LBD 00101111
  ⟨1, 3, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LBD 10011111
  ⟨1, 4, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LBE 11010000
  ⟨1, 4, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LBE 11001000
  ⟨1, 4, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LBE 10011000
  ⟨1, 4, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LBE 01001100
  ⟨1, 4, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LBE 11110010
  ⟨1, 4, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LBE 10111010
  ⟨1, 4, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LBE 01000101
  ⟨1, 4, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LBE 00001101
  ⟨1, 4, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LBE 10110011
  ⟨1, 4, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LBE 01100111
  ⟨1, 4, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LBE 00110111
  ⟨1, 4, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LBE 00101111
  ⟨1, 5, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LBF 10011000
  ⟨1, 5, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LBF 11011100
  ⟨1, 5, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LBF 10011010
  ⟨1, 5, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LBF 11011110
  ⟨1, 5, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LBF 00100001
  ⟨1, 5, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LBF 01100101
  ⟨1, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LBF 00100011
  ⟨1, 5, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LBF 01100111
  ⟨1, 6, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LBG 01100000
  ⟨1, 6, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LBG 11010000
  ⟨1, 6, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LBG 00110000
  ⟨1, 6, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LBG 11001000
  ⟨1, 6, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LBG 10011000
  ⟨1, 6, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LBG 10001100
  ⟨1, 6, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LBG 01001100
  ⟨1, 6, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LBG 11011100
  ⟨1, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LBG 00110010
  ⟨1, 6, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LBG 11110010
  ⟨1, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LBG 10111010
  ⟨1, 6, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LBG 11011110
  ⟨1, 6, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LBG 00100001
  ⟨1, 6, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LBG 01000101
  ⟨1, 6, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LBG 00001101
  ⟨1, 6, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LBG 11001101
  ⟨1, 6, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LBG 00100011
  ⟨1, 6, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LBG 10110011
  ⟨1, 6, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LBG 01110011
  ⟨1, 6, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LBG 01100111
  ⟨1, 6, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LBG 00110111
  ⟨1, 6, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LBG 11001111
  ⟨1, 6, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LBG 00101111
  ⟨1, 6, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LBG 10011111
  ⟨1, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LBH 01100000
  ⟨1, 7, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LBH 00110000
  ⟨1, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LBH 11110000
  ⟨1, 7, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LBH 10001100
  ⟨1, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LBH 01001100
  ⟨1, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LBH 11011100
  ⟨1, 7, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LBH 11110010
  ⟨1, 7, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LBH 10111010
  ⟨1, 7, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LBH 11011110
  ⟨1, 7, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LBH 00100001
  ⟨1, 7, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LBH 01000101
  ⟨1, 7, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LBH 00001101
  ⟨1, 7, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LBH 11001101
  ⟨1, 7, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LBH 00100011
  ⟨1, 7, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LBH 10110011
  ⟨1, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LBH 00001111
  ⟨1, 7, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LBH 11001111
  ⟨1, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LBH 10011111
  ⟨2, 3, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LCD 11110000
  ⟨2, 3, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LCD 11001000
  ⟨2, 3, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LCD 11000100
  ⟨2, 3, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LCD 11111100
  ⟨2, 3, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LCD 00110010
  ⟨2, 3, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LCD 00001010
  ⟨2, 3, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LCD 11110101
  ⟨2, 3, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LCD 11001101
  ⟨2, 3, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LCD 00000011
  ⟨2, 3, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LCD 00111011
  ⟨2, 3, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LCD 00110111
  ⟨2, 3, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LCD 00001111
  ⟨2, 4, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LCE 11010000
  ⟨2, 4, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LCE 11001000
  ⟨2, 4, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LCE 10011000
  ⟨2, 4, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LCE 11000100
  ⟨2, 4, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LCE 01001100
  ⟨2, 4, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LCE 11011100
  ⟨2, 4, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LCE 11111100
  ⟨2, 4, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LCE 00010010
  ⟨2, 4, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LCE 00110010
  ⟨2, 4, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LCE 11110010
  ⟨2, 4, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LCE 00001010
  ⟨2, 4, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LCE 10111010
  ⟨2, 4, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LCE 01000101
  ⟨2, 4, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LCE 11110101
  ⟨2, 4, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LCE 00001101
  ⟨2, 4, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LCE 11001101
  ⟨2, 4, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LCE 11101101
  ⟨2, 4, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LCE 00000011
  ⟨2, 4, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LCE 00100011
  ⟨2, 4, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LCE 10110011
  ⟨2, 4, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LCE 00111011
  ⟨2, 4, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LCE 01100111
  ⟨2, 4, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LCE 00110111
  ⟨2, 4, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LCE 00101111
  ⟨2, 5, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LCF 01100000
  ⟨2, 5, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LCF 11001000
  ⟨2, 5, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LCF 11000100
  ⟨2, 5, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LCF 11011100
  ⟨2, 5, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LCF 11111100
  ⟨2, 5, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LCF 11011110
  ⟨2, 5, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LCF 00100001
  ⟨2, 5, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LCF 00000011
  ⟨2, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LCF 00100011
  ⟨2, 5, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LCF 00111011
  ⟨2, 5, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LCF 00110111
  ⟨2, 5, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LCF 10011111
  ⟨2, 6, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LCG 11010000
  ⟨2, 6, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LCG 11011100
  ⟨2, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LCG 00110010
  ⟨2, 6, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LCG 11110010
  ⟨2, 6, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LCG 01000101
  ⟨2, 6, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LCG 11001101
  ⟨2, 6, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LCG 00100011
  ⟨2, 6, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LCG 01100111
  ⟨2, 7, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LCH 11000100
  ⟨2, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LCH 01001100
  ⟨2, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LCH 11011100
  ⟨2, 7, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LCH 00010010
  ⟨2, 7, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LCH 00001010
  ⟨2, 7, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LCH 10011010
  ⟨2, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LCH 01100101
  ⟨2, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LCH 11110101
  ⟨2, 7, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LCH 11101101
  ⟨2, 7, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LCH 00100011
  ⟨2, 7, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LCH 10110011
  ⟨2, 7, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LCH 00111011
  ⟨3, 4, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LDE 11010000
  ⟨3, 4, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LDE 11110000
  ⟨3, 4, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LDE 11001000
  ⟨3, 4, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LDE 10011000
  ⟨3, 4, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LDE 11111100
  ⟨3, 4, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LDE 00010010
  ⟨3, 4, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LDE 00110010
  ⟨3, 4, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LDE 00001010
  ⟨3, 4, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LDE 11110101
  ⟨3, 4, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LDE 11001101
  ⟨3, 4, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LDE 11101101
  ⟨3, 4, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LDE 00000011
  ⟨3, 4, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LDE 00100011
  ⟨3, 4, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LDE 00111011
  ⟨3, 4, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LDE 01100111
  ⟨3, 4, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LDE 00110111
  ⟨3, 4, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LDE 00001111
  ⟨3, 4, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LDE 00101111
  ⟨3, 5, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LDF 01100000
  ⟨3, 5, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LDF 11010000
  ⟨3, 5, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LDF 11001000
  ⟨3, 5, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LDF 10011000
  ⟨3, 5, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LDF 11000100
  ⟨3, 5, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LDF 10001100
  ⟨3, 5, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LDF 11011100
  ⟨3, 5, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LDF 11111100
  ⟨3, 5, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LDF 00001010
  ⟨3, 5, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LDF 11011110
  ⟨3, 5, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LDF 00100001
  ⟨3, 5, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LDF 11110101
  ⟨3, 5, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LDF 00000011
  ⟨3, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LDF 00100011
  ⟨3, 5, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LDF 01110011
  ⟨3, 5, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LDF 00111011
  ⟨3, 5, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LDF 01100111
  ⟨3, 5, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LDF 00101111
  ⟨3, 5, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LDF 10011111
  ⟨3, 6, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LDG 01100000
  ⟨3, 6, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LDG 11001000
  ⟨3, 6, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LDG 10001100
  ⟨3, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LDG 00110010
  ⟨3, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LDG 10011010
  ⟨3, 6, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LDG 11011110
  ⟨3, 6, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LDG 00100001
  ⟨3, 6, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LDG 01100101
  ⟨3, 6, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LDG 11001101
  ⟨3, 6, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LDG 01110011
  ⟨3, 6, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LDG 00110111
  ⟨3, 6, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LDG 10011111
  ⟨3, 7, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LDH 00110000
  ⟨3, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LDH 11110000
  ⟨3, 7, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LDH 11000100
  ⟨3, 7, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LDH 10001100
  ⟨3, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LDH 11011100
  ⟨3, 7, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LDH 11111100
  ⟨3, 7, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LDH 00010010
  ⟨3, 7, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LDH 00110010
  ⟨3, 7, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LDH 10011010
  ⟨3, 7, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LDH 11011110
  ⟨3, 7, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LDH 00100001
  ⟨3, 7, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LDH 11001101
  ⟨3, 7, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LDH 11101101
  ⟨3, 7, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LDH 00000011
  ⟨3, 7, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LDH 00100011
  ⟨3, 7, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LDH 01110011
  ⟨3, 7, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LDH 00111011
  ⟨3, 7, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LDH 11001111
  ⟨4, 5, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LEF 11010000
  ⟨4, 5, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LEF 11110000
  ⟨4, 5, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LEF 11011100
  ⟨4, 5, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LEF 11111100
  ⟨4, 5, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LEF 00000011
  ⟨4, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LEF 00100011
  ⟨4, 5, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LEF 00001111
  ⟨4, 5, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LEF 00101111
  ⟨4, 6, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LEG 11010000
  ⟨4, 6, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LEG 11110000
  ⟨4, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LEG 10011010
  ⟨4, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LEG 10111010
  ⟨4, 6, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LEG 01000101
  ⟨4, 6, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LEG 01100101
  ⟨4, 6, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LEG 00001111
  ⟨4, 6, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LEG 00101111
  ⟨4, 7, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LEH 11000100
  ⟨4, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LEH 01001100
  ⟨4, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LEH 11011100
  ⟨4, 7, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LEH 11111100
  ⟨4, 7, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- LEH 00010010
  ⟨4, 7, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LEH 11110010
  ⟨4, 7, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LEH 00001010
  ⟨4, 7, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LEH 10011010
  ⟨4, 7, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LEH 10111010
  ⟨4, 7, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LEH 01000101
  ⟨4, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LEH 01100101
  ⟨4, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LEH 11110101
  ⟨4, 7, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LEH 00001101
  ⟨4, 7, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- LEH 11001101
  ⟨4, 7, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- LEH 11101101
  ⟨4, 7, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LEH 00000011
  ⟨4, 7, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LEH 00100011
  ⟨4, 7, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LEH 10110011
  ⟨5, 6, ![true, true, false, false, true, false, false, false], ![0, 4, 3, 1, 5]⟩,  -- LFG 11001000
  ⟨5, 6, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LFG 10001100
  ⟨5, 6, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LFG 11011100
  ⟨5, 6, ![true, true, true, true, true, true, false, false], ![2, 5, 3, 4, 6]⟩,  -- LFG 11111100
  ⟨5, 6, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LFG 00001010
  ⟨5, 6, ![true, true, false, true, true, true, true, false], ![0, 5, 3, 2, 6]⟩,  -- LFG 11011110
  ⟨5, 6, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- LFG 00100001
  ⟨5, 6, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LFG 11110101
  ⟨5, 6, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- LFG 00000011
  ⟨5, 6, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LFG 00100011
  ⟨5, 6, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LFG 01110011
  ⟨5, 6, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LFG 00110111
  ⟨5, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LFH 01100000
  ⟨5, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LFH 11110000
  ⟨5, 7, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LFH 00001010
  ⟨5, 7, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LFH 10011010
  ⟨5, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LFH 01100101
  ⟨5, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LFH 11110101
  ⟨5, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LFH 00001111
  ⟨5, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LFH 10011111
  ⟨6, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LGH 01100000
  ⟨6, 7, ![false, false, true, true, false, false, false, false], ![0, 4, 6, 2, 5]⟩,  -- LGH 00110000
  ⟨6, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LGH 11110000
  ⟨6, 7, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- LGH 10001100
  ⟨6, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LGH 01001100
  ⟨6, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LGH 11011100
  ⟨6, 7, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LGH 00100011
  ⟨6, 7, ![true, false, true, true, false, false, true, true], ![0, 1, 4, 3, 5]⟩,  -- LGH 10110011
  ⟨6, 7, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LGH 01110011
  ⟨6, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LGH 00001111
  ⟨6, 7, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- LGH 11001111
  ⟨6, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩  -- LGH 10011111
]

def h21t2_lin6 : List (h21b_LinSpec 6) := [
  ⟨0, 1, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LAB 00001110
  ⟨0, 1, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LAB 11001110
  ⟨0, 1, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LAB 00110001
  ⟨0, 1, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LAB 11110001
  ⟨0, 2, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LAC 11100000
  ⟨0, 2, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LAC 10110000
  ⟨0, 2, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LAC 01100100
  ⟨0, 2, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LAC 11101100
  ⟨0, 2, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LAC 10010010
  ⟨0, 2, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LAC 10110010
  ⟨0, 2, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LAC 00011010
  ⟨0, 2, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LAC 00111010
  ⟨0, 2, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LAC 11000101
  ⟨0, 2, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LAC 01001101
  ⟨0, 2, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LAC 01101101
  ⟨0, 2, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LAC 00010011
  ⟨0, 2, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LAC 10011011
  ⟨0, 2, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LAC 01001111
  ⟨0, 2, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LAC 00011111
  ⟨0, 3, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LAD 01100100
  ⟨0, 3, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LAD 11110100
  ⟨0, 3, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LAD 00001110
  ⟨0, 3, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LAD 10011110
  ⟨0, 3, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LAD 01100001
  ⟨0, 3, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LAD 11110001
  ⟨0, 3, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LAD 00001011
  ⟨0, 3, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LAD 10011011
  ⟨0, 4, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LAE 01100100
  ⟨0, 4, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LAE 11101100
  ⟨0, 4, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LAE 00010011
  ⟨0, 4, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LAE 10011011
  ⟨0, 5, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LAF 11100000
  ⟨0, 5, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LAF 01100100
  ⟨0, 5, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LAF 10001010
  ⟨0, 5, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LAF 00001110
  ⟨0, 5, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LAF 01100001
  ⟨0, 5, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LAF 11110001
  ⟨0, 5, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LAF 11100101
  ⟨0, 5, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LAF 01110101
  ⟨0, 5, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LAF 00001011
  ⟨0, 5, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LAF 10011011
  ⟨0, 5, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LAF 10001111
  ⟨0, 5, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LAF 00011111
  ⟨0, 6, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LAG 10110000
  ⟨0, 6, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LAG 01110000
  ⟨0, 6, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LAG 10010010
  ⟨0, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LAG 10110010
  ⟨0, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LAG 01110010
  ⟨0, 6, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LAG 10001010
  ⟨0, 6, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LAG 00001110
  ⟨0, 6, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LAG 11001110
  ⟨0, 6, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LAG 00110001
  ⟨0, 6, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LAG 11110001
  ⟨0, 6, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LAG 01110101
  ⟨0, 6, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LAG 10001101
  ⟨0, 6, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LAG 01001101
  ⟨0, 6, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LAG 01101101
  ⟨0, 6, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LAG 01001111
  ⟨0, 7, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LAH 11100000
  ⟨0, 7, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LAH 10110000
  ⟨0, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LAH 01110000
  ⟨0, 7, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LAH 01100100
  ⟨0, 7, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LAH 11110100
  ⟨0, 7, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LAH 11101100
  ⟨0, 7, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LAH 10010010
  ⟨0, 7, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LAH 10110010
  ⟨0, 7, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LAH 01110010
  ⟨0, 7, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LAH 10001010
  ⟨0, 7, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LAH 00011010
  ⟨0, 7, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LAH 00111010
  ⟨0, 7, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LAH 00001110
  ⟨0, 7, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LAH 11001110
  ⟨0, 7, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LAH 10011110
  ⟨0, 7, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LAH 01100001
  ⟨0, 7, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LAH 00110001
  ⟨0, 7, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LAH 11110001
  ⟨0, 7, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LAH 11000101
  ⟨0, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LAH 11100101
  ⟨0, 7, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LAH 01110101
  ⟨0, 7, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LAH 10001101
  ⟨0, 7, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LAH 01001101
  ⟨0, 7, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LAH 01101101
  ⟨0, 7, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LAH 00010011
  ⟨0, 7, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LAH 00001011
  ⟨0, 7, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LAH 10011011
  ⟨0, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LAH 10001111
  ⟨0, 7, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LAH 01001111
  ⟨0, 7, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LAH 00011111
  ⟨1, 2, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LBC 11111000
  ⟨1, 2, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LBC 10010010
  ⟨1, 2, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LBC 01101101
  ⟨1, 2, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LBC 00000111
  ⟨1, 3, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LBD 01110000
  ⟨1, 3, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LBD 11011000
  ⟨1, 3, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LBD 10011100
  ⟨1, 3, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LBD 00100010
  ⟨1, 3, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LBD 01110010
  ⟨1, 3, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LBD 10001010
  ⟨1, 3, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LBD 11011010
  ⟨1, 3, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LBD 11001110
  ⟨1, 3, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LBD 10011110
  ⟨1, 3, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LBD 01100001
  ⟨1, 3, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LBD 00110001
  ⟨1, 3, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LBD 00100101
  ⟨1, 3, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LBD 01110101
  ⟨1, 3, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LBD 10001101
  ⟨1, 3, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LBD 11011101
  ⟨1, 3, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LBD 01100011
  ⟨1, 3, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LBD 00100111
  ⟨1, 3, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LBD 10001111
  ⟨1, 4, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LBE 10110000
  ⟨1, 4, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LBE 11011000
  ⟨1, 4, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LBE 11111000
  ⟨1, 4, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LBE 10010010
  ⟨1, 4, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LBE 10110010
  ⟨1, 4, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LBE 11011010
  ⟨1, 4, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LBE 00100101
  ⟨1, 4, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LBE 01001101
  ⟨1, 4, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LBE 01101101
  ⟨1, 4, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LBE 00000111
  ⟨1, 4, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LBE 00100111
  ⟨1, 4, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LBE 01001111
  ⟨1, 5, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LBF 10001010
  ⟨1, 5, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LBF 11001110
  ⟨1, 5, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LBF 00110001
  ⟨1, 5, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LBF 01110101
  ⟨1, 6, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LBG 10110000
  ⟨1, 6, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LBG 01110000
  ⟨1, 6, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LBG 11011000
  ⟨1, 6, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LBG 11111000
  ⟨1, 6, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LBG 10011100
  ⟨1, 6, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LBG 00100010
  ⟨1, 6, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LBG 10010010
  ⟨1, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LBG 10110010
  ⟨1, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LBG 01110010
  ⟨1, 6, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LBG 10001010
  ⟨1, 6, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LBG 11011010
  ⟨1, 6, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LBG 00001110
  ⟨1, 6, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LBG 11001110
  ⟨1, 6, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LBG 10011110
  ⟨1, 6, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LBG 01100001
  ⟨1, 6, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LBG 00110001
  ⟨1, 6, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LBG 11110001
  ⟨1, 6, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LBG 00100101
  ⟨1, 6, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LBG 01110101
  ⟨1, 6, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LBG 10001101
  ⟨1, 6, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LBG 01001101
  ⟨1, 6, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LBG 01101101
  ⟨1, 6, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LBG 11011101
  ⟨1, 6, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LBG 01100011
  ⟨1, 6, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LBG 00000111
  ⟨1, 6, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LBG 00100111
  ⟨1, 6, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LBG 10001111
  ⟨1, 6, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LBG 01001111
  ⟨1, 7, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LBH 10110000
  ⟨1, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LBH 01110000
  ⟨1, 7, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LBH 10011100
  ⟨1, 7, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LBH 00100010
  ⟨1, 7, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LBH 10110010
  ⟨1, 7, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LBH 01110010
  ⟨1, 7, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LBH 00001110
  ⟨1, 7, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LBH 11001110
  ⟨1, 7, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LBH 10011110
  ⟨1, 7, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LBH 01100001
  ⟨1, 7, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LBH 00110001
  ⟨1, 7, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LBH 11110001
  ⟨1, 7, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LBH 10001101
  ⟨1, 7, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LBH 01001101
  ⟨1, 7, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LBH 11011101
  ⟨1, 7, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LBH 01100011
  ⟨1, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LBH 10001111
  ⟨1, 7, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LBH 01001111
  ⟨2, 3, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LCD 11111000
  ⟨2, 3, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LCD 11110100
  ⟨2, 3, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LCD 00111010
  ⟨2, 3, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LCD 11000101
  ⟨2, 3, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LCD 00001011
  ⟨2, 3, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LCD 00000111
  ⟨2, 4, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LCE 11100000
  ⟨2, 4, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LCE 10110000
  ⟨2, 4, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LCE 11011000
  ⟨2, 4, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LCE 11111000
  ⟨2, 4, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LCE 01100100
  ⟨2, 4, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LCE 11010100
  ⟨2, 4, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LCE 11110100
  ⟨2, 4, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LCE 11101100
  ⟨2, 4, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LCE 00100010
  ⟨2, 4, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LCE 10010010
  ⟨2, 4, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LCE 10110010
  ⟨2, 4, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LCE 00011010
  ⟨2, 4, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LCE 11011010
  ⟨2, 4, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LCE 00111010
  ⟨2, 4, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LCE 11000101
  ⟨2, 4, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LCE 00100101
  ⟨2, 4, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LCE 11100101
  ⟨2, 4, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LCE 01001101
  ⟨2, 4, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LCE 01101101
  ⟨2, 4, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LCE 11011101
  ⟨2, 4, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LCE 00010011
  ⟨2, 4, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LCE 00001011
  ⟨2, 4, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LCE 00101011
  ⟨2, 4, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LCE 10011011
  ⟨2, 4, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LCE 00000111
  ⟨2, 4, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LCE 00100111
  ⟨2, 4, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LCE 01001111
  ⟨2, 4, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LCE 00011111
  ⟨2, 5, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LCF 11100000
  ⟨2, 5, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LCF 11011000
  ⟨2, 5, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LCF 11111000
  ⟨2, 5, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LCF 01100100
  ⟨2, 5, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LCF 11010100
  ⟨2, 5, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LCF 11110100
  ⟨2, 5, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LCF 11101100
  ⟨2, 5, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LCF 11011010
  ⟨2, 5, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LCF 00100101
  ⟨2, 5, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LCF 00010011
  ⟨2, 5, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LCF 00101011
  ⟨2, 5, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LCF 10011011
  ⟨2, 5, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LCF 00000111
  ⟨2, 5, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LCF 00100111
  ⟨2, 5, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LCF 00011111
  ⟨2, 6, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LCG 11011000
  ⟨2, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LCG 10110010
  ⟨2, 6, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LCG 01001101
  ⟨2, 6, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LCG 00100111
  ⟨2, 7, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LCH 11010100
  ⟨2, 7, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LCH 10010010
  ⟨2, 7, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LCH 00011010
  ⟨2, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LCH 11100101
  ⟨2, 7, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LCH 01101101
  ⟨2, 7, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LCH 00101011
  ⟨3, 4, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LDE 11100000
  ⟨3, 4, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LDE 11011000
  ⟨3, 4, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LDE 11111000
  ⟨3, 4, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LDE 11010100
  ⟨3, 4, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LDE 11110100
  ⟨3, 4, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LDE 11101100
  ⟨3, 4, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LDE 00100010
  ⟨3, 4, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LDE 00011010
  ⟨3, 4, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LDE 00111010
  ⟨3, 4, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LDE 11000101
  ⟨3, 4, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LDE 11100101
  ⟨3, 4, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LDE 11011101
  ⟨3, 4, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LDE 00010011
  ⟨3, 4, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LDE 00001011
  ⟨3, 4, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LDE 00101011
  ⟨3, 4, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LDE 00000111
  ⟨3, 4, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LDE 00100111
  ⟨3, 4, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LDE 00011111
  ⟨3, 5, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LDF 11100000
  ⟨3, 5, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LDF 01110000
  ⟨3, 5, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LDF 11011000
  ⟨3, 5, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LDF 11111000
  ⟨3, 5, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LDF 01100100
  ⟨3, 5, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LDF 11010100
  ⟨3, 5, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LDF 11110100
  ⟨3, 5, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LDF 11101100
  ⟨3, 5, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LDF 10011100
  ⟨3, 5, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LDF 10001010
  ⟨3, 5, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LDF 00011010
  ⟨3, 5, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LDF 11011010
  ⟨3, 5, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LDF 00001110
  ⟨3, 5, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LDF 11001110
  ⟨3, 5, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LDF 10011110
  ⟨3, 5, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LDF 01100001
  ⟨3, 5, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LDF 00110001
  ⟨3, 5, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LDF 11110001
  ⟨3, 5, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LDF 00100101
  ⟨3, 5, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LDF 11100101
  ⟨3, 5, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LDF 01110101
  ⟨3, 5, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LDF 01100011
  ⟨3, 5, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LDF 00010011
  ⟨3, 5, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LDF 00001011
  ⟨3, 5, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LDF 00101011
  ⟨3, 5, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LDF 10011011
  ⟨3, 5, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LDF 00000111
  ⟨3, 5, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LDF 00100111
  ⟨3, 5, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LDF 10001111
  ⟨3, 5, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LDF 00011111
  ⟨3, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LDG 01110010
  ⟨3, 6, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LDG 11011010
  ⟨3, 6, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LDG 10011110
  ⟨3, 6, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LDG 01100001
  ⟨3, 6, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LDG 00100101
  ⟨3, 6, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LDG 10001101
  ⟨3, 7, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LDH 11100000
  ⟨3, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LDH 01110000
  ⟨3, 7, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LDH 01100100
  ⟨3, 7, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LDH 11010100
  ⟨3, 7, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LDH 11110100
  ⟨3, 7, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LDH 11101100
  ⟨3, 7, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LDH 10011100
  ⟨3, 7, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LDH 00100010
  ⟨3, 7, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- LDH 01110010
  ⟨3, 7, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LDH 10001010
  ⟨3, 7, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LDH 00011010
  ⟨3, 7, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LDH 00111010
  ⟨3, 7, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LDH 00001110
  ⟨3, 7, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LDH 11001110
  ⟨3, 7, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LDH 10011110
  ⟨3, 7, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LDH 01100001
  ⟨3, 7, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LDH 00110001
  ⟨3, 7, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LDH 11110001
  ⟨3, 7, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LDH 11000101
  ⟨3, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LDH 11100101
  ⟨3, 7, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LDH 01110101
  ⟨3, 7, ![true, false, false, false, true, true, false, true], ![0, 1, 5, 2, 3, 4]⟩,  -- LDH 10001101
  ⟨3, 7, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LDH 11011101
  ⟨3, 7, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LDH 01100011
  ⟨3, 7, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LDH 00010011
  ⟨3, 7, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LDH 00001011
  ⟨3, 7, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LDH 00101011
  ⟨3, 7, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LDH 10011011
  ⟨3, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LDH 10001111
  ⟨3, 7, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LDH 00011111
  ⟨4, 5, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LEF 11100000
  ⟨4, 5, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LEF 11101100
  ⟨4, 5, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LEF 00010011
  ⟨4, 5, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LEF 00011111
  ⟨4, 6, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LEG 10110000
  ⟨4, 6, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LEG 11011010
  ⟨4, 6, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LEG 00100101
  ⟨4, 6, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- LEG 01001111
  ⟨4, 7, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- LEH 01100100
  ⟨4, 7, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- LEH 11010100
  ⟨4, 7, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LEH 11110100
  ⟨4, 7, ![true, true, true, false, true, true, false, false], ![0, 4, 3, 5, 2, 6]⟩,  -- LEH 11101100
  ⟨4, 7, ![false, false, true, false, false, false, true, false], ![0, 5, 2, 3, 4, 6]⟩,  -- LEH 00100010
  ⟨4, 7, ![true, false, false, true, false, false, true, false], ![0, 1, 4, 3, 2, 6]⟩,  -- LEH 10010010
  ⟨4, 7, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- LEH 10110010
  ⟨4, 7, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LEH 00011010
  ⟨4, 7, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- LEH 00111010
  ⟨4, 7, ![true, true, false, false, false, true, false, true], ![0, 4, 1, 3, 2, 5]⟩,  -- LEH 11000101
  ⟨4, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LEH 11100101
  ⟨4, 7, ![false, true, false, false, true, true, false, true], ![0, 1, 4, 3, 2, 5]⟩,  -- LEH 01001101
  ⟨4, 7, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- LEH 01101101
  ⟨4, 7, ![true, true, false, true, true, true, false, true], ![0, 5, 2, 3, 4, 6]⟩,  -- LEH 11011101
  ⟨4, 7, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- LEH 00010011
  ⟨4, 7, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LEH 00001011
  ⟨4, 7, ![false, false, true, false, true, false, true, true], ![0, 5, 3, 1, 4, 6]⟩,  -- LEH 00101011
  ⟨4, 7, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- LEH 10011011
  ⟨5, 6, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- LFG 11011000
  ⟨5, 6, ![true, true, true, true, true, false, false, false], ![1, 3, 4, 6, 2, 5]⟩,  -- LFG 11111000
  ⟨5, 6, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LFG 10011100
  ⟨5, 6, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LFG 10001010
  ⟨5, 6, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- LFG 11011010
  ⟨5, 6, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- LFG 00001110
  ⟨5, 6, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- LFG 11001110
  ⟨5, 6, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- LFG 01100001
  ⟨5, 6, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- LFG 00110001
  ⟨5, 6, ![true, true, true, true, false, false, false, true], ![1, 4, 6, 2, 3, 5]⟩,  -- LFG 11110001
  ⟨5, 6, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩,  -- LFG 00100101
  ⟨5, 6, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LFG 01110101
  ⟨5, 6, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LFG 01100011
  ⟨5, 6, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- LFG 00000111
  ⟨5, 6, ![false, false, true, false, false, true, true, true], ![0, 5, 1, 3, 4, 6]⟩,  -- LFG 00100111
  ⟨5, 7, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- LFH 11100000
  ⟨5, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LFH 01110000
  ⟨5, 7, ![true, false, false, false, true, false, true, false], ![0, 1, 3, 2, 6, 4]⟩,  -- LFH 10001010
  ⟨5, 7, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LFH 00011010
  ⟨5, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LFH 11100101
  ⟨5, 7, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- LFH 01110101
  ⟨5, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LFH 10001111
  ⟨5, 7, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- LFH 00011111
  ⟨6, 7, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- LGH 10110000
  ⟨6, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LGH 01110000
  ⟨6, 7, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- LGH 10011100
  ⟨6, 7, ![false, true, true, false, false, false, true, true], ![0, 1, 5, 3, 4, 6]⟩,  -- LGH 01100011
  ⟨6, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LGH 10001111
  ⟨6, 7, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩  -- LGH 01001111
]

def h21t2_lin7 : List (h21b_LinSpec 7) := [
  ⟨0, 2, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAC 11100100
  ⟨0, 2, ![false, true, true, false, true, true, false, false], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LAC 01101100
  ⟨0, 2, ![true, false, false, true, false, false, true, true], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LAC 10010011
  ⟨0, 2, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAC 00011011
  ⟨0, 5, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAF 11100100
  ⟨0, 5, ![false, true, true, true, false, true, false, false], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LAF 01110100
  ⟨0, 5, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAF 10001110
  ⟨0, 5, ![false, false, false, true, true, true, true, false], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LAF 00011110
  ⟨0, 5, ![true, true, true, false, false, false, false, true], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LAF 11100001
  ⟨0, 5, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAF 01110001
  ⟨0, 5, ![true, false, false, false, true, false, true, true], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LAF 10001011
  ⟨0, 5, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAF 00011011
  ⟨0, 6, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAG 10001110
  ⟨0, 6, ![false, true, false, false, true, true, true, false], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LAG 01001110
  ⟨0, 6, ![true, false, true, true, false, false, false, true], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LAG 10110001
  ⟨0, 6, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAG 01110001
  ⟨0, 7, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAH 11100100
  ⟨0, 7, ![false, true, true, true, false, true, false, false], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LAH 01110100
  ⟨0, 7, ![false, true, true, false, true, true, false, false], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LAH 01101100
  ⟨0, 7, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAH 10001110
  ⟨0, 7, ![false, true, false, false, true, true, true, false], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LAH 01001110
  ⟨0, 7, ![false, false, false, true, true, true, true, false], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LAH 00011110
  ⟨0, 7, ![true, true, true, false, false, false, false, true], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LAH 11100001
  ⟨0, 7, ![true, false, true, true, false, false, false, true], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LAH 10110001
  ⟨0, 7, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LAH 01110001
  ⟨0, 7, ![true, false, false, true, false, false, true, true], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LAH 10010011
  ⟨0, 7, ![true, false, false, false, true, false, true, true], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LAH 10001011
  ⟨0, 7, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LAH 00011011
  ⟨1, 3, ![false, true, true, false, false, false, true, false], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBD 01100010
  ⟨1, 3, ![true, true, false, false, true, false, true, false], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LBD 11001010
  ⟨1, 3, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBD 10001110
  ⟨1, 3, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBD 01110001
  ⟨1, 3, ![false, false, true, true, false, true, false, true], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LBD 00110101
  ⟨1, 3, ![true, false, false, true, true, true, false, true], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBD 10011101
  ⟨1, 4, ![true, false, true, true, true, false, false, false], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LBE 10111000
  ⟨1, 4, ![true, true, false, true, false, false, true, false], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LBE 11010010
  ⟨1, 4, ![false, false, true, false, true, true, false, true], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LBE 00101101
  ⟨1, 4, ![false, true, false, false, false, true, true, true], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LBE 01000111
  ⟨1, 6, ![true, false, true, true, true, false, false, false], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LBG 10111000
  ⟨1, 6, ![false, true, true, false, false, false, true, false], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBG 01100010
  ⟨1, 6, ![true, true, false, true, false, false, true, false], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LBG 11010010
  ⟨1, 6, ![true, true, false, false, true, false, true, false], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LBG 11001010
  ⟨1, 6, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBG 10001110
  ⟨1, 6, ![false, true, false, false, true, true, true, false], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LBG 01001110
  ⟨1, 6, ![true, false, true, true, false, false, false, true], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LBG 10110001
  ⟨1, 6, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBG 01110001
  ⟨1, 6, ![false, false, true, true, false, true, false, true], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LBG 00110101
  ⟨1, 6, ![false, false, true, false, true, true, false, true], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LBG 00101101
  ⟨1, 6, ![true, false, false, true, true, true, false, true], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBG 10011101
  ⟨1, 6, ![false, true, false, false, false, true, true, true], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LBG 01000111
  ⟨1, 7, ![false, true, true, false, false, false, true, false], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBH 01100010
  ⟨1, 7, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBH 10001110
  ⟨1, 7, ![false, true, false, false, true, true, true, false], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LBH 01001110
  ⟨1, 7, ![true, false, true, true, false, false, false, true], ![0, 1, 4, 6, 2, 3, 5]⟩,  -- LBH 10110001
  ⟨1, 7, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LBH 01110001
  ⟨1, 7, ![true, false, false, true, true, true, false, true], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LBH 10011101
  ⟨2, 4, ![true, true, true, false, true, false, false, false], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LCE 11101000
  ⟨2, 4, ![true, false, true, true, true, false, false, false], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LCE 10111000
  ⟨2, 4, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LCE 11100100
  ⟨2, 4, ![false, true, true, false, true, true, false, false], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LCE 01101100
  ⟨2, 4, ![true, true, false, true, false, false, true, false], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LCE 11010010
  ⟨2, 4, ![false, false, true, false, true, false, true, false], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LCE 00101010
  ⟨2, 4, ![true, true, false, true, false, true, false, true], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LCE 11010101
  ⟨2, 4, ![false, false, true, false, true, true, false, true], ![0, 5, 1, 4, 3, 2, 6]⟩,  -- LCE 00101101
  ⟨2, 4, ![true, false, false, true, false, false, true, true], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LCE 10010011
  ⟨2, 4, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LCE 00011011
  ⟨2, 4, ![false, true, false, false, false, true, true, true], ![0, 1, 3, 4, 6, 2, 5]⟩,  -- LCE 01000111
  ⟨2, 4, ![false, false, false, true, false, true, true, true], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LCE 00010111
  ⟨2, 5, ![true, true, true, false, true, false, false, false], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LCF 11101000
  ⟨2, 5, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LCF 11100100
  ⟨2, 5, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LCF 00011011
  ⟨2, 5, ![false, false, false, true, false, true, true, true], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LCF 00010111
  ⟨3, 4, ![true, true, true, false, true, false, false, false], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LDE 11101000
  ⟨3, 4, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDE 11100100
  ⟨3, 4, ![false, false, true, false, true, false, true, false], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LDE 00101010
  ⟨3, 4, ![true, true, false, true, false, true, false, true], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LDE 11010101
  ⟨3, 4, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDE 00011011
  ⟨3, 4, ![false, false, false, true, false, true, true, true], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LDE 00010111
  ⟨3, 5, ![true, true, true, false, true, false, false, false], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LDF 11101000
  ⟨3, 5, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDF 11100100
  ⟨3, 5, ![false, true, true, true, false, true, false, false], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LDF 01110100
  ⟨3, 5, ![true, true, false, false, true, false, true, false], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LDF 11001010
  ⟨3, 5, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LDF 10001110
  ⟨3, 5, ![false, false, false, true, true, true, true, false], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LDF 00011110
  ⟨3, 5, ![true, true, true, false, false, false, false, true], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LDF 11100001
  ⟨3, 5, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LDF 01110001
  ⟨3, 5, ![false, false, true, true, false, true, false, true], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LDF 00110101
  ⟨3, 5, ![true, false, false, false, true, false, true, true], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LDF 10001011
  ⟨3, 5, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDF 00011011
  ⟨3, 5, ![false, false, false, true, false, true, true, true], ![0, 4, 3, 1, 5, 2, 6]⟩,  -- LDF 00010111
  ⟨3, 7, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDH 11100100
  ⟨3, 7, ![false, true, true, true, false, true, false, false], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LDH 01110100
  ⟨3, 7, ![false, true, true, false, false, false, true, false], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LDH 01100010
  ⟨3, 7, ![false, false, true, false, true, false, true, false], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LDH 00101010
  ⟨3, 7, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LDH 10001110
  ⟨3, 7, ![false, false, false, true, true, true, true, false], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LDH 00011110
  ⟨3, 7, ![true, true, true, false, false, false, false, true], ![0, 4, 1, 5, 3, 2, 6]⟩,  -- LDH 11100001
  ⟨3, 7, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LDH 01110001
  ⟨3, 7, ![true, true, false, true, false, true, false, true], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LDH 11010101
  ⟨3, 7, ![true, false, false, true, true, true, false, true], ![0, 1, 5, 2, 3, 4, 6]⟩,  -- LDH 10011101
  ⟨3, 7, ![true, false, false, false, true, false, true, true], ![0, 1, 3, 5, 2, 6, 4]⟩,  -- LDH 10001011
  ⟨3, 7, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LDH 00011011
  ⟨4, 7, ![true, true, true, false, false, true, false, false], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LEH 11100100
  ⟨4, 7, ![false, true, true, false, true, true, false, false], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LEH 01101100
  ⟨4, 7, ![false, false, true, false, true, false, true, false], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LEH 00101010
  ⟨4, 7, ![true, true, false, true, false, true, false, true], ![0, 5, 2, 3, 1, 4, 6]⟩,  -- LEH 11010101
  ⟨4, 7, ![true, false, false, true, false, false, true, true], ![0, 1, 4, 3, 5, 2, 6]⟩,  -- LEH 10010011
  ⟨4, 7, ![false, false, false, true, true, false, true, true], ![0, 4, 1, 3, 5, 2, 6]⟩,  -- LEH 00011011
  ⟨5, 6, ![true, true, false, false, true, false, true, false], ![0, 4, 6, 2, 3, 1, 5]⟩,  -- LFG 11001010
  ⟨5, 6, ![true, false, false, false, true, true, true, false], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LFG 10001110
  ⟨5, 6, ![false, true, true, true, false, false, false, true], ![0, 1, 5, 3, 2, 6, 4]⟩,  -- LFG 01110001
  ⟨5, 6, ![false, false, true, true, false, true, false, true], ![0, 4, 6, 2, 3, 1, 5]⟩  -- LFG 00110101
]

set_option maxRecDepth 100000 in
theorem h21t2_dSeg5_good : ∀ s ∈ h21t2_dSeg5, s.Good h21S := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_dSeg6_good : ∀ s ∈ h21t2_dSeg6, s.Good h21S := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_lin3_good : ∀ s ∈ h21t2_lin3, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_lin4_good : ∀ s ∈ h21t2_lin4, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_lin5_good : ∀ s ∈ h21t2_lin5, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_lin6_good : ∀ s ∈ h21t2_lin6, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t2_lin7_good : ∀ s ∈ h21t2_lin7, s.Good := by decide +kernel

def h21t2_NoNew (T : Facets21 x) : Prop :=
  (∀ s ∈ h21t2_dSeg5, ¬ s.Cond (h21t2_sfac T)) ∧ (∀ s ∈ h21t2_dSeg6, ¬ s.Cond (h21t2_sfac T)) ∧
  (∀ s ∈ h21t2_lin3, ¬ h21rLinCond T s) ∧ (∀ s ∈ h21t2_lin4, ¬ h21rLinCond T s) ∧
  (∀ s ∈ h21t2_lin5, ¬ h21rLinCond T s) ∧ (∀ s ∈ h21t2_lin6, ¬ h21rLinCond T s) ∧
  (∀ s ∈ h21t2_lin7, ¬ h21rLinCond T s)

/-- The residual with the quad-diagonal views and the complete line lists added. -/
def H21Resid5 (T : Facets21 x) : Prop := H21Resid4 T ∧ h21t2_NoNew T

theorem h21t2_rule_isRupert (T : Facets21 x) (h : ¬ H21Resid5 T) : IsRupert (univ.image x) := by
  by_contra hR
  apply h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra h4
    exact hR (h21t_rule_isRupert T h4)
  · exact fun s hs hc => hR (s0x_seg_rupert (h21t2_sfac T) T.inj s (h21t2_dSeg5_good s hs) hc)
  · exact fun s hs hc => hR (s0x_seg_rupert (h21t2_sfac T) T.inj s (h21t2_dSeg6_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21t2_lin3_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21t2_lin4_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21t2_lin5_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21t2_lin6_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21t2_lin7_good s hs) hc)

theorem h21t2_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets21 x)
    (h : ¬ H21Resid5 T) : False :=
  hN.2 (h21t2_rule_isRupert T h)

end H21
end Minimality
