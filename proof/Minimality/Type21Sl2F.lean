module

public import Minimality.Type21Sl2E

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21

/-! ### Leaf lists (generated: `gen_seg.cc`, `gen_lin.cc`) -/

/-- Edge views s01 s04 s05 s13 s14 s15 s34 s35 s46: every facing pattern whose silhouette is a cycle
not containing the viewed edge (tilt bits for the two edge-on facets), by cycle length. -/
def h21b_seg4 : List (h21b_SegSpec 4) := [
  ⟨0, 1, 0, 1, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- s01 AvBvG-H-
  ⟨0, 1, 0, 1, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- s01 A^B^G-H-
  ⟨0, 5, 1, 2, ![false, false, false, false, false, true, false, true], ![1, 3, 2, 5]⟩,  -- s05 BvCvE-G-
  ⟨0, 5, 1, 2, ![false, true, true, false, true, true, true, true], ![0, 1, 4, 6]⟩,  -- s05 B^C^E+G+
  ⟨1, 3, 4, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- s13 EvFvC+D+
  ⟨1, 3, 4, 5, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- s13 E^F^C+D+
  ⟨1, 4, 0, 4, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- s14 AvEvC+H+
  ⟨1, 4, 0, 4, ![true, false, true, true, true, false, true, true], ![0, 1, 3, 5]⟩,  -- s14 A^E^C+H+
  ⟨1, 5, 1, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- s15 BvFvD+G+
  ⟨1, 5, 1, 5, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩,  -- s15 B^F^D+G+
  ⟨3, 4, 4, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- s34 EvGvB-C-
  ⟨3, 4, 4, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩,  -- s34 E^G^B+C+
  ⟨4, 6, 3, 6, ![false, false, true, false, false, false, false, false], ![0, 5, 2, 6]⟩,  -- s46 DvGvB-F-H-
  ⟨4, 6, 3, 6, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- s46 D^G^B-F-H+
  ⟨4, 6, 3, 6, ![false, true, true, true, false, true, true, true], ![0, 1, 3, 4]⟩  -- s46 D^G^B+F+H+
]

def h21b_seg5 : List (h21b_SegSpec 5) := [
  ⟨0, 1, 0, 1, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- s01 AvBvG-H+
  ⟨0, 1, 0, 1, ![true, true, false, false, true, true, false, true], ![0, 4, 3, 2, 5]⟩,  -- s01 A^B^G-H+
  ⟨0, 1, 0, 1, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s01 AvBvG+H+
  ⟨0, 1, 0, 1, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- s01 A^B^G+H+
  ⟨0, 4, 0, 3, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- s04 AvDvF-H-
  ⟨0, 4, 0, 3, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- s04 A^D^F-H-
  ⟨0, 4, 0, 3, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s04 AvDvF+H+
  ⟨0, 4, 0, 3, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- s04 A^D^F+H+
  ⟨0, 5, 1, 2, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- s05 B^C^E-G-
  ⟨0, 5, 1, 2, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- s05 BvCvE+G-
  ⟨0, 5, 1, 2, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- s05 B^C^E-G+
  ⟨0, 5, 1, 2, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s05 BvCvE+G+
  ⟨1, 3, 4, 5, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- s13 EvFvC-D-
  ⟨1, 3, 4, 5, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s13 E^F^C-D-
  ⟨1, 3, 4, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- s13 EvFvC+D-
  ⟨1, 3, 4, 5, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- s13 E^F^C+D-
  ⟨1, 4, 0, 4, ![false, false, false, true, false, false, true, false], ![0, 4, 3, 2, 6]⟩,  -- s14 AvEvC-H-
  ⟨1, 4, 0, 4, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- s14 A^E^C-H-
  ⟨1, 4, 0, 4, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s14 AvEvC+H-
  ⟨1, 4, 0, 4, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- s14 A^E^C+H-
  ⟨1, 5, 1, 5, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- s15 BvFvD-G-
  ⟨1, 5, 1, 5, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- s15 B^F^D-G-
  ⟨1, 5, 1, 5, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- s15 BvFvD-G+
  ⟨1, 5, 1, 5, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- s15 B^F^D-G+
  ⟨3, 4, 4, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- s34 E^G^B-C-
  ⟨3, 4, 4, 6, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- s34 EvGvB+C-
  ⟨3, 4, 4, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- s34 E^G^B-C+
  ⟨3, 4, 4, 6, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- s34 EvGvB+C+
  ⟨3, 5, 5, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- s35 FvHvA-D-
  ⟨3, 5, 5, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- s35 F^H^A-D-
  ⟨3, 5, 5, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- s35 FvHvA+D+
  ⟨3, 5, 5, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- s35 F^H^A+D+
  ⟨4, 6, 3, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s46 D^G^B-F-H-
  ⟨4, 6, 3, 6, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- s46 DvGvB+F-H-
  ⟨4, 6, 3, 6, ![false, false, true, false, false, false, false, true], ![0, 5, 3, 2, 6]⟩,  -- s46 DvGvB-F-H+
  ⟨4, 6, 3, 6, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- s46 D^G^B+F-H+
  ⟨4, 6, 3, 6, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- s46 D^G^B-F+H+
  ⟨4, 6, 3, 6, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩  -- s46 DvGvB+F+H+
]

def h21b_seg6 : List (h21b_SegSpec 6) := [
  ⟨0, 1, 0, 1, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- s01 AvBvG+H-
  ⟨0, 1, 0, 1, ![true, true, false, false, true, true, true, false], ![0, 4, 6, 2, 3, 5]⟩,  -- s01 A^B^G+H-
  ⟨0, 4, 0, 3, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- s04 AvDvF+H-
  ⟨0, 4, 0, 3, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- s04 A^D^F+H-
  ⟨0, 4, 0, 3, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- s04 AvDvF-H+
  ⟨0, 4, 0, 3, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- s04 A^D^F-H+
  ⟨0, 5, 1, 2, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- s05 B^C^E+G-
  ⟨0, 5, 1, 2, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- s05 BvCvE-G+
  ⟨1, 3, 4, 5, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- s13 EvFvC-D+
  ⟨1, 3, 4, 5, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- s13 E^F^C-D+
  ⟨1, 4, 0, 4, ![false, false, false, true, false, false, true, true], ![0, 4, 3, 5, 2, 6]⟩,  -- s14 AvEvC-H+
  ⟨1, 4, 0, 4, ![true, false, false, true, true, false, true, true], ![0, 1, 3, 5, 2, 6]⟩,  -- s14 A^E^C-H+
  ⟨1, 5, 1, 5, ![false, false, true, true, false, false, false, true], ![0, 4, 6, 2, 3, 5]⟩,  -- s15 BvFvD+G-
  ⟨1, 5, 1, 5, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- s15 B^F^D+G-
  ⟨3, 4, 4, 6, ![true, true, false, true, true, false, true, false], ![0, 5, 1, 3, 2, 6]⟩,  -- s34 E^G^B+C-
  ⟨3, 4, 4, 6, ![true, false, true, true, false, false, false, false], ![0, 1, 4, 6, 2, 5]⟩,  -- s34 EvGvB-C+
  ⟨3, 5, 5, 7, ![true, true, true, false, false, false, false, false], ![0, 4, 1, 5, 2, 6]⟩,  -- s35 FvHvA+D-
  ⟨3, 5, 5, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- s35 F^H^A+D-
  ⟨3, 5, 5, 7, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- s35 FvHvA-D+
  ⟨3, 5, 5, 7, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- s35 F^H^A-D+
  ⟨4, 6, 3, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- s46 D^G^B+F-H-
  ⟨4, 6, 3, 6, ![false, true, true, false, false, true, false, false], ![0, 1, 3, 5, 2, 6]⟩,  -- s46 DvGvB+F+H-
  ⟨4, 6, 3, 6, ![false, true, true, false, false, false, false, true], ![0, 1, 5, 3, 2, 6]⟩,  -- s46 DvGvB+F-H+
  ⟨4, 6, 3, 6, ![false, false, true, false, false, true, false, true], ![0, 5, 1, 3, 2, 6]⟩  -- s46 DvGvB-F+H+
]


/-- Line views: the pattern leaves predicted on the segment-uncovered adversary samples, closed under the
symmetries s1, s2, s3. -/
def h21b_lin4 : List (h21b_LinSpec 4) := [
  ⟨0, 2, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LAC 00110011
  ⟨0, 2, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LAC 11001100
  ⟨0, 6, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LAG 00110011
  ⟨0, 6, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LAG 11001100
  ⟨0, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LAH 00110011
  ⟨0, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LAH 11001100
  ⟨1, 3, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LBD 00110011
  ⟨1, 3, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LBD 11001100
  ⟨1, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LBH 00110011
  ⟨1, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LBH 11001100
  ⟨2, 3, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LCD 00110011
  ⟨2, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LCF 00110011
  ⟨2, 5, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LCF 11001100
  ⟨2, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LCH 00110011
  ⟨3, 4, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LDE 00110011
  ⟨3, 4, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LDE 11001100
  ⟨3, 5, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LDF 00110011
  ⟨3, 5, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LDF 11001100
  ⟨3, 6, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LDG 11001100
  ⟨4, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LEH 00110011
  ⟨4, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LEH 11001100
  ⟨5, 6, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- LFG 00110011
  ⟨5, 6, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- LFG 11001100
  ⟨6, 7, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩  -- LGH 00110011
]

def h21b_lin5 : List (h21b_LinSpec 5) := [
  ⟨0, 2, ![false, true, false, false, false, true, false, true], ![0, 1, 3, 2, 5]⟩,  -- LAC 01000101
  ⟨0, 2, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LAC 01100101
  ⟨0, 2, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LAC 10011010
  ⟨0, 2, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LAC 10111010
  ⟨0, 5, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LAF 10011010
  ⟨0, 5, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LAF 11110000
  ⟨0, 6, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LAG 00001101
  ⟨0, 6, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LAG 00001111
  ⟨0, 6, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LAG 11110000
  ⟨0, 6, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- LAG 11110010
  ⟨0, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LAH 00001111
  ⟨0, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- LAH 01001100
  ⟨0, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LAH 01100101
  ⟨0, 7, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LAH 10011010
  ⟨0, 7, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LAH 11110000
  ⟨1, 3, ![false, false, true, false, false, false, true, true], ![0, 5, 3, 4, 6]⟩,  -- LBD 00100011
  ⟨1, 3, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LBD 01110011
  ⟨1, 4, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LBE 00001111
  ⟨1, 4, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LBE 01100101
  ⟨1, 4, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LBE 10011010
  ⟨1, 4, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LBE 11110000
  ⟨1, 6, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LBG 00001111
  ⟨1, 6, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LBG 01100101
  ⟨1, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LBG 10011010
  ⟨1, 6, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LBG 11110000
  ⟨1, 7, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LBH 00110010
  ⟨1, 7, ![false, true, true, true, false, false, true, true], ![0, 1, 5, 3, 4]⟩,  -- LBH 01110011
  ⟨2, 4, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LCE 00001111
  ⟨2, 4, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LCE 01100101
  ⟨2, 4, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LCE 10011010
  ⟨2, 4, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LCE 11110000
  ⟨2, 5, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LCF 00001111
  ⟨2, 5, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LCF 00101111
  ⟨2, 5, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- LCF 11010000
  ⟨2, 5, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LCF 11110000
  ⟨2, 6, ![false, false, false, false, true, true, false, true], ![1, 4, 3, 2, 5]⟩,  -- LCG 00001101
  ⟨2, 6, ![false, false, true, false, true, true, true, true], ![0, 5, 1, 4, 6]⟩,  -- LCG 00101111
  ⟨2, 6, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LCG 10011000
  ⟨2, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- LCG 10111010
  ⟨3, 4, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- LDE 11000100
  ⟨3, 4, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- LDE 11011100
  ⟨3, 5, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LDF 00001111
  ⟨3, 5, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- LDF 00110111
  ⟨3, 5, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LDF 01100101
  ⟨3, 5, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩,  -- LDF 10011010
  ⟨3, 5, ![true, true, true, true, false, false, false, false], ![1, 4, 6, 2, 5]⟩,  -- LDF 11110000
  ⟨3, 7, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- LDH 00001010
  ⟨3, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- LDH 00001111
  ⟨3, 7, ![false, true, true, false, false, false, false, false], ![0, 1, 5, 2, 6]⟩,  -- LDH 01100000
  ⟨3, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LDH 01100101
  ⟨3, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- LDH 10011111
  ⟨3, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- LDH 11110101
  ⟨4, 7, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- LEH 00110010
  ⟨4, 7, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- LEH 00111011
  ⟨5, 6, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- LFG 01100101
  ⟨5, 6, ![false, true, true, false, false, true, true, true], ![0, 1, 3, 4, 6]⟩,  -- LFG 01100111
  ⟨5, 6, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- LFG 10011000
  ⟨5, 6, ![true, false, false, true, true, false, true, false], ![0, 1, 3, 2, 6]⟩  -- LFG 10011010
]

def h21b_lin6 : List (h21b_LinSpec 6) := [
  ⟨0, 2, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- LAC 11100101
  ⟨0, 5, ![false, false, false, true, true, false, true, false], ![0, 4, 1, 3, 2, 6]⟩,  -- LAF 00011010
  ⟨0, 5, ![false, true, true, true, false, false, false, false], ![0, 1, 5, 2, 6, 4]⟩,  -- LAF 01110000
  ⟨0, 5, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩,  -- LAF 10011110
  ⟨0, 5, ![true, true, true, true, false, true, false, false], ![1, 3, 5, 2, 6, 4]⟩,  -- LAF 11110100
  ⟨0, 6, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- LAG 10001111
  ⟨2, 5, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- LCF 00001011
  ⟨5, 6, ![true, false, false, true, true, true, true, false], ![0, 1, 5, 3, 2, 6]⟩  -- LFG 10011110
]


set_option maxRecDepth 100000 in
theorem h21b_seg4_good : ∀ s ∈ h21b_seg4, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21b_seg5_good : ∀ s ∈ h21b_seg5, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21b_seg6_good : ∀ s ∈ h21b_seg6, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21b_lin4_good : ∀ s ∈ h21b_lin4, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21b_lin5_good : ∀ s ∈ h21b_lin5, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21b_lin6_good : ∀ s ∈ h21b_lin6, s.Good := by decide +kernel

end H21
end Minimality
