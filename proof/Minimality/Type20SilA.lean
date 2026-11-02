module

public import Minimality.SilS0XC
public import Minimality.SevenTypes
public import Minimality.Type16

@[expose] public section


/-!
# H20S-A: type 20's facets as an `S0xFac`, and the metric-item cells (I_MA, I_MC)

Labels (skeleton = Frame20): `0 m1+, 1 xa, 2 m2+, 3 m1-, 4 m2-, 5 v, 6 xb`.  Facets, indexed as in
`SIL/packages.md` §3.1 (`A..H = 0..7`): `A 134, B 025, C 0135, D 345, E 016, F 026, G 146, H 2456`.
Edges (facet pair): `01 CE, 02 BF, 05 BC, 06 EF, 13 AC, 14 AG, 16 EG, 25 BH, 26 FH, 34 AD, 35 CD,
45 DH, 46 GH`.

Cells (packages §3.3; pattern `A..H`, `t` = up):
* I_MA: `LCG:01625[CvGv]` (up `B E F`), `s05:0162[B^C^]` (literals `A+ G+`).
* I_MC: `s01:0546[C^E^]` (literals `D+ H-`), `s35:1346[C^D^]` (literals `E+ F+ G-`),
  `LCF:01346[C^F^]` (up `B C D F H`), `LBD:2546[B^D^]` (up all but `H`),
  `LAF:01352[AvFv]` (up `B C`).
A line view `L_XY` is `cross (N X) (N Y)`; the frame cell fixes it up to the orientation of the
frame, so each line cell comes with its complemented pattern (`…'`, the view `-u`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H20S
open Minimality.H21

/-- Facet vertex sets of type 20, `A..H = 0..7`. -/
def h20s_S : Fin 8 → Finset (Fin 7) :=
  ![{1, 3, 4}, {0, 2, 5}, {0, 1, 3, 5}, {3, 4, 5}, {0, 1, 6}, {0, 2, 6}, {1, 4, 6}, {2, 4, 5, 6}]

theorem h20s_mem (t : Fin 8) : h20s_S t ∈ sevenTypeFaces 19 := by
  fin_cases t <;> decide

/-- The facet `t` from the realization `hR`. -/
noncomputable def h20s_face {x : Fin 7 → ℝ³} (hR : RealizesFaces x (sevenTypeFaces 19))
    (t : Fin 8) : Face16 x (h20s_S t) :=
  Face16.ofAffine (hR _ (h20s_mem t)).choose (hR _ (h20s_mem t)).choose_spec

/-- **Type 20's eight facets as a type-free facet family.** -/
noncomputable def h20s_fac {x : Fin 7 → ℝ³} (hR : RealizesFaces x (sevenTypeFaces 19)) :
    S0xFac 8 h20s_S x where
  f t := (h20s_face hR t).f
  N t := (h20s_face hR t).N
  hN t := (h20s_face hR t).hN
  zero t := (h20s_face hR t).zero
  neg t := (h20s_face hR t).neg

/-! ### Leaf specifications -/

/-- I_MA, `LCG:01625[CvGv]`. -/
def h20s_LCG : S0xLin 7 8 5 where
  X := 2
  Y := 6
  pat := ![false, true, false, false, true, true, false, false]
  c := ![0, 1, 6, 2, 5]

def h20s_LCG' : S0xLin 7 8 5 := { h20s_LCG with pat := fun t => !h20s_LCG.pat t }

/-- I_MA, `s05:0162[B^C^]`. -/
def h20s_s05 : S0xSeg 7 8 4 where
  i := 0
  j := 5
  pat := ![true, true, true, true, false, false, true, true]
  c := ![0, 1, 6, 2]

/-- I_MC, `s01:0546[C^E^]`. -/
def h20s_s01 : S0xSeg 7 8 4 where
  i := 0
  j := 1
  pat := ![true, false, true, true, true, false, true, false]
  c := ![0, 5, 4, 6]

/-- I_MC, `s35:1346[C^D^]`. -/
def h20s_s35 : S0xSeg 7 8 4 where
  i := 3
  j := 5
  pat := ![false, true, true, true, true, true, false, true]
  c := ![1, 3, 4, 6]

/-- I_MC, `LCF:01346[C^F^]`. -/
def h20s_LCF : S0xLin 7 8 5 where
  X := 2
  Y := 5
  pat := ![false, true, true, true, false, true, false, true]
  c := ![0, 1, 3, 4, 6]

def h20s_LCF' : S0xLin 7 8 5 := { h20s_LCF with pat := fun t => !h20s_LCF.pat t }

/-- I_MC, `LBD:2546[B^D^]`. -/
def h20s_LBD : S0xLin 7 8 4 where
  X := 1
  Y := 3
  pat := ![true, true, true, true, true, true, true, false]
  c := ![2, 5, 4, 6]

def h20s_LBD' : S0xLin 7 8 4 := { h20s_LBD with pat := fun t => !h20s_LBD.pat t }

/-- I_MC, `LAF:01352[AvFv]`. -/
def h20s_LAF : S0xLin 7 8 5 where
  X := 0
  Y := 5
  pat := ![false, true, true, false, false, false, false, false]
  c := ![0, 1, 3, 5, 2]

def h20s_LAF' : S0xLin 7 8 5 := { h20s_LAF with pat := fun t => !h20s_LAF.pat t }

theorem h20s_LCG_good : h20s_LCG.Good h20s_S := by decide
theorem h20s_LCG'_good : h20s_LCG'.Good h20s_S := by decide
theorem h20s_s05_good : h20s_s05.Good h20s_S := by decide
theorem h20s_s01_good : h20s_s01.Good h20s_S := by decide
theorem h20s_s35_good : h20s_s35.Good h20s_S := by decide
theorem h20s_LCF_good : h20s_LCF.Good h20s_S := by decide
theorem h20s_LCF'_good : h20s_LCF'.Good h20s_S := by decide
theorem h20s_LBD_good : h20s_LBD.Good h20s_S := by decide
theorem h20s_LBD'_good : h20s_LBD'.Good h20s_S := by decide
theorem h20s_LAF_good : h20s_LAF.Good h20s_S := by decide
theorem h20s_LAF'_good : h20s_LAF'.Good h20s_S := by decide

end H20S
end Minimality
