module

public import Minimality.Type24ROff
public import Minimality.Type24ROffTieA

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.Sym
  Minimality.T24.Reg Minimality.T24.A17

/-!
# Type 24: S7 `rOff_closed` without the tie hypothesis (named pieces)

Tie `nB = 0` (facet 0345 edge-on): `tieA_lexAny` (file `TieA`: vertex-2 tilt + `frontOf_lex` + the 6-rim leaf).
Tie `nu346b = 0`, `nB < 0` (facet 346 edge-on): `e12_A2_tie` (file `A2Tie`: the pentagon leaf with 346 facing down
at the tilt).
-/

namespace Minimality.T24.A19

theorem nB_zero_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    nB x = 0 ↔ F.f 3 (x 2) = F.f 3 (x 1) := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := (nB_neg_iff F).mpr hl; linarith
    · have := (nB_pos_iff F).mpr hl; linarith
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := (nB_neg_iff F).mp hl; linarith
    · have := (nB_pos_iff F).mp hl; linarith

/-- **Core of S7**, all of `nC > 0` (no tie hypothesis): `rOff_core` plus the two tie pieces. -/
theorem rOff_core_all {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h1234 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (hO : ¬ H24K.SAT.OB1 x) (hU : ¬ LexAny F) (hnC : 0 < nC x) : False := by
  by_cases hT : CoreTie F
  · have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp hnC
    have h235 : F.f 6 (x 1) < F.f 6 (x 6) := nu235c_pos F hC h1356 hnC.le
    obtain ⟨hac, hbc⟩ := e16_sym F hC hnc h235 hU
    have hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ := by
      by_contra h
      exact hO ⟨not_lt.mp h, hac, hbc⟩
    rcases hT with hB | ⟨hB, h8⟩
    · have h346 : F.f 8 (x 1) < F.f 8 (x 2) := nu346b_pos F hC h1234 hB.ge
      exact hU (tieA_lexAny F hC ((nB_zero_iff F).mp hB) hnc h346 h1356 h1456 hab hbc)
    · exact e12_A2_tie F hC ((nB_neg_iff F).mp hB) h8.symm hab hbc hU
  · exact rOff_core F hC h1234 h1356 h1456 hO hU hnC hT

/-- **S7 (`offOB1_closed`) on `R_off`**: `Hole24R` and `ROff` give `False` . -/
theorem rOff_closed {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) (hRo : Reg.ROff x) :
    False := by
  obtain ⟨hO, h1234, h1356, h1456, ha⟩ := hRo
  have hC : CbarIn x := hR.1
  have hU : ¬ LexAny F := hR.2.2.2.2.1
  have h1245 := resid24_b1245 hR.2.1 hO
  rcases nBC_pos F ha with hB | hCp
  · by_cases hCn : 0 < nC x
    · exact rOff_core_all F hC h1234 h1356 h1456 hO hU hCn
    · have hnC' : 0 < nC (x ∘ pi24) := by rw [nC_comp_pi24]; exact hB
      refine rOff_core_all (sym24 F) ((cbarIn_comp_pi24 x).2 hC) ?_ ?_ ?_ ?_ ?_ hnC'
      · simp only [oblX0_comp_pi24, oblX6_comp_pi24, pi24_3, pi24_4]
        linarith
      · simp only [oblX0_comp_pi24, oblX2_comp_pi24, pi24_3, pi24_5]
        linarith
      · simp only [oblX0_comp_pi24, oblX2_comp_pi24, pi24_4, pi24_5]
        linarith
      · rwa [ob1_comp_pi24]
      · exact fun h => hU (lexAny_sym F h)
  · exact rOff_core_all F hC h1234 h1356 h1456 hO hU hCp

end Minimality.T24.A19
