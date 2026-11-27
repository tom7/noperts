module

public import Minimality.Type24NamedCover
public import Minimality.Type24ROffTie

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.RCell Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Sym Minimality.T24.Reg Minimality.T24.A19 Minimality.T24.Stmt

/-!
# Type 24 off `OB1`: the hole lies on `OffWall` (job OSPEC, nopert229 notes/OPENSPECIAL-STRATEGY.md)

* `rOff_closed_gen`: S7 (`rOff_closed`) needs only `CbarIn` and `¬ LexAny`: on `Reg.ROff` (off `OB1`, the three frame
  brackets `b1234 < 0 < b1356, b1456` and `a4 < 1 ∨ a5 < 1`) and `b1245 > 0` every point has a lex cell.  The proof of
  `rOff_closed` uses nothing else of `Hole24R`.
* `offWall_of_hole24`: a `Hole24` point off `OB1` has `a4 ≥ 1` and `a5 ≥ 1` (`Resid24` gives the brackets,
  `resid24_frame_signs`).
* `OpenSpecialW`: `OpenSpecial` restricted to `OffWall` and the three brackets; strictly weaker obligation,
  `openSpecialW_of_openSpecial`; it still closes the hole with `NamedCoverEmpty` (`not_hole24_of_namedCoverEmpty_W`)
  and with `OpenOB1` (`open24_of_split_W`).
-/

namespace Minimality.T24.OSpec

/-- **S7 with the minimal hypotheses**: off `OB1`, on the bracket region `Reg.ROff`, every point inside `CbarIn` has
a lex cell (`LexAny F`). -/
theorem rOff_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hRo : Reg.ROff x)
    (h1245 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) : LexAny F := by
  by_contra hU
  obtain ⟨hO, h1234, h1356, h1456, ha⟩ := hRo
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

/-- The three frame brackets plus `CbarIn`, off `OB1`, and no lex cell force `a4 ≥ 1` and `a5 ≥ 1`. -/
theorem offWall_of_brackets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hO : ¬ H24K.SAT.OB1 x)
    (h1234 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (h1245 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5)
    (hU : ¬ LexAny F) : 1 ≤ oblX0 x 4 ∧ 1 ≤ oblX0 x 5 := by
  by_contra hne
  have ha : oblX0 x 4 < 1 ∨ oblX0 x 5 < 1 := by
    by_contra hh
    push Not at hh
    exact hne hh
  exact hU (rOff_lexAny F hC ⟨hO, h1234, h1356, h1456, ha⟩ h1245)

/-- **A `Hole24` point off `OB1` lies on `OffWall`** (`a4 ≥ 1`, `a5 ≥ 1`). -/
theorem offWall_of_hole24 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F)
    (hO : ¬ H24K.SAT.OB1 x) : Reg.OffWall x := by
  obtain ⟨h1, h2, h3⟩ := resid24_frame_signs h.2.2.1 hO
  exact ⟨hO, offWall_of_brackets F h.1.1 hO h1 h2 h3 (resid24_b1245 h.2.2.1 hO) h.1.2.2.2.1⟩

/-- [OPEN] The special piece, restricted: off `OB1`, on `OffWall` (`a4, a5 ≥ 1`), with the four frame brackets of
`Resid24` (`resid24_frame_signs`, `resid24_b1245`), on a wall or on `Q45Special'`, `HoleFull` fails. -/
def OpenSpecialW : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  ((oblX0 x 4 = 1 ∨ oblX0 x 5 = 1) ∨ Q45.Q45Special' F) → ¬ HoleFull x F

/-- [PROVED] `OpenSpecial → OpenSpecialW` (more hypotheses). -/
theorem openSpecialW_of_openSpecial (h : OpenSpecial) : OpenSpecialW :=
  fun x F hO _ _ _ _ _ _ hw => h x F hO hw

/-- Every `Hole24` point off `OB1` meets the hypotheses of `OpenSpecialW`. -/
theorem hole24_offOB1 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialW) : False := by
  obtain ⟨h1, h2, h3⟩ := resid24_frame_signs h.2.2.1 hO
  have h6 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  rcases hole24_ob1_or_special h with hO' | ⟨-, hw⟩ | hq
  · exact hO hO'
  · exact hS x F hO h4 h5 h1 h2 h3 h6 (Or.inl hw) (holeFull_of_hole24 h)
  · exact hS x F hO h4 h5 h1 h2 h3 h6 (Or.inr hq) (holeFull_of_hole24 h)

/-- [PROVED] Generic + restricted special assemble to `Open24`. -/
theorem open24_of_split_W (h1 : OpenOB1) (h2 : OpenSpecialW) : Open24 := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact h1 x _ hO (holeFull_of_hole24 hH)
  · exact hole24_offOB1 hH hO h2

end Minimality.T24.OSpec
