module

public import Minimality.Type16SAT.Cls16C
public import Minimality.Type16SAT.Cls16Z
public import Minimality.Type16SAT.Cls16W

@[expose] public section

/-!
# Type 16: wall cores with a case hypothesis

The wall analogues of `Core16T` (`Cls16C`) and `Core16Z` (`Cls16Z`): the four bracket signs are given by `SgnP`
(`e = 0`: that bracket is zero), as `Core16W` of `Cls16W`, plus the case hypothesis `CaseT16 y` resp. `¬ ZShape16 y F`.
`rupert_of_core_bothTW` / `rupert_of_core_bothZW`: both chiralities (mirror), in the form `Vec16 e1 e2 e3 e4 y` of the
products `C * bracket`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- A wall core with the case hypothesis `CaseT16`. -/
def Core16TW (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³}, S0xFac 8 Minimality.V2.fIdx y → 0 < C16 y →
    SgnP e1 (br16 y 0 1 2 6) → SgnP e2 (br16 y 0 1 3 4) → SgnP e3 (br16 y 1 2 3 4) → SgnP e4 (br16 y 2 3 4 6) →
    CaseT16 y → IsRupert (univ.image y)

/-- A wall core with the case hypothesis `¬ ZShape16`. -/
def Core16ZW (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y), 0 < C16 y →
    SgnP e1 (br16 y 0 1 2 6) → SgnP e2 (br16 y 0 1 3 4) → SgnP e3 (br16 y 1 2 3 4) → SgnP e4 (br16 y 2 3 4 6) →
    ¬ ZShape16 y F → IsRupert (univ.image y)

/-- Both chiralities for a `Core16TW`. -/
theorem rupert_of_core_bothTW {e1 e2 e3 e4 : ℝ} (hcore : Core16TW e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0) (h : Vec16 e1 e2 e3 e4 y)
    (hA : CaseT16 y) : IsRupert (univ.image y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ ((caseT16_mir y).2 hA))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h1
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h2
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h3
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h4
  · exact hcore F hp (sgnP_pos hp h1) (sgnP_pos hp h2) (sgnP_pos hp h3) (sgnP_pos hp h4) hA

/-- Both chiralities for a `Core16ZW`. -/
theorem rupert_of_core_bothZW {e1 e2 e3 e4 : ℝ} (hcore : Core16ZW e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0) (h : Vec16 e1 e2 e3 e4 y)
    (hA : ¬ ZShape16 y F) : IsRupert (univ.image y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ (fun h => hA ((zShape16_mir y F).1 h)))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h1
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h2
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h3
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h4
  · exact hcore F hp (sgnP_pos hp h1) (sgnP_pos hp h2) (sgnP_pos hp h3) (sgnP_pos hp h4) hA

/-- The `sigma16` image of a wall vector: `Vec16 f x` with `f = (-e1, e4, e3, e2)` gives `Vec16 e (x ∘ sigma16)`. -/
theorem vec16_sigma {e1 e2 e3 e4 : ℝ} {x : Fin 7 → ℝ³} (h : Vec16 (-e1) e4 e3 e2 x) :
    Vec16 e1 e2 e3 e4 (x ∘ sigma16) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have a1 := C16_sigma x
  have a2 := b1_sigma x
  have a3 := b2_sigma x
  have a4 := b3_sigma x
  have a5 := b4_sigma x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a1, a2, neg_mul, sgnP_neg]; exact h1
  · rw [a1, a3, neg_mul_neg]; exact h4
  · rw [a1, a4, neg_mul_neg]; exact h3
  · rw [a1, a5, neg_mul_neg]; exact h2

end Minimality.H16.SAT
