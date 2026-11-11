module

public import Minimality.Type16SAT.Cls16WC

@[expose] public section

/-!
# Type 16: cores with the cases "off `Z` and off its `sigma16` image" and "on `Z` with `CaseT16`"

`sigFac F`: the facet family of `y ∘ sigma16` obtained from a facet family `F` of `y` by the facet permutation `tau16`
(`sigma16 = (0 6)(1 2)` maps the facets `A B C D E F G H` to `B A G D E H C F`).  Then `ZShape16 (y ∘ sigma16) (sigFac F)`
says that the 18 `sigma16` images of the shape entries of `Z` vanish for `y`.
* `Core16ZZW e1 e2 e3 e4`: a wall core (signs by `SgnP`) with the case hypotheses `¬ ZShape16 y F` and
  `¬ ZShape16 (y ∘ sigma16) (sigFac F)`.
* `Core16ZTW e1 e2 e3 e4`: a wall core with the hypotheses `ZShape16 y F` (on `Z`) and `CaseT16 y`.
`rupert_of_core_bothZZW`, `rupert_of_core_bothZTW`: both chiralities (mirror).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The facet permutation induced by `sigma16`. -/
def tau16 : Fin 8 → Fin 8 := ![1, 0, 6, 3, 4, 7, 2, 5]

theorem mem_fIdx_sigma16 : ∀ (t : Fin 8) (i : Fin 7),
    i ∈ Minimality.V2.fIdx t ↔ sigma16 i ∈ Minimality.V2.fIdx (tau16 t) := by decide

/-- The facet family of `y ∘ sigma16` from a facet family of `y`. -/
def sigFac {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) : S0xFac 8 Minimality.V2.fIdx (y ∘ sigma16) where
  f := fun t => F.f (tau16 t)
  N := fun t => F.N (tau16 t)
  hN := fun t => F.hN (tau16 t)
  zero := fun t i hi => F.zero (tau16 t) (sigma16 i) ((mem_fIdx_sigma16 t i).1 hi)
  neg := fun t i hi => F.neg (tau16 t) (sigma16 i) (fun h => hi ((mem_fIdx_sigma16 t i).2 h))

/-- A wall core with the case hypotheses: off `Z`, and off the `sigma16` image of `Z`. -/
def Core16ZZW (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y), 0 < C16 y →
    SgnP e1 (br16 y 0 1 2 6) → SgnP e2 (br16 y 0 1 3 4) → SgnP e3 (br16 y 1 2 3 4) → SgnP e4 (br16 y 2 3 4 6) →
    ¬ ZShape16 y F → ¬ ZShape16 (y ∘ sigma16) (sigFac F) → IsRupert (univ.image y)

/-- A wall core with the case hypotheses: on `Z`, and `CaseT16`. -/
def Core16ZTW (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y), 0 < C16 y →
    SgnP e1 (br16 y 0 1 2 6) → SgnP e2 (br16 y 0 1 3 4) → SgnP e3 (br16 y 1 2 3 4) → SgnP e4 (br16 y 2 3 4 6) →
    ZShape16 y F → CaseT16 y → IsRupert (univ.image y)

/-- Both chiralities for a `Core16ZZW`. -/
theorem rupert_of_core_bothZZW {e1 e2 e3 e4 : ℝ} (hcore : Core16ZZW e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0) (h : Vec16 e1 e2 e3 e4 y)
    (hA : ¬ ZShape16 y F) (hB : ¬ ZShape16 (y ∘ sigma16) (sigFac F)) : IsRupert (univ.image y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ (fun h => hA ((zShape16_mir y F).1 h))
      (fun h => hB ((zShape16_mir (y ∘ sigma16) (sigFac F)).1 h)))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h1
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h2
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h3
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h4
  · exact hcore F hp (sgnP_pos hp h1) (sgnP_pos hp h2) (sgnP_pos hp h3) (sgnP_pos hp h4) hA hB

/-- Both chiralities for a `Core16ZTW`. -/
theorem rupert_of_core_bothZTW {e1 e2 e3 e4 : ℝ} (hcore : Core16ZTW e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0) (h : Vec16 e1 e2 e3 e4 y)
    (hz : ZShape16 y F) (hA : CaseT16 y) : IsRupert (univ.image y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ ((zShape16_mir y F).2 hz) ((caseT16_mir y).2 hA))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h1
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h2
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h3
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h4
  · exact hcore F hp (sgnP_pos hp h1) (sgnP_pos hp h2) (sgnP_pos hp h3) (sgnP_pos hp h4) hz hA

end Minimality.H16.SAT
