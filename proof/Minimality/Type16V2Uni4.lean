module

public import Minimality.TwoRayDiag

@[expose] public section

/-!
# V2: four-cycle depth unimodality and the pop choice (real-number lemmas)
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open Type08Sp Type08Sp.C2 TwoRay

/-- Peak count of a 4-cycle `a, b, c, d`. -/
noncomputable def peaks4 (a b c d : ℝ) : ℕ :=
  (if d < a ∧ b < a then 1 else 0) + (if a < b ∧ c < b then 1 else 0) +
  (if b < c ∧ d < c then 1 else 0) + (if c < d ∧ a < d then 1 else 0)

theorem lexUni4_of (z : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → i = j) (h : peaks4 (z 0) (z 1) (z 2) (z 3) = 1) :
    LexUni z (fun _ => 0) := by
  classical
  refine ⟨fun i j h _ => hinj i j h, ?_⟩
  have hne : ∀ i j : ZMod 4, i ≠ j → z i ≠ z j := fun i j hij h' => hij (hinj i j h')
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  have f0 : (0 : ZMod 4) + 1 = 1 := by decide
  have f1 : (1 : ZMod 4) + 1 = 2 := by decide
  have f2 : (2 : ZMod 4) + 1 = 3 := by decide
  have f3 : (3 : ZMod 4) + 1 = 0 := by decide
  have d01 : z 0 ≠ z 1 := hne _ _ (by decide)
  have d02 : z 0 ≠ z 2 := hne _ _ (by decide)
  have d03 : z 0 ≠ z 3 := hne _ _ (by decide)
  have d12 : z 1 ≠ z 2 := hne _ _ (by decide)
  have d13 : z 1 ≠ z 3 := hne _ _ (by decide)
  have d23 : z 2 ≠ z 3 := hne _ _ (by decide)
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  simp only [lexLt_iff d01, lexLt_iff d01.symm, lexLt_iff d02, lexLt_iff d02.symm, lexLt_iff d03, lexLt_iff d03.symm,
    lexLt_iff d12, lexLt_iff d12.symm, lexLt_iff d13, lexLt_iff d13.symm, lexLt_iff d23, lexLt_iff d23.symm]
  unfold peaks4 at h
  convert h using 3

theorem chord_above (dw dA du s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hu : (1 - s) * dw + s * dA < du) :
    dw < du ∨ dA < du := by
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc.1) (sub_pos.2 hs1).le, mul_nonneg (sub_nonneg.2 hc.2) hs0.le]

theorem chord_below (dw dA dd s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hd : dd < (1 - s) * dw + s * dA) :
    dd < dw ∨ dd < dA := by
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc.1) (sub_pos.2 hs1).le, mul_nonneg (sub_nonneg.2 hc.2) hs0.le]

/-- **The pop choice.**  With `du` not below both chord ends and `dd` not above both, one of the two 4-cycles
`(dw, d?, dA, dB)` has exactly one peak. -/
theorem pop_choice (dw dA dB du dd : ℝ)
    (h1 : dw ≠ dA) (h2 : dw ≠ dB) (h3 : dA ≠ dB) (h4 : du ≠ dw) (h5 : du ≠ dA)
    (h7 : dd ≠ dw) (h8 : dd ≠ dA)
    (F1 : dw < du ∨ dA < du) (F2 : dd < dw ∨ dd < dA) :
    peaks4 dw du dA dB = 1 ∨ peaks4 dw dd dA dB = 1 := by
  unfold peaks4
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;> rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
    rcases lt_or_gt_of_ne h3 with a3 | a3 <;> rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
    rcases lt_or_gt_of_ne h5 with a5 | a5 <;> rcases lt_or_gt_of_ne h7 with a7 | a7 <;>
    rcases lt_or_gt_of_ne h8 with a8 | a8 <;>
    first
      | (exfalso; rcases F1 with F | F <;> linarith)
      | (exfalso; rcases F2 with F | F <;> linarith)
      | (left; simp [a1, a2, a3, a4, a5, a1.le, a2.le, a3.le, a4.le, a5.le, not_lt.2 a1.le, not_lt.2 a2.le,
          not_lt.2 a3.le, not_lt.2 a4.le, not_lt.2 a5.le]; done)
      | (right; simp [a1, a2, a3, a7, a8, a1.le, a2.le, a3.le, a7.le, a8.le, not_lt.2 a1.le, not_lt.2 a2.le,
          not_lt.2 a3.le, not_lt.2 a7.le, not_lt.2 a8.le]; done)
