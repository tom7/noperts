module

public import Minimality.Type16UE

@[expose] public section


/-!
# U1: the pentagon screen cycle `(0,0), (1,0), (A5,B5), (A2,B2), (0,1)` (type-free pieces)
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

/-- Peak count of a 5-cycle. -/
noncomputable def peaks5 (a b c d e : ℝ) : ℕ :=
  (if e < a ∧ b < a then 1 else 0) + (if a < b ∧ c < b then 1 else 0) + (if b < c ∧ d < c then 1 else 0) +
  (if c < d ∧ e < d then 1 else 0) + (if d < e ∧ a < e then 1 else 0)

theorem lexUni5_of (z : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → i = j)
    (h : peaks5 (z 0) (z 1) (z 2) (z 3) (z 4) = 1) : LexUni z (fun _ => 0) := by
  classical
  refine ⟨fun i j h _ => hinj i j h, ?_⟩
  have hne : ∀ i j : ZMod 5, i ≠ j → z i ≠ z j := fun i j hij h' => hij (hinj i j h')
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  have f0 : (0 : ZMod 5) + 1 = 1 := by decide
  have f1 : (1 : ZMod 5) + 1 = 2 := by decide
  have f2 : (2 : ZMod 5) + 1 = 3 := by decide
  have f3 : (3 : ZMod 5) + 1 = 4 := by decide
  have f4 : (4 : ZMod 5) + 1 = 0 := by decide
  have d01 : z 0 ≠ z 1 := hne _ _ (by decide)
  have d12 : z 1 ≠ z 2 := hne _ _ (by decide)
  have d23 : z 2 ≠ z 3 := hne _ _ (by decide)
  have d34 : z 3 ≠ z 4 := hne _ _ (by decide)
  have d04 : z 0 ≠ z 4 := hne _ _ (by decide)
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  simp only [lexLt_iff d01, lexLt_iff d01.symm, lexLt_iff d12, lexLt_iff d12.symm, lexLt_iff d23,
    lexLt_iff d23.symm, lexLt_iff d34, lexLt_iff d34.symm, lexLt_iff d04, lexLt_iff d04.symm]
  unfold peaks5 at h
  convert h using 3

/-- Exactly one peak: only the adjacent comparisons and the absence of two peaks at distance two matter. -/
theorem peaks5_eq_one (a b c d e : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (n1 : ¬ ((e < a ∧ b < a) ∧ (b < c ∧ d < c))) (n2 : ¬ ((a < b ∧ c < b) ∧ (c < d ∧ e < d)))
    (n3 : ¬ ((b < c ∧ d < c) ∧ (d < e ∧ a < e))) (n4 : ¬ ((c < d ∧ e < d) ∧ (e < a ∧ b < a)))
    (n5 : ¬ ((d < e ∧ a < e) ∧ (a < b ∧ c < b))) : peaks5 a b c d e = 1 := by
  unfold peaks5
  rcases lt_or_gt_of_ne hab with a1 | a1 <;> rcases lt_or_gt_of_ne hbc with a2 | a2 <;>
    rcases lt_or_gt_of_ne hcd with a3 | a3 <;> rcases lt_or_gt_of_ne hde with a4 | a4 <;>
    rcases lt_or_gt_of_ne hea with a5 | a5 <;>
    first
      | (exfalso; linarith)
      | (exfalso; simp_all; done)
      | (simp [a1, a2, a3, a4, a5, not_lt.2 a1.le, not_lt.2 a2.le,
          not_lt.2 a3.le, not_lt.2 a4.le, not_lt.2 a5.le]; done)

/-- The pentagon cycle. -/
def cyc5 (A5 B5 z5 A2 B2 z2 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := fun i =>
  if i = 0 then (0, 0, 0) else if i = 1 then (1, 0, 0) else if i = 2 then (A5, B5, z5)
  else if i = 3 then (A2, B2, z2) else (0, 1, 0)

section
variable (A5 B5 z5 A2 B2 z2 : ℝ)
theorem cyc5_0 : cyc5 A5 B5 z5 A2 B2 z2 0 = (0, 0, 0) := by simp [cyc5]
theorem cyc5_1 : cyc5 A5 B5 z5 A2 B2 z2 1 = (1, 0, 0) := by
  have n : (1 : ZMod 5) ≠ 0 := by decide
  simp [cyc5, n]
theorem cyc5_2 : cyc5 A5 B5 z5 A2 B2 z2 2 = (A5, B5, z5) := by
  have n0 : (2 : ZMod 5) ≠ 0 := by decide
  have n1 : (2 : ZMod 5) ≠ 1 := by decide
  simp [cyc5, n0, n1]
theorem cyc5_3 : cyc5 A5 B5 z5 A2 B2 z2 3 = (A2, B2, z2) := by
  have n0 : (3 : ZMod 5) ≠ 0 := by decide
  have n1 : (3 : ZMod 5) ≠ 1 := by decide
  have n2 : (3 : ZMod 5) ≠ 2 := by decide
  simp [cyc5, n0, n1, n2]
theorem cyc5_4 : cyc5 A5 B5 z5 A2 B2 z2 4 = (0, 1, 0) := by
  have n0 : (4 : ZMod 5) ≠ 0 := by decide
  have n1 : (4 : ZMod 5) ≠ 1 := by decide
  have n2 : (4 : ZMod 5) ≠ 2 := by decide
  have n3 : (4 : ZMod 5) ≠ 3 := by decide
  simp [cyc5, n0, n1, n2, n3]
end

end H16U
end Minimality
