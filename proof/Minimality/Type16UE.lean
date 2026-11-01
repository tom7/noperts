module

public import Minimality.Type16UA
public import Minimality.Type16V2Uni4

@[expose] public section


/-!
# U1: the quadrilateral screen cycle `(0,0), (1,0), (A,B), (0,1)` for EV1 (type-free)

`h16u_ev1_cyc4`: frame `(p, q, r, d)`; corners `d`, `d + p`, `fpoint (A,B,z5)`, `d + q`; every other point of `V`
is strictly inside the quadrilateral, or over the corner `Y 0` with `z < 0` (the other end of the viewed edge).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
theorem zmod5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

/-- The quadrilateral cycle. -/
def cyc4 (A B z : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := fun i =>
  if i = 0 then (0, 0, 0) else if i = 1 then (1, 0, 0) else if i = 2 then (A, B, z) else (0, 1, 0)

theorem cyc4_0 (A B z : ℝ) : cyc4 A B z 0 = (0, 0, 0) := by simp [cyc4]
theorem cyc4_1 (A B z : ℝ) : cyc4 A B z 1 = (1, 0, 0) := by
  have n10 : (1 : ZMod 4) ≠ 0 := by decide
  simp [cyc4, n10]
theorem cyc4_2 (A B z : ℝ) : cyc4 A B z 2 = (A, B, z) := by
  have n20 : (2 : ZMod 4) ≠ 0 := by decide
  have n21 : (2 : ZMod 4) ≠ 1 := by decide
  simp [cyc4, n20, n21]
theorem cyc4_3 (A B z : ℝ) : cyc4 A B z 3 = (0, 1, 0) := by
  have n30 : (3 : ZMod 4) ≠ 0 := by decide
  have n31 : (3 : ZMod 4) ≠ 1 := by decide
  have n32 : (3 : ZMod 4) ≠ 2 := by decide
  simp [cyc4, n30, n31, n32]

theorem cyc4_hconv (A B z : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : 1 < A + B) :
    ∀ i j, j ≠ i → j ≠ i + 1 → 0 < TwoRay.cross2 (cyc4 A B z (i + 1) - cyc4 A B z i) (cyc4 A B z j - cyc4 A B z i) := by
  intro i j hji hj
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hji
      | exact absurd (by decide) hj
      | (simp only [TwoRay.cross2, cyc4_0, cyc4_1, cyc4_2, cyc4_3, show (0 : ZMod 4) + 1 = 1 from rfl,
          show (1 : ZMod 4) + 1 = 2 from rfl, show (2 : ZMod 4) + 1 = 3 from rfl,
          show (3 : ZMod 4) + 1 = 0 from rfl, Prod.mk_sub_mk]
         nlinarith)

theorem cyc4_inside (A B z a b w : ℝ) (h1 : 0 < b) (h2 : 0 < (A - 1) * b - B * (a - 1))
    (h3 : 0 < -A * (b - B) - (1 - B) * (a - A)) (h4 : 0 < a) :
    ∀ i, 0 < TwoRay.cross2 (cyc4 A B z (i + 1) - cyc4 A B z i) ((a, b, w) - cyc4 A B z i) := by
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · simp only [TwoRay.cross2, cyc4_0, cyc4_1, show (0 : ZMod 4) + 1 = 1 from rfl, Prod.mk_sub_mk]; nlinarith
  · simp only [TwoRay.cross2, cyc4_1, cyc4_2, show (1 : ZMod 4) + 1 = 2 from rfl, Prod.mk_sub_mk]; nlinarith
  · simp only [TwoRay.cross2, cyc4_2, cyc4_3, show (2 : ZMod 4) + 1 = 3 from rfl, Prod.mk_sub_mk]; nlinarith
  · simp only [TwoRay.cross2, cyc4_3, cyc4_0, show (3 : ZMod 4) + 1 = 0 from rfl, Prod.mk_sub_mk]; nlinarith

/-- Peak count one for four distinct values without the two alternating patterns. -/
theorem peaks4_eq_one (a b c d : ℝ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (h1 : ¬ (b < a ∧ d < a ∧ b < c ∧ d < c)) (h2 : ¬ (a < b ∧ c < b ∧ a < d ∧ c < d)) :
    V2.peaks4 a b c d = 1 := by
  unfold V2.peaks4
  rcases lt_or_gt_of_ne hab with a1 | a1 <;> rcases lt_or_gt_of_ne hac with a2 | a2 <;>
    rcases lt_or_gt_of_ne had with a3 | a3 <;> rcases lt_or_gt_of_ne hbc with a4 | a4 <;>
    rcases lt_or_gt_of_ne hbd with a5 | a5 <;> rcases lt_or_gt_of_ne hcd with a6 | a6 <;>
    first
      | (exfalso; linarith)
      | (exfalso; exact h1 ⟨by linarith, by linarith, by linarith, by linarith⟩)
      | (exfalso; exact h2 ⟨by linarith, by linarith, by linarith, by linarith⟩)
      | (simp [a1, a2, a3, a4, a5, a6, a1.le, a2.le, a3.le, a4.le, a5.le, a6.le, not_lt.2 a1.le, not_lt.2 a2.le,
          not_lt.2 a3.le, not_lt.2 a4.le, not_lt.2 a5.le, not_lt.2 a6.le]; done)

set_option maxHeartbeats 1600000 in
/-- **EV1 on the quadrilateral cycle** (strict depths: distinct, no alternating pattern). -/
theorem h16u_ev1_cyc4 (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) (A B z5 : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hAB : 1 < A + B)
    (hm1 : d + p ∈ V) (hm0 : d ∈ V) (hm2 : fpoint p q r d (A, B, z5) ∈ V) (hm3 : d + q ∈ V)
    (h01 : ⟪d, r⟫ ≠ ⟪d + p, r⟫) (h02 : ⟪d, r⟫ ≠ ⟪fpoint p q r d (A, B, z5), r⟫) (h03 : ⟪d, r⟫ ≠ ⟪d + q, r⟫)
    (h12 : ⟪d + p, r⟫ ≠ ⟪fpoint p q r d (A, B, z5), r⟫) (h13 : ⟪d + p, r⟫ ≠ ⟪d + q, r⟫)
    (h23 : ⟪fpoint p q r d (A, B, z5), r⟫ ≠ ⟪d + q, r⟫)
    (hn1 : ¬ (⟪d + p, r⟫ < ⟪d, r⟫ ∧ ⟪d + q, r⟫ < ⟪d, r⟫ ∧ ⟪d + p, r⟫ < ⟪fpoint p q r d (A, B, z5), r⟫ ∧
      ⟪d + q, r⟫ < ⟪fpoint p q r d (A, B, z5), r⟫))
    (hn2 : ¬ (⟪d, r⟫ < ⟪d + p, r⟫ ∧ ⟪fpoint p q r d (A, B, z5), r⟫ < ⟪d + p, r⟫ ∧ ⟪d, r⟫ < ⟪d + q, r⟫ ∧
      ⟪fpoint p q r d (A, B, z5), r⟫ < ⟪d + q, r⟫))
    (hV : ∀ y ∈ V, y ≠ d → y ≠ d + p → y ≠ fpoint p q r d (A, B, z5) → y ≠ d + q →
      ∃ a b z : ℝ, y = fpoint p q r d (a, b, z) ∧
        ((0 < a ∧ 0 < b ∧ 0 < (A - 1) * b - B * (a - 1) ∧ 0 < -A * (b - B) - (1 - B) * (a - A)) ∨
          (a = 0 ∧ b = 0 ∧ z < 0))) :
    HasLexCellAt V r := by
  have e0 : fpoint p q r d (cyc4 A B z5 0) = d := by simp [cyc4_0, fpoint, fcomb]
  have e1 : fpoint p q r d (cyc4 A B z5 1) = d + p := by simp [cyc4_1, fpoint, fcomb]
  have e2 : fpoint p q r d (cyc4 A B z5 2) = fpoint p q r d (A, B, z5) := by rw [cyc4_2]
  have e3 : fpoint p q r d (cyc4 A B z5 3) = d + q := by simp [cyc4_3, fpoint, fcomb]
  have hmem : ∀ i, fpoint p q r d (cyc4 A B z5 i) ∈ V := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [e0]; exact hm0
    · rw [e1]; exact hm1
    · rw [e2]; exact hm2
    · rw [e3]; exact hm3
  have hdist : ∀ i j, ⟪fpoint p q r d (cyc4 A B z5 i), r⟫ = ⟪fpoint p q r d (cyc4 A B z5 j), r⟫ → i = j := by
    intro i j h
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3] at h <;>
      first
        | rfl
        | exact absurd h h01 | exact absurd h.symm h01 | exact absurd h h02 | exact absurd h.symm h02
        | exact absurd h h03 | exact absurd h.symm h03 | exact absurd h h12 | exact absurd h.symm h12
        | exact absurd h h13 | exact absurd h.symm h13 | exact absurd h h23 | exact absurd h.symm h23
  have hdep : LexUni (fun i => ⟪fpoint p q r d (cyc4 A B z5 i), r⟫) (fun _ => 0) := by
    refine lexUni4_of _ hdist ?_
    simp only [e0, e1, e2, e3]
    exact peaks4_eq_one _ _ _ _ h01 h02 h03 h12 h13 h23 hn1 hn2
  have hm : (-1 : ZMod 4) = 3 := by decide
  refine h16u_ev1_hasLexCellAt V p q r d hΔ (k := 4) (by norm_num) (cyc4 A B z5) (cyc4_0 A B z5) (cyc4_1 A B z5)
    (by rw [hm]; exact cyc4_3 A B z5) hmem (cyc4_hconv A B z5 hA hB hAB) hdep (σP := 1) (σQ := 1) one_ne_zero
    one_ne_zero ?_
  intro y hy hyx
  have hy0 : y ≠ d := fun h => hyx 0 (by rw [e0]; exact h)
  have hy1 : y ≠ d + p := fun h => hyx 1 (by rw [e1]; exact h)
  have hy2 : y ≠ fpoint p q r d (A, B, z5) := fun h => hyx 2 (by rw [e2]; exact h)
  have hy3 : y ≠ d + q := fun h => hyx 3 (by rw [e3]; exact h)
  obtain ⟨a, b, z, hyz, hc⟩ := hV y hy hy0 hy1 hy2 hy3
  refine ⟨(a, b, z), hyz, ?_⟩
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨rfl, rfl, hz⟩
  · exact Or.inl (cyc4_inside A B z5 a b z h2 h3 h4 h1)
  · exact Or.inr (Or.inr (Or.inr ⟨z, rfl, by linarith, by linarith⟩))

end H16U
end Minimality
