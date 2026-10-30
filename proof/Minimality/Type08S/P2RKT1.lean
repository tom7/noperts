module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT1: coordinate toolkit in a frame `p, q, r` (`det3 p q r ≠ 0`).
`det3_coord`, `tiltSign_coord`: determinants of frame combinations are `Δ` times a 3×3 polynomial;
`lexUni_four`: a 4-cycle of lex pairs with equal first components is lex unimodal.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Frame combination. -/
noncomputable def fcomb (p q r : ℝ³) (x y z : ℝ) : ℝ³ := x • p + y • q + z • r

/-- Polynomial of the 3×3 determinant. -/
def d3 (x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) : ℝ :=
  x1 * (y2 * z3 - z2 * y3) - y1 * (x2 * z3 - z2 * x3) + z1 * (x2 * y3 - y2 * x3)

theorem det3_coord (p q r : ℝ³) (x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) :
    det3 (fcomb p q r x1 y1 z1) (fcomb p q r x2 y2 z2) (fcomb p q r x3 y3 z3) =
      det3 p q r * d3 x1 y1 z1 x2 y2 z2 x3 y3 z3 := by
  simp only [fcomb, d3, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring


theorem fcomb_zero (p q r : ℝ³) : fcomb p q r 0 0 0 = 0 := by simp [fcomb]

theorem fcomb_sub (p q r : ℝ³) (x y z x' y' z' : ℝ) :
    fcomb p q r x y z - fcomb p q r x' y' z' = fcomb p q r (x - x') (y - y') (z - z') := by
  simp only [fcomb]; module

theorem inner_fcomb_left (p q r w : ℝ³) (x y z : ℝ) :
    ⟪fcomb p q r x y z, w⟫ = x * ⟪p, w⟫ + y * ⟪q, w⟫ + z * ⟪r, w⟫ := by
  simp only [fcomb, inner_add_left, real_inner_smul_left]

/-- Sign condition of one tilt test in frame coordinates (`Δ = det3 p q r`). -/
def TSc (Δ : ℝ) (e f v : ℝ × ℝ × ℝ) : Prop :=
  0 < Δ * d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1 ∨
    (Δ * d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1 = 0 ∧
      0 < Δ * d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 v.1 v.2.1 v.2.2)

theorem tiltSign_fcomb (p q r : ℝ³) {e f v : ℝ × ℝ × ℝ} (h : TSc (det3 p q r) e f v) :
    TiltSign (fcomb p q r e.1 e.2.1 e.2.2) (fcomb p q r f.1 f.2.1 f.2.2) r
      (fcomb p q r v.1 v.2.1 v.2.2) := by
  have hr : fcomb p q r 0 0 1 = r := by simp [fcomb]
  have e0 := det3_coord p q r e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1
  have e1 := det3_coord p q r e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 v.1 v.2.1 v.2.2
  rw [hr] at e0
  unfold TiltSign
  rw [e0, e1]
  exact h

/-- The point with frame coordinates `t` over the base point `d`. -/
noncomputable def fpoint (p q r d : ℝ³) (t : ℝ × ℝ × ℝ) : ℝ³ := d + fcomb p q r t.1 t.2.1 t.2.2

theorem fpoint_sub (p q r d : ℝ³) (s t : ℝ × ℝ × ℝ) :
    fpoint p q r d s - fpoint p q r d t = fcomb p q r (s - t).1 (s - t).2.1 (s - t).2.2 := by
  simp only [fpoint, Prod.fst_sub, Prod.snd_sub]
  rw [add_sub_add_left_eq_sub, fcomb_sub]

/-- **Toolkit: a lex cell from frame coordinates.**  Cycle `X` of frame points (over `d`), tilt `v` in frame
coordinates, base view `r`; every test is a `TSc` sign condition; the other points of `V` are given by
coordinates. -/
theorem lexCell_coord (V : Finset ℝ³) (p q r d : ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ × ℝ × ℝ) (v : ℝ × ℝ × ℝ) (hV : ∀ i, fpoint p q r d (X i) ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TSc (det3 p q r) (X (i + 1) - X i) (X j - X i) v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (X j)) →
      ∃ t, y = fpoint p q r d t ∧ ∀ i, TSc (det3 p q r) (X (i + 1) - X i) (t - X i) v)
    (hlex : LexUni (fun i => ⟪fpoint p q r d (X i), r⟫) (fun i => ⟪fpoint p q r d (X i), fcomb p q r v.1 v.2.1 v.2.2⟫)) :
    LexCell V r (fcomb p q r v.1 v.2.1 v.2.2) (fun i => fpoint p q r d (X i)) := by
  refine ⟨hk, hV, fun i j h1 h2 => ?_, fun y hy hyx i => ?_, hlex⟩
  · rw [fpoint_sub, fpoint_sub]; exact tiltSign_fcomb p q r (hcyc i j h1 h2)
  · obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
    rw [fpoint_sub, fpoint_sub]; exact tiltSign_fcomb p q r (ht i)

set_option linter.unusedSimpArgs false in
theorem lexUni_four (z w : ZMod 4 → ℝ) (hz : ∀ i j, z i = z j) (hw : ∀ i j, i ≠ j → w i ≠ w j)
    (hna1 : ¬ (max (w 1) (w 3) < min (w 0) (w 2)))
    (hna2 : ¬ (max (w 0) (w 2) < min (w 1) (w 3))) : LexUni z w := by
  classical
  refine ⟨fun i j _ h => by_contra fun hne => hw i j hne h, ?_⟩
  have h01 := lt_or_gt_of_ne (hw 0 1 (by decide))
  have h02 := lt_or_gt_of_ne (hw 0 2 (by decide))
  have h03 := lt_or_gt_of_ne (hw 0 3 (by decide))
  have h12 := lt_or_gt_of_ne (hw 1 2 (by decide))
  have h13 := lt_or_gt_of_ne (hw 1 3 (by decide))
  have h23 := lt_or_gt_of_ne (hw 2 3 (by decide))
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have f0 : (0 : ZMod 4) + 1 = 1 := by decide
  have f1 : (1 : ZMod 4) + 1 = 2 := by decide
  have f2 : (2 : ZMod 4) + 1 = 3 := by decide
  have f3 : (3 : ZMod 4) + 1 = 0 := by decide
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) = 1
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  have hl : ∀ i j : ZMod 4, LexLt (z i, w i) (z j, w j) ↔ w i < w j := by
    intro i j; simp [LexLt, hz i j]
  simp only [hl]
  rcases h01 with h01 | h01 <;> rcases h02 with h02 | h02 <;> rcases h03 with h03 | h03 <;>
  rcases h12 with h12 | h12 <;> rcases h13 with h13 | h13 <;> rcases h23 with h23 | h23 <;>
  first
  | (exfalso; linarith)
  | (simp [h01, (not_lt_of_gt h01), h02, (not_lt_of_gt h02), h03, (not_lt_of_gt h03), h12, (not_lt_of_gt h12), h13, (not_lt_of_gt h13),
      h23, (not_lt_of_gt h23)]; done)
  | (exfalso; simp [h01, (not_lt_of_gt h01), h02, (not_lt_of_gt h02), h03, (not_lt_of_gt h03), h12, (not_lt_of_gt h12), h13,
      (not_lt_of_gt h13), h23, (not_lt_of_gt h23)] at hna1 hna2)


end Type08Sp
end Minimality
