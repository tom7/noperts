module

public import Minimality.Type16SAT.ResW16

@[expose] public section

/-!
# Type 16: the residue `PL`, `r = 1`, `c = 0` at `a = 1`

`ResW16` closes the residue (`g = d = q = r = 1`, `x 1 - x 6` orthogonal to `x 0 - x 3` and `x 0 - x 6`,
`c = ⟪x 0 - x 3, x 6 - x 3⟫ = 0`) for `a ≠ 1`.  At `a = 1` (the zero of `[0126]` on `Z`; then `0 2 ∥ 3 5`) three split
leaves cover it, by the region of `p` and of the metric `e, h, L = ⟪E₁, E₁⟫, ⟪E₂, E₂⟫, ⟪E₃, E₃⟫`:
* `p > 1`: the leaf `F1` of `ResW16` (rim `4 1 5 3 0`, edge `15`, corner `4`); its rim tests need only `a ≤ 1`
  (`rimF1le`).
* `p ≤ 1`, `p (1 - b) h ≤ L`: rim `0 2 5 1 6`, edge `60`, corner `5` (the rim of the leaf `D`), at a view `l` with
  `e l₀ < (1 - b) h l₁`, `h l₁ < L l₂`, `p (1 - b) l₂ < (1 - b) l₀ + l₁`, `p l₁ < l₀ + l₂` (`rimDa`, `rowsDa`; the view
  exists, `exDa`: `lD` of `ResW16` for `h ≤ L`, an explicit polynomial view for `L < h`).
* `p ≤ 1`, `L < p (1 - b) h`: rim `0 2 4 5 1 6`, edge `24`, corner `6`, sign `-1`, at a view with
  `l₁ + (1 - b) l₀ < p (1 - b) l₂`, `l₀ + l₁ < p l₂`, `L l₂ < h l₁`, `e l₀ + b h l₁ < L l₂` (`rimN`, `rowsN`, `exN`).
Every rim test and split row is factored into linear forms of the view, each positive by the view's inequalities.
* `NF16.isRupert_PL_res1`: a normal form on the residue with `a = 1` is Rupert.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.NF16

variable {x : Fin 7 → ℝ³}

theorem rimN (b p l0 l1 l2 : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hp : 0 < p) (hp1 : 0 ≤ 1 - p)
    (h0 : 0 < l0) (h1 : 0 < l1) (h2 : 0 < l2)
    (n1 : l1 + (1 - b) * l0 < p * (1 - b) * l2) (n2 : l0 + l1 < p * l2) :
    RimOK 1 b p [(0, 2), (2, 4), (4, 5), (5, 1), (1, 6), (6, 0)] ![l0, l1, l2] := by
  have k1 : 0 < (1 - b) * l2 - l1 := by nlinarith [mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos hb1 h0]

  have c021 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 1 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c023 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 3 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c024 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 4 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c025 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 5 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c026 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 6 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c240 : 0 < resDet (resY 1 b p 4 - resY 1 b p 2) (resY 1 b p 0 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c241 : 0 < resDet (resY 1 b p 4 - resY 1 b p 2) (resY 1 b p 1 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (p) * (-b*l2 - l1 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c243 : 0 < resDet (resY 1 b p 4 - resY 1 b p 2) (resY 1 b p 3 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b*l0 - b*l2*p - l1 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c245 : 0 < resDet (resY 1 b p 4 - resY 1 b p 2) (resY 1 b p 5 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b*l0 - b*l2*p - l0 - l1 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c246 : 0 < resDet (resY 1 b p 4 - resY 1 b p 2) (resY 1 b p 6 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l2*p + l0 - l1*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c450 : 0 < resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 0 - resY 1 b p 4) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-l0 - l1 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c451 : 0 < resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 1 - resY 1 b p 4) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l1) * (p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c452 : 0 < resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 2 - resY 1 b p 4) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b*l0 - b*l2*p - l0 - l1 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c453 : 0 < resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 3 - resY 1 b p 4) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-l0 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c456 : 0 < resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 6 - resY 1 b p 4) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-l0 + l1*p + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c510 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 0 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c512 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 2 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 + l0 + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c513 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 3 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c514 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 4 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l1) * (p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c516 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 6 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c160 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 0 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c162 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 2 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c163 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 3 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c164 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 4 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l2) * (p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c165 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 5 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c601 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 1 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c602 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 2 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c603 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 3 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c604 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 4 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 - l1*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c605 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 5 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l1 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n2, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  intro A B m hAB h0 h1
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hAB
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    fin_cases m <;> first | exact absurd rfl h0 | exact absurd rfl h1 | assumption

theorem rowsN (b p e h L l0 l1 l2 : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hp : 0 < p) (hp1 : 0 ≤ 1 - p) (he : 0 < e) (hh : 0 < h)
    (h0 : 0 < l0) (h1 : 0 < l1) (h2 : 0 < l2)
    (n1 : l1 + (1 - b) * l0 < p * (1 - b) * l2) (n3 : L * l2 < h * l1)
    (n4 : e * l0 + b * h * l1 < L * l2) :
    RowsOK 1 b p e h L
      [(0, 2, 0), (0, 2, 2), (4, 5, 4), (4, 5, 5), (5, 1, 5), (5, 1, 1), (1, 6, 1), (6, 0, 0)]
      6 2 4 (-1) ![l0, l1, l2] := by
  have k1 : 0 < (1 - b) * l2 - l1 := by nlinarith [mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos hb1 h0]
  have r020 : 0 < (-1) * (resIp e h L (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (L*l2 - e*l0) * (b) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r022 : 0 < (-1) * (resIp e h L (resY 1 b p 2 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (L*l2 - b*h*l1 - e*l0) * (b) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r454 : 0 < (-1) * (resIp e h L (resY 1 b p 4 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (e*l0*p + h*l1) * (b*l0 - b*l2*p - l0 - l1 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r455 : 0 < (-1) * (resIp e h L (resY 1 b p 5 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 5 - resY 1 b p 4) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-L*l2 + h*l1) * (b*l0 - b*l2*p - l0 - l1 + l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r515 : 0 < (-1) * (resIp e h L (resY 1 b p 5 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-L*l2 + h*l1) * (-b*l0 + l0 - l1*p + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r511 : 0 < (-1) * (resIp e h L (resY 1 b p 1 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (h) * (l1) * (-b*l0 + l0 - l1*p + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r161 : 0 < (-1) * (resIp e h L (resY 1 b p 1 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (h) * (l1) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r600 : 0 < (-1) * (resIp e h L (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2] *
      resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (L*l2 - e*l0) * (-b*l0 - b*l2 + l0 - l1*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [n1, n3, n4, k1, mul_pos hp k1, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hh) h1, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le, mul_pos he h0, mul_pos hh h1])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  intro A B J hAB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hAB
  rcases hAB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> assumption

theorem rimDa (b p l0 l1 l2 : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hp : 0 < p) (hp1 : 0 ≤ 1 - p)
    (h0 : 0 < l0) (h1 : 0 < l1) (h2 : 0 < l2) (d3 : p * (1 - b) * l2 < (1 - b) * l0 + l1)
    (d4 : p * l1 < l0 + l2) :
    RimOK 1 b p [(0, 2), (2, 5), (5, 1), (1, 6), (6, 0)] ![l0, l1, l2] := by

  have c021 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 1 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c023 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 3 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c024 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 4 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 - l2*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c025 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 5 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c026 : 0 < resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 6 - resY 1 b p 0) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c250 : 0 < resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 0 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c251 : 0 < resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 1 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 + l0 + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c253 : 0 < resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 3 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c254 : 0 < resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 4 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 + b*l2*p + l0 + l1 - l2*p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c256 : 0 < resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 6 - resY 1 b p 2) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 + l0 + l1 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c510 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 0 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c512 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 2 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 + l0 + l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c513 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 3 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c514 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 4 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l1) * (p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c516 : 0 < resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 6 - resY 1 b p 5) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c160 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 0 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c162 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 2 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c163 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 3 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c164 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 4 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l2) * (p) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c165 : 0 < resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 5 - resY 1 b p 1) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c601 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 1 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c602 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 2 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (b) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c603 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 3 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c604 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 4 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 - l1*p + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have c605 : 0 < resDet (resY 1 b p 0 - resY 1 b p 6) (resY 1 b p 5 - resY 1 b p 6) ![l0, l1, l2] :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l1 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d3, d4, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_nonneg hp1 h0.le, mul_nonneg hp1 h1.le, mul_nonneg hp1 h2.le, mul_pos hp h0, mul_pos hp h1, mul_pos hp h2, mul_pos (mul_pos hb hp) h2, mul_nonneg (mul_nonneg hp1 hb1.le) h2.le])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  intro A B m hAB h0 h1
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hAB
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    fin_cases m <;> first | exact absurd rfl h0 | exact absurd rfl h1 | assumption

theorem rowsDa (b p e h L l0 l1 l2 : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hh : 0 < h) (hL : 0 < L)
    (h0 : 0 < l0) (h1 : 0 < l1) (h2 : 0 < l2)
    (d1 : e * l0 < (1 - b) * h * l1) (d2 : h * l1 < L * l2) :
    RowsOK 1 b p e h L
      [(0, 2, 0), (0, 2, 2), (2, 5, 2), (5, 1, 1), (1, 6, 1), (1, 6, 6)]
      5 6 0 (1) ![l0, l1, l2] := by
  have r020 : 0 < 1 * (resIp e h L (resY 1 b p 0 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) * (b) * (-e*l0 + h*l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r022 : 0 < 1 * (resIp e h L (resY 1 b p 2 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 2 - resY 1 b p 0) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) * (b) * (-b*h*l1 - e*l0 + h*l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r252 : 0 < 1 * (resIp e h L (resY 1 b p 2 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 5 - resY 1 b p 2) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (-b*l0 - b*l2 + l0 + l1 + l2) * (-b*h*l1 - e*l0 + h*l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r511 : 0 < 1 * (resIp e h L (resY 1 b p 1 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 1 - resY 1 b p 5) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (L) * (l1) * (l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r161 : 0 < 1 * (resIp e h L (resY 1 b p 1 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (L) * (l2) * (l0 + l2) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  have r166 : 0 < 1 * (resIp e h L (resY 1 b p 6 - resY 1 b p 5) ![l0, l1, l2] *
      resDet (resY 1 b p 6 - resY 1 b p 1) (resY 1 b p 0 - resY 1 b p 6) ![l0, l1, l2]) :=
    lt_of_lt_of_eq (show (0 : ℝ) < (l0 + l2) * (L*l2 - h*l1) by
      (try apply_rules [mul_pos, pow_pos]) <;> first | positivity | linarith [d1, d2, mul_pos hb h0, mul_pos hb h1, mul_pos hb h2, mul_pos hb1 h0, mul_pos hb1 h1, mul_pos hb1 h2, mul_pos (mul_pos hb hh) h1, mul_pos hh h1, mul_pos hL h2])
      (by simp only [resY, resDet, resIp, det3c, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; ring)
  intro A B J hAB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hAB
  rcases hAB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> assumption


/-- A view for the leaf `Da` (`p (1 - b) h ≤ L`). -/
theorem exDa (b p e h L : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hp : 0 < p) (hp1 : 0 ≤ 1 - p) (he : 0 < e)
    (hh : 0 < h) (hL : 0 < L) (hk : p * (1 - b) * h ≤ L) :
    ∃ l0 l1 l2 : ℝ, 0 < l0 ∧ 0 < l1 ∧ 0 < l2 ∧ e * l0 < (1 - b) * h * l1 ∧ h * l1 < L * l2 ∧
      p * (1 - b) * l2 < (1 - b) * l0 + l1 ∧ p * l1 < l0 + l2 := by
  rcases le_or_gt h L with hLh | hLh
  · refine ⟨2 * (1 - b) * h, 4 * e, 4 * e + (1 - b) * h, by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
    · nlinarith [mul_pos (mul_pos he hb1) hh]
    · nlinarith [mul_nonneg he.le (sub_nonneg.2 hLh), mul_pos (mul_pos hb1 hh) hL]
    · nlinarith [mul_pos (mul_pos hb1 hb1) hh, mul_pos he hb,
        mul_nonneg (mul_nonneg hp1 hb1.le) (by positivity : (0 : ℝ) ≤ 4 * e + (1 - b) * h)]
    · nlinarith [mul_pos hb1 hh, mul_nonneg he.le hp1]
  · have hk' : 0 ≤ L - p * (1 - b) * h := by linarith
    have hm : 0 < h - L := by linarith
    refine ⟨(1 - b) * h * L * (2 * e * p + (1 - b) * L), 2 * e * L * (2 * e * p + (1 - b) * L),
      2 * e * h * (2 * e * p + 2 * (1 - b) * L), by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
    · nlinarith [show 0 < e * (1 - b) * h * L * (2 * e * p + (1 - b) * L) by positivity]
    · nlinarith [show 0 < 2 * e * h * L * (1 - b) * L by positivity]
    · nlinarith [show 0 < (1 - b) ^ 3 * h * L ^ 2 by positivity,
        mul_nonneg (show (0 : ℝ) ≤ 4 * e ^ 2 * p by positivity) hk',
        mul_nonneg (show (0 : ℝ) ≤ 2 * e * (1 - b) * L by positivity) hk']
    · nlinarith [show 0 < (1 - b) * h * L * (2 * e * p + (1 - b) * L) by positivity,
        mul_nonneg (show (0 : ℝ) ≤ 2 * e * L * (2 * e * p) by positivity) hp1,
        mul_nonneg (show (0 : ℝ) ≤ 2 * e * L * ((1 - b) * L) by positivity) hp1,
        show 0 < 2 * e * L * ((1 - b) * L) by positivity,
        mul_pos (show (0 : ℝ) < 2 * e * (2 * e * p + 2 * (1 - b) * L) by positivity) hm]

/-- A view for the leaf `N` (`L < p (1 - b) h`). -/
theorem exN (b p e h L : ℝ) (hb : 0 < b) (hb1 : 0 < 1 - b) (hp : 0 < p) (he : 0 < e)
    (hh : 0 < h) (hL : 0 < L) (hk : L < p * (1 - b) * h) :
    ∃ l0 l1 l2 : ℝ, 0 < l0 ∧ 0 < l1 ∧ 0 < l2 ∧ l1 + (1 - b) * l0 < p * (1 - b) * l2 ∧ l0 + l1 < p * l2 ∧
      L * l2 < h * l1 ∧ e * l0 + b * h * l1 < L * l2 := by
  have hδ : 0 < p * (1 - b) * h - L := by linarith
  have hX : 0 < (1 - b) * L := by positivity
  have hY : 0 < (1 - b) * L * h / (4 * e) := by positivity
  have hu0 : 0 < min (p * (1 - b) * h - L) ((1 - b) * L) / 4 := div_pos (lt_min hδ hX) (by norm_num)
  have hu1 : min (p * (1 - b) * h - L) ((1 - b) * L) / 4 ≤ (p * (1 - b) * h - L) / 4 := by
    have := min_le_left (p * (1 - b) * h - L) ((1 - b) * L); linarith
  have hu2 : min (p * (1 - b) * h - L) ((1 - b) * L) / 4 ≤ (1 - b) * L / 4 := by
    have := min_le_right (p * (1 - b) * h - L) ((1 - b) * L); linarith
  have hv0 : 0 < min ((p * (1 - b) * h - L) / 4) ((1 - b) * L * h / (4 * e)) :=
    lt_min (by linarith) hY
  have hv1 : min ((p * (1 - b) * h - L) / 4) ((1 - b) * L * h / (4 * e)) ≤ (p * (1 - b) * h - L) / 4 :=
    min_le_left _ _
  have hv2 : e * min ((p * (1 - b) * h - L) / 4) ((1 - b) * L * h / (4 * e)) ≤ (1 - b) * L * h / 4 := by
    calc e * min ((p * (1 - b) * h - L) / 4) ((1 - b) * L * h / (4 * e))
        ≤ e * ((1 - b) * L * h / (4 * e)) := mul_le_mul_of_nonneg_left (min_le_right _ _) he.le
      _ = (1 - b) * L * h / 4 := by field_simp
  set u := min (p * (1 - b) * h - L) ((1 - b) * L) / 4
  set v := min ((p * (1 - b) * h - L) / 4) ((1 - b) * L * h / (4 * e))
  have hbu : b * h * u ≤ b * h * ((1 - b) * L / 4) := mul_le_mul_of_nonneg_left hu2 (by positivity)
  refine ⟨v, L + u, h, hv0, by linarith, hh, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos hb hv0]
  · nlinarith [mul_pos (mul_pos hp hb) hh]
  · nlinarith [mul_pos hh hu0]
  · nlinarith [mul_pos (mul_pos (mul_pos hb1 hL) hh) (show (0 : ℝ) < 3 - b by linarith)]

/-- The rim of the leaf `N`. -/
def labN : ZMod 6 → Fin 7 := ![0, 2, 4, 5, 1, 6]

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 4096 in
theorem rlN : ∀ i j : ZMod 6, i ≠ 1 → (j = i ∨ j = i + 1) → j ≠ 5 →
    (labN i, labN (i + 1), labN j) ∈
      ([(0, 2, 0), (0, 2, 2), (4, 5, 4), (4, 5, 5), (5, 1, 5), (5, 1, 1), (1, 6, 1), (6, 0, 0)]
        : List (Fin 7 × Fin 7 × Fin 7)) := by decide

/-- **The residue at `a = 1` is Rupert.**  A type 16 normal form on `Z` (`g = d = q = 1`) with `x 1 - x 6` orthogonal
to `x 0 - x 3` and `x 0 - x 6`, `r = 1`, `⟪x 0 - x 3, x 6 - x 3⟫ = 0` and `a = 1` is Rupert: the leaf `F1` (`p > 1`),
`Da` (`p ≤ 1`, `p (1 - b) h ≤ L`) or `N` (`p ≤ 1`, `L < p (1 - b) h`). -/
theorem isRupert_PL_res1 (N : NF16 x) (F : H21.S0xFac 8 Minimality.V2.fIdx x)
    (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h1 : ⟪x 0 - x 3, x 1 - x 6⟫ = 0) (h2 : ⟪x 0 - x 6, x 1 - x 6⟫ = 0) (hr : N.r = 1)
    (hc : ⟪x 0 - x 3, x 6 - x 3⟫ = 0) (ha1 : N.a = 1) : IsRupert (univ.image x) := by
  obtain ⟨he, hh, hL⟩ := res_metric_pos N
  have ha := N.ha
  have hb := N.hb
  have hp := N.hp
  have hb1 : 0 < 1 - N.b := by
    have t := N.tB125
    rw [hg, hd, hq] at t
    nlinarith
  rcases lt_or_ge 1 N.p with hp1 | hp1
  · exact isRupert_res_split N F hg hd hq hr h1 h2 hc (k := 5) (by norm_num) labF1 (by decide) 1 0
      (by decide) (by decide) 1 (lF1 N.p ⟪N.E₁, N.E₁⟫ ⟪N.E₂, N.E₂⟫ ⟪N.E₃, N.E₃⟫)
      [(4, 1), (1, 5), (5, 3), (3, 0), (0, 4)] (by decide)
      (rimF1le _ _ _ _ _ _ ha hb hb1 he hh hL (by rw [ha1]; norm_num) hp (by linarith)) 4 1 5 (by decide)
      (by decide) (by decide)
      [(4, 1, 1), (5, 3, 5), (5, 3, 3), (3, 0, 3), (3, 0, 0), (0, 4, 0)] rlF1
      (rowsF1 _ _ _ _ _ _ he hh hL hp (by linarith))
  have hp1' : 0 ≤ 1 - N.p := by linarith
  rcases le_or_gt (N.p * (1 - N.b) * ⟪N.E₂, N.E₂⟫) ⟪N.E₃, N.E₃⟫ with hk | hk
  · obtain ⟨l0, l1, l2, p0, p1, p2, d1, d2, d3, d4⟩ := exDa _ _ _ _ _ hb hb1 hp hp1' he hh hL hk
    exact isRupert_res_split N F hg hd hq hr h1 h2 hc (k := 5) (by norm_num) labAD (by decide) 4 2
      (by decide) (by decide) 1 ![l0, l1, l2]
      [(0, 2), (2, 5), (5, 1), (1, 6), (6, 0)] (by decide)
      (by rw [ha1]; exact rimDa _ _ _ _ _ hb hb1 hp hp1' p0 p1 p2 d3 d4) 5 6 0 (by decide)
      (by decide) (by decide) [(0, 2, 0), (0, 2, 2), (2, 5, 2), (5, 1, 1), (1, 6, 1), (1, 6, 6)] rlD
      (by rw [ha1]; exact rowsDa _ _ _ _ _ _ _ _ hb hb1 hh hL p0 p1 p2 d1 d2)
  · obtain ⟨l0, l1, l2, p0, p1, p2, n1, n2, n3, n4⟩ := exN _ _ _ _ _ hb hb1 hp he hh hL hk
    exact isRupert_res_split N F hg hd hq hr h1 h2 hc (k := 6) (by norm_num) labN (by decide) 1 5
      (by decide) (by decide) (-1) ![l0, l1, l2]
      [(0, 2), (2, 4), (4, 5), (5, 1), (1, 6), (6, 0)] (by decide)
      (by rw [ha1]; exact rimN _ _ _ _ _ hb hb1 hp hp1' p0 p1 p2 n1 n2) 6 2 4 (by decide)
      (by decide) (by decide)
      [(0, 2, 0), (0, 2, 2), (4, 5, 4), (4, 5, 5), (5, 1, 5), (5, 1, 1), (1, 6, 1), (6, 0, 0)] rlN
      (by rw [ha1]; exact rowsN _ _ _ _ _ _ _ _ hb hb1 hp hp1' he hh p0 p1 p2 n1 n3 n4)

end Minimality.NF16
