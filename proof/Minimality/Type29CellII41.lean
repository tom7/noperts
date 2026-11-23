module

public import Minimality.Type29CellII

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`, Task L41 (`A41-REFEREE`): the line `F012 × F124` (view `v12 = x2 - x1`)

Formalizes the surviving pieces of Carbon A41 as refereed in `A41-REFEREE.md` (corrected identities only):
* `L41-1a/b`: the facet values at `v12`; the region bounds (`P2 < s`, `a2 + b2 + h2 > 0`, `D234 < t`, `1 - b2 - h2 > 0`).
* `L41-1c/d`: the case `2A` (`b2 + h2 t ≤ 0`) and `2B` (`b2 + h2 t > 0`) identities, the `False`-lemmas and the leaf
  `l41_v12_closes`.  The two rim steps ("RU on `(0,2,4,6,5)`", "not RU on `(0,1,4,6,5)` forces `V12_10 ≥ 0`") are the
  named hypotheses `RimStepA29`, `RimStepB29`; they are lean-sem facts, NOT proved here.
* `L41-1e`, `L41-3`: the corrected Radon identities (`+a2` resp. `+b2` times `v012`) and the collapse `False`-lemmas.
* `L41-2` (Part 1A, `F-B × {C_Q2, C_Q5-}` on `chi < 0`): the corrected `G`-form identities (`l41_CQ5`, `l41_CQ5'`,
  `l41_B05_eq`, `l41_B04_eq`, `l41_B05_zero`, `l41_B04_zero`, `l41_K04_eq`, `l41_FB{1,2,3}_sum`) and the
  `False`-lemmas `l41_FB{1,2,3}_false` on the six valid rows; only the sub-case `del05 ≥ 0` is formalized
  (hypothesis of `L41Facts`); the cancellation of a negative `del05` and the case `w5 ≤ 0, w4' ≥ 0` are not.
  `FB-3` takes `w4' < 0` as hypothesis (referee failure F4).

Carbon ↔ Lean naming as in `Type29CellII`: Carbon `P4 = N.P5 = P4C_sp`, Carbon `P5 = N.P4 = P5C_sp`, `D0 = N.D02`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

section L41Real

variable (a0 b0 h0 a2 b2 h2 s t : ℝ)

/-! ## L41-1b: bounds (ring identities) -/

theorem l41_b_id1 : (1 - t) * (P5C_sp a0 h0 a2 h2 - P4C_sp b0 h0 b2 h2) =
    v4_sp a0 b0 h0 a2 b2 h2 s t + S_sp s t * P4C_sp b0 h0 b2 h2 := by
  dsimp only [P5C_sp, P4C_sp, v4_sp, S_sp]; ring

theorem l41_b_id2 : b2 * P5C_sp a0 h0 a2 h2 =
    -h2 * D0_sp a0 b0 a2 b2 - a2 * P4C_sp b0 h0 b2 h2 := by
  dsimp only [P5C_sp, P4C_sp, D0_sp]; ring

theorem l41_b_id3 : P4C_sp b0 h0 b2 h2 * (a2 + b2 + h2) =
    h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) +
      (-b2) * (P5C_sp a0 h0 a2 h2 - P4C_sp b0 h0 b2 h2) := by
  dsimp only [P5C_sp, P4C_sp, D0_sp]; ring

theorem l41_b_id4 : (1 - t) * P4C_sp b0 h0 b2 h2 * (s - P2_sp a2 b2 h2 s t) =
    s * (1 - t) * h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) +
      s * (-b2) * v4_sp a0 b0 h0 a2 b2 h2 s t + S_sp s t * P4C_sp b0 h0 b2 h2 * qA4_sp a2 b2 s t := by
  dsimp only [P5C_sp, P4C_sp, D0_sp, v4_sp, S_sp, P2_sp, qA4_sp]; ring

theorem l41_b_id5 : DG5_sp a0 b0 h0 a2 b2 h2 =
    (-a0) * (1 - b2 - h2) - (-a2) * (1 - b0 - h0) := by
  dsimp only [DG5_sp, D0_sp, G5_sp]; ring

theorem l41_b_id6 : P4C_sp b0 h0 b2 h2 * (D234_sp a2 b2 h2 s t - t) +
    (-b2) * v5_sp a0 b0 h0 a2 b2 h2 s t =
    -t * h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) := by
  dsimp only [P5C_sp, P4C_sp, D0_sp, v5_sp, D234_sp]; ring

/-- `P2 < s` on `{D0 ≤ P4, v4 ≥ 0}` (`a2 < 0`, `b2 < 0`, `t < 1`, `P4 > 0`, `h2 > 0`, `S > 0`). -/
theorem l41_P2_lt_s (hS : 0 < S_sp s t) (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hh2 : 0 < h2)
    (ha2 : a2 < 0) (hb2 : b2 < 0) (hs : 0 < s) (ht : t < 1)
    (hD : D0_sp a0 b0 a2 b2 ≤ P4C_sp b0 h0 b2 h2) (hv4 : 0 ≤ v4_sp a0 b0 h0 a2 b2 h2 s t) :
    P2_sp a2 b2 h2 s t < s := by
  have hq : 0 < qA4_sp a2 b2 s t := by dsimp only [qA4_sp]; nlinarith
  have hid := l41_b_id4 a0 b0 h0 a2 b2 h2 s t
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < (1 - t) * P4C_sp b0 h0 b2 h2 * (s - P2_sp a2 b2 h2 s t) := by
    rw [hid]
    have e1 : 0 ≤ s * (1 - t) * h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 0 ≤ s * (-b2) * v4_sp a0 b0 h0 a2 b2 h2 s t :=
      mul_nonneg (by nlinarith) hv4
    have e3 : 0 < S_sp s t * P4C_sp b0 h0 b2 h2 * qA4_sp a2 b2 s t := by positivity
    linarith
  have := pos_of_mul_pos_right hr (mul_pos h1t hP4).le
  linarith

/-- `a2 + b2 + h2 > 0` on `{D0 ≤ P4, v4 ≥ 0}`. -/
theorem l41_a2b2h2_pos (hS : 0 < S_sp s t) (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hh2 : 0 < h2)
    (hb2 : b2 < 0) (ht : t < 1)
    (hD : D0_sp a0 b0 a2 b2 ≤ P4C_sp b0 h0 b2 h2) (hv4 : 0 ≤ v4_sp a0 b0 h0 a2 b2 h2 s t) :
    0 < a2 + b2 + h2 := by
  have h1t : 0 < 1 - t := by linarith
  have hd : 0 < P5C_sp a0 h0 a2 h2 - P4C_sp b0 h0 b2 h2 := by
    have := l41_b_id1 a0 b0 h0 a2 b2 h2 s t
    have h : 0 < (1 - t) * (P5C_sp a0 h0 a2 h2 - P4C_sp b0 h0 b2 h2) := by
      rw [this]; have := mul_pos hS hP4; linarith
    exact pos_of_mul_pos_right h h1t.le
  have hid := l41_b_id3 a0 b0 h0 a2 b2 h2
  have h : 0 < P4C_sp b0 h0 b2 h2 * (a2 + b2 + h2) := by
    rw [hid]
    have e1 : 0 ≤ h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) :=
      mul_nonneg hh2.le (by linarith)
    have e2 : 0 < (-b2) * (P5C_sp a0 h0 a2 h2 - P4C_sp b0 h0 b2 h2) :=
      mul_pos (by linarith) hd
    linarith
  exact pos_of_mul_pos_right h hP4.le

/-- `1 - b2 - h2 > 0` from `DG5 > 0` (`a0 < 0`, `a2 < 0`, `1 - b0 - h0 > 0`). -/
theorem l41_one_sub_b2h2_pos (ha0 : a0 < 0) (ha2 : a2 < 0) (h1bh : 0 < 1 - b0 - h0)
    (hDG5 : 0 < DG5_sp a0 b0 h0 a2 b2 h2) : 0 < 1 - b2 - h2 := by
  have hid := l41_b_id5 a0 b0 h0 a2 b2 h2
  have : 0 < (-a0) * (1 - b2 - h2) := by
    have := mul_pos (neg_pos.mpr ha2) h1bh
    linarith
  exact pos_of_mul_pos_right this (neg_pos.mpr ha0).le

/-- `D234 < t` on `{D0 ≤ P4, v5 > 0}`. -/
theorem l41_D234_lt_t (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hh2 : 0 < h2) (hb2 : b2 < 0) (ht : 0 < t)
    (hD : D0_sp a0 b0 a2 b2 ≤ P4C_sp b0 h0 b2 h2) (hv5 : 0 < v5_sp a0 b0 h0 a2 b2 h2 s t) :
    D234_sp a2 b2 h2 s t < t := by
  have hid := l41_b_id6 a0 b0 h0 a2 b2 h2 s t
  have h : P4C_sp b0 h0 b2 h2 * (D234_sp a2 b2 h2 s t - t) < 0 := by
    have e1 : 0 ≤ t * h2 * (P4C_sp b0 h0 b2 h2 - D0_sp a0 b0 a2 b2) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 0 < (-b2) * v5_sp a0 b0 h0 a2 b2 h2 s t := mul_pos (by linarith) hv5
    linarith
  have := neg_of_mul_neg_right h hP4.le
  linarith

end L41Real

/-! ## L41-1c/d: the Gram-level identities and `False`-lemmas -/

section L41Gram

/-- `z4(S v12)` in the `(e3, e4, e5)` frame, `S v12 = (S h2, P2 - s, D234 - t)`. -/
def l41_z4 (a2 b2 h2 s t G44 g34 g45 : ℝ) : ℝ :=
  S_sp s t * h2 * g34 + (P2_sp a2 b2 h2 s t - s) * G44 + (D234_sp a2 b2 h2 s t - t) * g45

/-- `z5(S v12)`. -/
def l41_z5 (a2 b2 h2 s t G55 g35 g45 : ℝ) : ℝ :=
  S_sp s t * h2 * g35 + (P2_sp a2 b2 h2 s t - s) * g45 + (D234_sp a2 b2 h2 s t - t) * G55

/-- `W21' = S^2 (z1 - z4)(v12) = (1 - t) z4 + t z5` (at `S v12`). -/
def l41_W21 (a2 b2 h2 s t G44 G55 g34 g35 g45 : ℝ) : ℝ :=
  (1 - t) * l41_z4 a2 b2 h2 s t G44 g34 g45 + t * l41_z5 a2 b2 h2 s t G55 g35 g45

/-- `|(0, A4, A5)|_G^2` with `A4 = P2 - s`, `A5 = D234 - t`. -/
def l41_Anorm (a2 b2 h2 s t G44 G55 g45 : ℝ) : ℝ :=
  (P2_sp a2 b2 h2 s t - s) ^ 2 * G44 + (D234_sp a2 b2 h2 s t - t) ^ 2 * G55 +
    2 * (P2_sp a2 b2 h2 s t - s) * (D234_sp a2 b2 h2 s t - t) * g45

variable (a2 b2 h2 s t G44 G55 g34 g35 g45 : ℝ)

/-- **Case 2A identity** (`A41` Q41.2, 6-entry form, ring in the `G` entries). -/
theorem l41_id_2A :
    S_sp s t * (-b2 - h2 * t) * l41_z5 a2 b2 h2 s t G55 g35 g45 +
        (s - P2_sp a2 b2 h2 s t) * l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 =
      -(1 - t) * l41_Anorm a2 b2 h2 s t G44 G55 g45 +
        (1 - t) * S_sp s t * h2 *
          ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) := by
  dsimp only [l41_z5, l41_W21, l41_z4, l41_Anorm, S_sp, P2_sp, D234_sp]; ring

/-- **Case 2B identity**. -/
theorem l41_id_2B :
    S_sp s t * (b2 + h2 * t) * l41_z4 a2 b2 h2 s t G44 g34 g45 +
        (t - D234_sp a2 b2 h2 s t) * l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 =
      -t * l41_Anorm a2 b2 h2 s t G44 G55 g45 +
        t * S_sp s t * h2 *
          ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) := by
  dsimp only [l41_z5, l41_W21, l41_z4, l41_Anorm, S_sp, P2_sp, D234_sp]; ring

variable {a2 b2 h2 s t G44 G55 g34 g35 g45}

/-- Common sign of the right-hand sides: `-c * |A|^2 + c S h2 [(s - P2) g34 + (t - D234) g35] < 0`
for `c > 0`, `g34, g35 ≤ 0`, `P2 ≤ s`, `D234 ≤ t`, `|A|^2 > 0`. -/
theorem l41_rhs_neg {c : ℝ} (hc : 0 < c) (hS : 0 < S_sp s t) (hh2 : 0 < h2)
    (hP2 : P2_sp a2 b2 h2 s t ≤ s) (hD : D234_sp a2 b2 h2 s t ≤ t) (hg34 : g34 ≤ 0) (hg35 : g35 ≤ 0)
    (hA : 0 < l41_Anorm a2 b2 h2 s t G44 G55 g45) :
    -c * l41_Anorm a2 b2 h2 s t G44 G55 g45 +
        c * S_sp s t * h2 *
          ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) < 0 := by
  have e1 : (s - P2_sp a2 b2 h2 s t) * g34 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hg34
  have e2 : (t - D234_sp a2 b2 h2 s t) * g35 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hg35
  have e3 : c * S_sp s t * h2 *
      ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have e4 := mul_pos hc hA
  linarith

/-- **`l41_2A_z5_neg`** (L41-1c closing step, algebra): in case `b2 + h2 t ≤ 0`, `W21' ≥ 0` forces
`z5(S v12) < 0` and hence `z4(S v12) > 0`. -/
theorem l41_2A_z5_neg (hb : b2 + h2 * t ≤ 0) (ht1 : t < 1) (ht0 : 0 < t) (hS : 0 < S_sp s t)
    (hh2 : 0 < h2) (hP2 : P2_sp a2 b2 h2 s t ≤ s) (hD : D234_sp a2 b2 h2 s t ≤ t)
    (hg34 : g34 ≤ 0) (hg35 : g35 ≤ 0)
    (hA : 0 < l41_Anorm a2 b2 h2 s t G44 G55 g45)
    (hW : 0 ≤ l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45) :
    l41_z5 a2 b2 h2 s t G55 g35 g45 < 0 ∧ 0 < l41_z4 a2 b2 h2 s t G44 g34 g45 := by
  have hid := l41_id_2A a2 b2 h2 s t G44 G55 g34 g35 g45
  have hneg := l41_rhs_neg (c := 1 - t) (by linarith) hS hh2 hP2 hD hg34 hg35 hA
  have hz5 : l41_z5 a2 b2 h2 s t G55 g35 g45 < 0 := by
    by_contra h
    replace h := not_lt.mp h
    have h1 : 0 ≤ S_sp s t * (-b2 - h2 * t) * l41_z5 a2 b2 h2 s t G55 g35 g45 :=
      mul_nonneg (mul_nonneg hS.le (by linarith)) h
    have h2' : 0 ≤ (s - P2_sp a2 b2 h2 s t) * l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 :=
      mul_nonneg (by linarith) hW
    have : -(1 - t) * l41_Anorm a2 b2 h2 s t G44 G55 g45 +
        (1 - t) * S_sp s t * h2 *
          ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) < 0 := hneg
    linarith
  refine ⟨hz5, ?_⟩
  have : l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 =
      (1 - t) * l41_z4 a2 b2 h2 s t G44 g34 g45 + t * l41_z5 a2 b2 h2 s t G55 g35 g45 := rfl
  nlinarith [mul_pos ht0 (neg_pos.mpr hz5)]

/-- **`l41_2B_z4_neg`** (L41-1d, algebra): in case `b2 + h2 t > 0`, `W21' ≥ 0` forces
`z4(S v12) < 0` and hence `z5(S v12) > 0`. -/
theorem l41_2B_z4_neg (hb : 0 < b2 + h2 * t) (ht1 : t < 1) (ht0 : 0 < t) (hS : 0 < S_sp s t)
    (hh2 : 0 < h2) (hP2 : P2_sp a2 b2 h2 s t ≤ s) (hD : D234_sp a2 b2 h2 s t ≤ t)
    (hg34 : g34 ≤ 0) (hg35 : g35 ≤ 0)
    (hA : 0 < l41_Anorm a2 b2 h2 s t G44 G55 g45)
    (hW : 0 ≤ l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45) :
    l41_z4 a2 b2 h2 s t G44 g34 g45 < 0 ∧ 0 < l41_z5 a2 b2 h2 s t G55 g35 g45 := by
  have hid := l41_id_2B a2 b2 h2 s t G44 G55 g34 g35 g45
  have hneg := l41_rhs_neg (c := t) ht0 hS hh2 hP2 hD hg34 hg35 hA
  have hz4 : l41_z4 a2 b2 h2 s t G44 g34 g45 < 0 := by
    by_contra h
    replace h := not_lt.mp h
    have h1 : 0 ≤ S_sp s t * (b2 + h2 * t) * l41_z4 a2 b2 h2 s t G44 g34 g45 :=
      mul_nonneg (mul_nonneg hS.le hb.le) h
    have h2' : 0 ≤ (t - D234_sp a2 b2 h2 s t) * l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 :=
      mul_nonneg (by linarith) hW
    have : -t * l41_Anorm a2 b2 h2 s t G44 G55 g45 +
        t * S_sp s t * h2 *
          ((s - P2_sp a2 b2 h2 s t) * g34 + (t - D234_sp a2 b2 h2 s t) * g35) < 0 := hneg
    linarith
  refine ⟨hz4, ?_⟩
  have : l41_W21 a2 b2 h2 s t G44 G55 g34 g35 g45 =
      (1 - t) * l41_z4 a2 b2 h2 s t G44 g34 g45 + t * l41_z5 a2 b2 h2 s t G55 g35 g45 := rfl
  nlinarith [mul_pos (sub_pos.mpr ht1) (neg_pos.mpr hz4)]

end L41Gram

/-! ## L41-1a: facet values at `v12 = x2 - x1`, and the vector layer -/

section L41Vec

variable {x : Fin 7 → ℝ³}

theorem l41_v12_f015 (N : NF29 x) : N.f015.f (x 2) - N.f015.f (x 1) = -N.P4 * N.D ^ 2 := by
  dsimp only [f015, Face16.ofPoly]; nf29_simp N; simp only [det3c, NF29.D, NF29.P4]; ring
theorem l41_v12_f023 (N : NF29 x) : N.f023.f (x 2) - N.f023.f (x 1) = N.D02 * N.D ^ 2 := by
  dsimp only [f023, Face16.ofPoly]; nf29_simp N; simp only [det3c, NF29.D, NF29.D02]; ring
theorem l41_v12_f035 (N : NF29 x) :
    N.f035.f (x 2) - N.f035.f (x 1) = (-N.a0 - N.DG5) * N.D ^ 2 := by
  dsimp only [f035, Face16.ofPoly]; nf29_simp N
  simp only [det3c, NF29.D, NF29.DG5, NF29.D02, NF29.dG]; ring
theorem l41_v12_f1456 (N : NF29 x) : N.f1456.f (x 2) - N.f1456.f (x 1) = -N.h2 * N.D ^ 2 := by
  dsimp only [f1456, Face16.ofPoly]; nf29_simp N; simp only [det3c, NF29.D]; ring
theorem l41_v12_f234 (N : NF29 x) : N.f234.f (x 2) - N.f234.f (x 1) = (-N.b2) * N.D ^ 2 := by
  dsimp only [f234, Face16.ofPoly]; nf29_simp N; simp only [det3c, NF29.D]; ring
theorem l41_v12_f346 (N : NF29 x) :
    N.f346.f (x 2) - N.f346.f (x 1) = (N.t - D234_sp N.a2 N.b2 N.h2 N.s N.t) * N.D ^ 2 := by
  dsimp only [f346, Face16.ofPoly, D234_sp]; nf29_simp N; simp only [det3c, NF29.D]; ring
theorem l41_v12_f356 (N : NF29 x) :
    N.f356.f (x 2) - N.f356.f (x 1) = (N.s - P2_sp N.a2 N.b2 N.h2 N.s N.t) * N.D ^ 2 := by
  dsimp only [f356, Face16.ofPoly, P2_sp]; nf29_simp N; simp only [det3c, NF29.D]; ring
/-- `v12` lies on the facets `012` and `124` (edge `1 2`). -/
theorem l41_v12_f012 (N : NF29 x) : N.f012.f (x 2) - N.f012.f (x 1) = 0 := by
  rw [N.f012.zero 2 (by decide), N.f012.zero 1 (by decide)]; ring
theorem l41_v12_f124 (N : NF29 x) : N.f124.f (x 2) - N.f124.f (x 1) = 0 := by
  rw [N.f124.zero 2 (by decide), N.f124.zero 1 (by decide)]; ring

/-- `S v12 = (S h2) e3 + (P2 - s) e4 + (D234 - t) e5` with `e_i = x_i - x_6`. -/
theorem l41_w_decomp (N : NF29 x) :
    S_sp N.s N.t • (x 2 - x 1) = (S_sp N.s N.t * N.h2) • (x 3 - x 6) +
      (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) • (x 4 - x 6) +
      (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) • (x 5 - x 6) := by
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h : S_sp N.s N.t • (x 2 - x 1) =
      S_sp N.s N.t • (x 2 - x 6) - S_sp N.s N.t • (x 1 - x 6) := by module
  rw [h, hqc.2.2, hqc.2.1]; module

theorem l41_inner_e4 (N : NF29 x) :
    ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ =
      l41_z4 N.a2 N.b2 N.h2 N.s N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 4 - x 6⟫
        ⟪x 4 - x 6, x 5 - x 6⟫ := by
  rw [l41_w_decomp N]
  simp only [inner_add_right, inner_smul_right, l41_z4]
  rw [real_inner_comm (x 3 - x 6) (x 4 - x 6)]

theorem l41_inner_e5 (N : NF29 x) :
    ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ =
      l41_z5 N.a2 N.b2 N.h2 N.s N.t ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫
        ⟪x 4 - x 6, x 5 - x 6⟫ := by
  rw [l41_w_decomp N]
  simp only [inner_add_right, inner_smul_right, l41_z5]
  rw [real_inner_comm (x 3 - x 6) (x 5 - x 6), real_inner_comm (x 4 - x 6) (x 5 - x 6)]

/-- The vector `A = (P2 - s) e4 + (D234 - t) e5` has `⟪A, A⟫ = l41_Anorm`. -/
theorem l41_inner_A (N : NF29 x) :
    ⟪(P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) • (x 4 - x 6) +
        (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) • (x 5 - x 6),
      (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) • (x 4 - x 6) +
        (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) • (x 5 - x 6)⟫ =
      l41_Anorm N.a2 N.b2 N.h2 N.s N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫
        ⟪x 4 - x 6, x 5 - x 6⟫ := by
  simp only [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left, l41_Anorm,
    RCLike.conj_to_real]
  rw [real_inner_comm (x 4 - x 6) (x 5 - x 6)]; ring

/-- `A ≠ 0` when `P2 ≠ s`: the facet `356` vanishes at `e5` and not at `e4`. -/
theorem l41_A_ne_zero (N : NF29 x) (hP2 : P2_sp N.a2 N.b2 N.h2 N.s N.t ≠ N.s) :
    (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) • (x 4 - x 6) +
      (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) • (x 5 - x 6) ≠ 0 := by
  intro h
  have h4 : ⟪N.f356.N, x 4 - x 6⟫ < 0 := by
    rw [← N.f356.hN, N.f356.zero 6 (by decide), sub_zero]; exact N.f356.neg 4 (by decide)
  have h5 : ⟪N.f356.N, x 5 - x 6⟫ = 0 := by
    rw [← N.f356.hN, N.f356.zero 6 (by decide), N.f356.zero 5 (by decide), sub_zero]
  have := congrArg (fun v => ⟪N.f356.N, v⟫) h
  simp only [inner_add_right, inner_smul_right, h5, inner_zero_right] at this
  have h' : (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) * ⟪N.f356.N, x 4 - x 6⟫ = 0 := by linarith
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact hP2 (by linarith)
  · linarith

/-- `0 < ⟪A, A⟫` (the `PD` hypothesis of the `False`-lemmas, from `A ≠ 0`). -/
theorem l41_Anorm_pos (N : NF29 x) (hP2 : P2_sp N.a2 N.b2 N.h2 N.s N.t ≠ N.s) :
    0 < l41_Anorm N.a2 N.b2 N.h2 N.s N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫
        ⟪x 4 - x 6, x 5 - x 6⟫ := by
  rw [← l41_inner_A N]
  exact real_inner_self_pos.mpr (l41_A_ne_zero N hP2)

/-- `v012 = v4 e4 + v5 e5` (the view of the line `F012 × F1456`). -/
noncomputable def l41_v012 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
    v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6)

/-- **Radon vector identity of the line `012 × 124`**: `S h2 (x1 - x0) + v012 + h0 (S v12) = 0`. -/
theorem l41_radon_v12 (N : NF29 x) :
    (S_sp N.s N.t * N.h2) • (x 1 - x 0) + l41_v012 N x +
      N.h0 • (S_sp N.s N.t • (x 2 - x 1)) = 0 := by
  dsimp only [l41_v012, v4_sp, v5_sp, S_sp, P5C_sp, P4C_sp]
  rw [N.x0, N.x1, N.x2, N.x4, N.x5, N.x6]
  simp only [nfP]
  module

/-- **L41-1d closing (corrected multipliers `(h2, 1, S^2 h0)`)**:
`h2 V12_10 + FA21 + h0 |S v12|^2 = 0`, with `V12_10 = S ⟪x1 - x0, S v12⟫`,
`FA21 = ⟪S v12, v012⟫`. -/
theorem l41_id_close (N : NF29 x) :
    N.h2 * (S_sp N.s N.t * ⟪x 1 - x 0, S_sp N.s N.t • (x 2 - x 1)⟫) +
      ⟪S_sp N.s N.t • (x 2 - x 1), l41_v012 N x⟫ +
      N.h0 * ⟪S_sp N.s N.t • (x 2 - x 1), S_sp N.s N.t • (x 2 - x 1)⟫ = 0 := by
  have h := congrArg (fun v => ⟪v, S_sp N.s N.t • (x 2 - x 1)⟫) (l41_radon_v12 N)
  simp only [inner_add_left, inner_smul_left, inner_zero_left, RCLike.conj_to_real] at h
  have h2 := real_inner_comm (l41_v012 N x) (S_sp N.s N.t • (x 2 - x 1))
  simp only [inner_smul_left, RCLike.conj_to_real] at h2 ⊢
  linarith

/-- **L41-1d closing, `False` form**: `V12_10 ≥ 0` and `FA21 ≥ 0` are impossible. -/
theorem l41_close_false (N : NF29 x) (hh2 : 0 < N.h2) (hh0 : 0 < N.h0)
    (hV : 0 ≤ S_sp N.s N.t * ⟪x 1 - x 0, S_sp N.s N.t • (x 2 - x 1)⟫)
    (hF : 0 ≤ ⟪S_sp N.s N.t • (x 2 - x 1), l41_v012 N x⟫) : False := by
  have hid := l41_id_close N
  have hS := S_pos_of_NF29 N
  have hne : S_sp N.s N.t • (x 2 - x 1) ≠ 0 := by
    refine smul_ne_zero hS.ne' (sub_ne_zero.mpr fun h => ?_)
    exact absurd (N.inj h) (by decide)
  have hpos : 0 < ⟪S_sp N.s N.t • (x 2 - x 1), S_sp N.s N.t • (x 2 - x 1)⟫ :=
    real_inner_self_pos.mpr hne
  nlinarith [mul_nonneg hh2.le hV, mul_pos hh0 hpos]

end L41Vec

/-! ## L41-1 leaf: `v12_closes` -/

section L41Leaf

variable {x : Fin 7 → ℝ³}

/-- Region of the line `F012 × F124`: `K1a ∩ G* ∩ Cell II` facts, `D0 ≤ P4`, `v5 > 0`, `P2 < s`, and the two
obtuse-at-`6` inner products `g34, g35 ≤ 0` (Carbon `P4 = P4C_sp`, `D0 = D0_sp`). -/
def L41Region (N : NF29 x) : Prop :=
  N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0 ∧ N.h0 < 1 ∧ 1 < N.h2 ∧ N.t < 1 ∧ 0 < N.dG4 ∧
  0 < 1 - N.b0 - N.h0 ∧
  D0_sp N.a0 N.b0 N.a2 N.b2 ≤ P4C_sp N.b0 N.h0 N.b2 N.h2 ∧
  0 < v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
  P2_sp N.a2 N.b2 N.h2 N.s N.t < N.s ∧
  ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0

/-- **Rim step `2A` (lean-sem fact, NOT proved; hypothesis of the leaf)**: in case `b2 + h2 t ≤ 0` with
`z5(S v12) < 0 < z4(S v12)` and `W21' ≥ 0`, the lex semantics at `v12` is RU on the rim `R_{--} = (0,2,4,6,5)`
(every 4-subset strictly monotone), i.e. `LexAny29` holds (tie tilt through the facets `012`, `124`). -/
def RimStepA29 (N : NF29 x) : Prop :=
  L41Region N → N.b2 + N.h2 * N.t ≤ 0 →
    ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ < 0 → 0 < ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ →
    0 ≤ (1 - N.t) * ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ +
      N.t * ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ →
    Minimality.H29.LexAny29 (s0x_fac29 N.facets)

/-- **Rim step `2B` (lean-sem fact, NOT proved; hypothesis of the leaf)**: in case `b2 + h2 t > 0` with
`z4(S v12) < 0 < z5(S v12)` and `W21' ≥ 0`, if `V12_10 = S^2 (z1 - z0)(v12) < 0` then the lex semantics is RU on
`R_{++} = (0,1,4,6,5)`, i.e. `LexAny29` holds. -/
def RimStepB29 (N : NF29 x) : Prop :=
  L41Region N → 0 < N.b2 + N.h2 * N.t →
    ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ < 0 → 0 < ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ →
    0 ≤ (1 - N.t) * ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ +
      N.t * ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ →
    S_sp N.s N.t * ⟪x 1 - x 0, S_sp N.s N.t • (x 2 - x 1)⟫ < 0 →
    Minimality.H29.LexAny29 (s0x_fac29 N.facets)

/-- The `W14` row `W21' ≥ 0` (from `w14_of_not_lexAny29`) in inner-product form. -/
theorem l41_W21_inner (N : NF29 x) :
    (1 - N.t) * ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ +
        N.t * ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ =
      Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) N.h2
        (1 - N.t) N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
        ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  rw [l41_inner_e4 N, l41_inner_e5 N]
  dsimp only [l41_z4, l41_z5, Row_sp]; ring

/-- **L41-1 (`v12_closes`)**: on `{K1a, G*, Cell II, D0 ≤ P4, v5 > 0, P2 < s}` with `g34, g35 ≤ 0`, `FA21 ≥ 0`,
and the two rim steps, `¬ LexAny29` is contradictory.  Case `2A` (`b2 + h2 t ≤ 0`, needed by `P_cex1/2`,
`w2q1p_0`) does not use `FA21`; case `2B` (`b2 + h2 t > 0`, `g3Bd_14`) closes by the corrected identity
`h2 V12_10 + FA21 + S^2 h0 |v12|^2 = 0`.  The hypothesis `v4 ≥ 0 ∨ b2 + h2 t > 0` of the spec is not needed
(only `P2 < s`, which is in the region). -/
theorem l41_v12_closes (N : NF29 x) (hreg : L41Region N)
    (hFA : 0 ≤ ⟪S_sp N.s N.t • (x 2 - x 1), l41_v012 N x⟫)
    (hA : RimStepA29 N) (hB : RimStepB29 N)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  obtain ⟨ha2, _hb0, _hV, _hh0, hh2, ht1, hdG4, h1bh, hD, hv5, hP2, hg34, hg35⟩ := id hreg
  have hS := S_pos_of_NF29 N
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by
    have := P5_pos_of_NF29 N; dsimp only [NF29.P5] at this; dsimp only [P4C_sp]; exact this
  have hD234 : D234_sp N.a2 N.b2 N.h2 N.s N.t < N.t :=
    l41_D234_lt_t N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t hP4 (by linarith) N.hb2 N.ht hD hv5
  have hrow := (w14_of_not_lexAny29 N ha2 ht1 hdG4 h1bh hnf).1
  have hW' : 0 ≤ (1 - N.t) * ⟪x 4 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ +
      N.t * ⟪x 5 - x 6, S_sp N.s N.t • (x 2 - x 1)⟫ := by rw [l41_W21_inner N]; exact hrow
  have hA0 := l41_Anorm_pos N hP2.ne
  have hW : 0 ≤ l41_W21 N.a2 N.b2 N.h2 N.s N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫ := by
    rw [l41_inner_e4 N, l41_inner_e5 N] at hW'; exact hW'
  rcases le_or_gt (N.b2 + N.h2 * N.t) 0 with hb | hb
  · obtain ⟨hz5, hz4⟩ := l41_2A_z5_neg hb ht1 N.ht hS (by linarith) hP2.le hD234.le hg34 hg35 hA0 hW
    rw [← l41_inner_e5 N] at hz5
    rw [← l41_inner_e4 N] at hz4
    exact hnf (hA hreg hb hz5 hz4 hW')
  · obtain ⟨hz4, hz5⟩ := l41_2B_z4_neg hb ht1 N.ht hS (by linarith) hP2.le hD234.le hg34 hg35 hA0 hW
    rw [← l41_inner_e4 N] at hz4
    rw [← l41_inner_e5 N] at hz5
    by_cases hV10 : S_sp N.s N.t * ⟪x 1 - x 0, S_sp N.s N.t • (x 2 - x 1)⟫ < 0
    · exact hnf (hB hreg hb hz4 hz5 hW' hV10)
    · exact l41_close_false N N.hh2 N.hh0 (not_lt.mp hV10) hFA

end L41Leaf

/-! ## L41-1e and L41-3: the corrected Radon identities and the collapse `False`-lemmas -/

section L41Radon

/-- Generic collapse: `pA zA + pB zB + cn = pC zC + pD zD` with balanced nonnegative weights and `cn < 0`
refutes `min(zC, zD) ≥ max(zA, zB)`. -/
theorem l41_sep_false {zA zB zC zD pA pB pC pD cn : ℝ} (hA : 0 ≤ pA) (hB : 0 ≤ pB) (hC : 0 ≤ pC)
    (hD : 0 ≤ pD) (hbal : pA + pB = pC + pD) (hid : pA * zA + pB * zB + cn = pC * zC + pD * zD)
    (hcn : cn < 0) (h1 : zA ≤ zC) (h2 : zB ≤ zC) (h3 : zA ≤ zD) (h4 : zB ≤ zD) : False := by
  rcases le_total zA zB with h | h
  · have e : (pA + pB) * zB = (pC + pD) * zB := by rw [hbal]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr h2), mul_nonneg hD (sub_nonneg.mpr h4),
      mul_nonneg hA (sub_nonneg.mpr h)]
  · have e : (pA + pB) * zA = (pC + pD) * zA := by rw [hbal]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr h1), mul_nonneg hD (sub_nonneg.mpr h3),
      mul_nonneg hB (sub_nonneg.mpr h)]

/-- Weight `K1` of `x1` in the Radon identity of `Q1-collapse` (Carbon: `(-a2)(b0 h2 + h0 (h2-1)) + (-a0) h2 (1-b2-h2)`). -/
def l41_K1 (a0 b0 h0 a2 b2 h2 : ℝ) : ℝ :=
  (-a2) * (b0 * h2 + h0 * (h2 - 1)) + (-a0) * h2 * (1 - b2 - h2)

/-- Weight of `x1` in the Radon identity of `WI-QIII-No-FA`: `P4 + h2 (D0 - P4)`. -/
def l41_K3 (a0 b0 h0 a2 b2 h2 : ℝ) : ℝ :=
  P4C_sp b0 h0 b2 h2 + h2 * (D0_sp a0 b0 a2 b2 - P4C_sp b0 h0 b2 h2)

theorem l41_K1_bal (a0 b0 h0 a2 b2 h2 s t : ℝ) :
    S_sp s t * P5C_sp a0 h0 a2 h2 + S_sp s t * h2 * D0_sp a0 b0 a2 b2 =
      S_sp s t * h2 * P5C_sp a0 h0 a2 h2 + S_sp s t * l41_K1 a0 b0 h0 a2 b2 h2 := by
  dsimp only [S_sp, P5C_sp, D0_sp, l41_K1]; ring

theorem l41_K3_bal (a0 b0 h0 a2 b2 h2 s t : ℝ) :
    S_sp s t * h2 * P4C_sp b0 h0 b2 h2 + S_sp s t * l41_K3 a0 b0 h0 a2 b2 h2 =
      S_sp s t * P4C_sp b0 h0 b2 h2 + S_sp s t * h2 * D0_sp a0 b0 a2 b2 := by
  dsimp only [S_sp, P4C_sp, D0_sp, l41_K3]; ring

theorem l41_K1_pos {a0 b0 h0 a2 b2 h2 : ℝ} (ha0 : a0 < 0) (ha2 : a2 < 0) (hb0 : 0 < b0)
    (hh0 : 0 < h0) (hh2 : 1 < h2) (h1b2h2 : 0 < 1 - b2 - h2) : 0 < l41_K1 a0 b0 h0 a2 b2 h2 := by
  dsimp only [l41_K1]
  have h1 : 0 < b0 * h2 + h0 * (h2 - 1) := by nlinarith
  have := mul_pos (neg_pos.mpr ha2) h1
  have := mul_pos (mul_pos (neg_pos.mpr ha0) (by linarith : (0:ℝ) < h2)) h1b2h2
  linarith

variable {x : Fin 7 → ℝ³}

/-- **L41-1e, corrected Radon identity (`+a2` times `v012`)**:
`S P5 x2 + S h2 D0 x5 + a2 v012 = S h2 P5 x3 + S K1 x1`. -/
theorem l41_radon_Q1 (N : NF29 x) :
    (S_sp N.s N.t * P5C_sp N.a0 N.h0 N.a2 N.h2) • x 2 + (S_sp N.s N.t * N.h2 * D0_sp N.a0 N.b0 N.a2 N.b2) • x 5 +
      N.a2 • l41_v012 N x =
    (S_sp N.s N.t * N.h2 * P5C_sp N.a0 N.h0 N.a2 N.h2) • x 3 +
      (S_sp N.s N.t * l41_K1 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) • x 1 := by
  dsimp only [l41_v012, l41_K1, v4_sp, v5_sp, S_sp, P5C_sp, P4C_sp, D0_sp]
  rw [N.x1, N.x2, N.x3, N.x4, N.x5, N.x6]
  simp only [nfP]
  module

/-- **L41-3, corrected Radon identity (`+b2` times `v012`)**:
`S h2 P4 x3 + S K3 x1 + b2 v012 = S P4 x2 + S h2 D0 x4`. -/
theorem l41_radon_Q3 (N : NF29 x) :
    (S_sp N.s N.t * N.h2 * P4C_sp N.b0 N.h0 N.b2 N.h2) • x 3 +
      (S_sp N.s N.t * l41_K3 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) • x 1 + N.b2 • l41_v012 N x =
    (S_sp N.s N.t * P4C_sp N.b0 N.h0 N.b2 N.h2) • x 2 +
      (S_sp N.s N.t * N.h2 * D0_sp N.a0 N.b0 N.a2 N.b2) • x 4 := by
  dsimp only [l41_v012, l41_K3, v4_sp, v5_sp, S_sp, P5C_sp, P4C_sp, D0_sp]
  rw [N.x1, N.x2, N.x3, N.x4, N.x5, N.x6]
  simp only [nfP]
  module

/-- **`Q1-collapse` `False`-lemma**: `min(z1, z3) ≥ max(z2, z5)` at `v012` is impossible (`a2 < 0`,
`v012 ≠ 0`, weights positive). -/
theorem l41_Q1_false (N : NF29 x) (hS : 0 < S_sp N.s N.t) (ha2 : N.a2 < 0)
    (hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2) (hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2)
    (hh2 : 0 < N.h2) (hK1 : 0 < l41_K1 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2)
    (hv : l41_v012 N x ≠ 0)
    (h21 : ⟪x 2, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫) (h51 : ⟪x 5, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫)
    (h23 : ⟪x 2, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫) (h53 : ⟪x 5, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫) :
    False := by
  have hid := congrArg (fun w => ⟪w, l41_v012 N x⟫) (l41_radon_Q1 N)
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at hid
  have hn := real_inner_self_pos.mpr hv
  exact l41_sep_false (zA := ⟪x 2, l41_v012 N x⟫) (zB := ⟪x 5, l41_v012 N x⟫)
    (zC := ⟪x 3, l41_v012 N x⟫) (zD := ⟪x 1, l41_v012 N x⟫)
    (pA := S_sp N.s N.t * P5C_sp N.a0 N.h0 N.a2 N.h2) (pB := S_sp N.s N.t * N.h2 * D0_sp N.a0 N.b0 N.a2 N.b2)
    (pC := S_sp N.s N.t * N.h2 * P5C_sp N.a0 N.h0 N.a2 N.h2)
    (pD := S_sp N.s N.t * l41_K1 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) (cn := N.a2 * ⟪l41_v012 N x, l41_v012 N x⟫)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (l41_K1_bal _ _ _ _ _ _ _ _) (by linarith) (mul_neg_of_neg_of_pos ha2 hn) h23 h53 h21 h51

/-- **`WI-QIII-No-FA` `False`-lemma**: `min(z2, z4) ≥ max(z1, z3)` at `v012` is impossible (`b2 < 0`). -/
theorem l41_Q3_false (N : NF29 x) (hS : 0 < S_sp N.s N.t)
    (hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2) (hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2)
    (hh2 : 0 < N.h2) (hK3 : 0 < l41_K3 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2)
    (hv : l41_v012 N x ≠ 0)
    (h13 : ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫) (h14 : ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 4, l41_v012 N x⟫)
    (h12 : ⟪x 1, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫) (h15 : ⟪x 1, l41_v012 N x⟫ ≤ ⟪x 4, l41_v012 N x⟫) :
    False := by
  have hid := congrArg (fun w => ⟪w, l41_v012 N x⟫) (l41_radon_Q3 N)
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at hid
  have hn := real_inner_self_pos.mpr hv
  exact l41_sep_false (zA := ⟪x 3, l41_v012 N x⟫) (zB := ⟪x 1, l41_v012 N x⟫)
    (zC := ⟪x 2, l41_v012 N x⟫) (zD := ⟪x 4, l41_v012 N x⟫)
    (pA := S_sp N.s N.t * N.h2 * P4C_sp N.b0 N.h0 N.b2 N.h2)
    (pB := S_sp N.s N.t * l41_K3 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2)
    (pC := S_sp N.s N.t * P4C_sp N.b0 N.h0 N.b2 N.h2) (pD := S_sp N.s N.t * N.h2 * D0_sp N.a0 N.b0 N.a2 N.b2)
    (cn := N.b2 * ⟪l41_v012 N x, l41_v012 N x⟫)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (l41_K3_bal _ _ _ _ _ _ _ _) (by linarith) (mul_neg_of_neg_of_pos N.hb2 hn) h13 h12 h14 h15

/-- **Rim step `1e` (lean-sem fact, NOT proved)**: on `{D0 ≤ P4, v4 ≥ 0}` a non-`LexAny29` shape has a weakly
alternating 4-rim `(5,1,2,3)` at `012 × 1456` (engine / lean-sem; tie tilt at `v4 = 0`):
`min(z2, z5) ≥ max(z1, z3)` or `min(z1, z3) ≥ max(z2, z5)` at `v012`. -/
def RimStep1e29 (N : NF29 x) : Prop :=
  D0_sp N.a0 N.b0 N.a2 N.b2 ≤ P4C_sp N.b0 N.h0 N.b2 N.h2 →
  0 ≤ v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t →
  ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets) →
  (⟪x 2, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫ ∧ ⟪x 5, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫ ∧
    ⟪x 2, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫ ∧ ⟪x 5, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫) ∨
  (⟪x 1, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫ ∧ ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫ ∧
    ⟪x 1, l41_v012 N x⟫ ≤ ⟪x 5, l41_v012 N x⟫ ∧ ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 5, l41_v012 N x⟫)

/-- **`FA21 ≥ 0` on `QI`** (Theorem Q1-012-Collapse): the Radon collapse kills the first alternative of
`RimStep1e29`, the second gives `z2 ≥ z1`. -/
theorem l41_FA21_nonneg_QI (N : NF29 x) (hrim : RimStep1e29 N)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets))
    (ha2 : N.a2 < 0) (hb0 : 0 < N.b0) (hh2 : 1 < N.h2) (h1bh : 0 < 1 - N.b0 - N.h0)
    (hD : D0_sp N.a0 N.b0 N.a2 N.b2 ≤ P4C_sp N.b0 N.h0 N.b2 N.h2)
    (hv4 : 0 ≤ v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (hv : l41_v012 N x ≠ 0) :
    0 ≤ ⟪S_sp N.s N.t • (x 2 - x 1), l41_v012 N x⟫ := by
  have hS := S_pos_of_NF29 N
  have hDG5 : 0 < DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    dsimp only [DG5_sp, D0_sp, G5_sp]; linarith [N.hDG5]
  have h1 := l41_one_sub_b2h2_pos N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.ha0 ha2 h1bh hDG5
  have hK1 := l41_K1_pos N.ha0 ha2 hb0 N.hh0 hh2 h1
  have hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := P4_pos_of_NF29 N
  have hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2 := D02_pos_of_NF29 N
  rcases hrim hD hv4 hnf with ⟨h21, h51, h23, h53⟩ | ⟨h12, _, _, _⟩
  · exact (l41_Q1_false N hS ha2 hP5 hD0 (by linarith) hK1 hv h21 h51 h23 h53).elim
  · simp only [inner_smul_left, RCLike.conj_to_real, inner_sub_left]
    nlinarith [mul_nonneg hS.le (sub_nonneg.mpr h12)]

/-- **Rim step `3` (lean-sem fact, NOT proved)**: on `{D0 > P4, v5 ≤ 0}` (W-I, QIII) a non-`LexAny29` shape has a
weakly alternating 4-rim `(4,1,2,3)` at `v012`. -/
def RimStep3_29 (N : NF29 x) : Prop :=
  P4C_sp N.b0 N.h0 N.b2 N.h2 < D0_sp N.a0 N.b0 N.a2 N.b2 →
  v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0 →
  ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets) →
  (⟪x 1, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫ ∧ ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 2, l41_v012 N x⟫ ∧
    ⟪x 1, l41_v012 N x⟫ ≤ ⟪x 4, l41_v012 N x⟫ ∧ ⟪x 3, l41_v012 N x⟫ ≤ ⟪x 4, l41_v012 N x⟫) ∨
  (⟪x 2, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫ ∧ ⟪x 4, l41_v012 N x⟫ ≤ ⟪x 1, l41_v012 N x⟫ ∧
    ⟪x 2, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫ ∧ ⟪x 4, l41_v012 N x⟫ ≤ ⟪x 3, l41_v012 N x⟫)

/-- **`L41-3`: `F12 ≥ 0` on `QIII` of `W-I`**. -/
theorem l41_F12_nonneg_QIII (N : NF29 x) (hrim : RimStep3_29 N)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets))
    (hD : P4C_sp N.b0 N.h0 N.b2 N.h2 < D0_sp N.a0 N.b0 N.a2 N.b2)
    (hv5 : v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0) (hh2 : 1 < N.h2)
    (hv : l41_v012 N x ≠ 0) :
    0 ≤ ⟪S_sp N.s N.t • (x 1 - x 2), l41_v012 N x⟫ := by
  have hS := S_pos_of_NF29 N
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := P5_pos_of_NF29 N
  have hK3 : 0 < l41_K3 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    dsimp only [l41_K3]; nlinarith
  have hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2 := D02_pos_of_NF29 N
  rcases hrim hD hv5 hnf with ⟨h12, h32, h14, h34⟩ | ⟨h21, _, _, _⟩
  · exact (l41_Q3_false N hS hP4 hD0 (by linarith) hK3 hv h32 h34 h12 h14).elim
  · simp only [inner_smul_left, RCLike.conj_to_real, inner_sub_left]
    nlinarith [mul_nonneg hS.le (sub_nonneg.mpr h21)]

/-- Facet `234` at `v012`: `⟪N234, v012⟫ = -S K3 D^2` (so `K3 > 0` is the sign `phi_234(v012) < 0`). -/
theorem l41_phi234_v012 (N : NF29 x) :
    ⟪N.f234.N, l41_v012 N x⟫ = -(S_sp N.s N.t * l41_K3 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) * N.D ^ 2 := by
  dsimp only [l41_v012]
  have h4 : ⟪N.f234.N, x 4 - x 6⟫ = N.f234.f (x 4) - N.f234.f (x 6) := (N.f234.hN _ _).symm
  have h5 : ⟪N.f234.N, x 5 - x 6⟫ = N.f234.f (x 5) - N.f234.f (x 6) := (N.f234.hN _ _).symm
  rw [inner_add_right, inner_smul_right, inner_smul_right, h4, h5]
  dsimp only [f234, Face16.ofPoly, l41_K3, S_sp, P4C_sp, D0_sp, v4_sp, v5_sp, P5C_sp]
  nf29_simp N
  simp only [det3c, NF29.D]; ring

end L41Radon

/-! ## L41-2: Part 1A (`F-B × {C_Q2, C_Q5-}` on `chi < 0`), corrected identities -/

section L41Part1A

/-- The shape parameters and the six `G`-entries of the `(e3, e4, e5)` frame (`G33` never enters the rows). -/
structure L41P where
  a0 : ℝ
  b0 : ℝ
  h0 : ℝ
  a2 : ℝ
  b2 : ℝ
  h2 : ℝ
  s : ℝ
  t : ℝ
  G44 : ℝ
  G55 : ℝ
  g45 : ℝ
  g34 : ℝ
  g35 : ℝ

namespace L41P

variable (p : L41P)

/-- Carbon names: `S, D0, P4 = P4C, P5 = P5C, G4, U4, U5, q_A4`. -/
abbrev S : ℝ := S_sp p.s p.t
abbrev D0 : ℝ := D0_sp p.a0 p.b0 p.a2 p.b2
abbrev P4 : ℝ := P4C_sp p.b0 p.h0 p.b2 p.h2
abbrev P5 : ℝ := P5C_sp p.a0 p.h0 p.a2 p.h2
abbrev G4 : ℝ := G4_sp p.b0 p.h0 p.b2 p.h2
abbrev U4 : ℝ := U4_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t
abbrev U5 : ℝ := U5_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t
abbrev qA4 : ℝ := qA4_sp p.a2 p.b2 p.s p.t
abbrev V : ℝ := p.h0 * (1 - p.a2 - p.b2) - p.h2 * (1 - p.a0 - p.b0)
abbrev chi : ℝ := (-p.V) * p.s - p.P5 * p.S
abbrev w4 : ℝ := p.s * (p.h2 - p.P4) + (1 - p.t) * p.P5
abbrev w5 : ℝ := p.t * p.P5 - (p.s - 1) * (p.h2 - p.P4)
/-- `w4' = w4 - S h2`, `w5' = w5 + S h2`. -/
abbrev w4p : ℝ := p.w4 - p.S * p.h2
abbrev w5p : ℝ := p.w5 + p.S * p.h2

/-- `Row_sp` at the view `v = v4 e4 + v5 e5`; equals `S ⟪x_i - x_j, v⟫` (`nf29_row_eq_inner`). -/
abbrev row (q4 q5 Y v4 v5 : ℝ) : ℝ := Row_sp q4 q5 Y v4 v5 p.G44 p.G55 p.g45 p.g34 p.g35 p.S

/-- `Q_{05} = S (z0 - z5)(v_Q)`, `v_Q = (0, -U4, -U5)`. -/
abbrev Q05 : ℝ := p.row (D035_sp p.a0 p.b0 p.h0 p.s p.t) (P0_sp p.a0 p.b0 p.h0 p.s p.t - p.S) p.h0 (-p.U4) (-p.U5)
abbrev Q04 : ℝ := p.row (D035_sp p.a0 p.b0 p.h0 p.s p.t - p.S) (P0_sp p.a0 p.b0 p.h0 p.s p.t) p.h0 (-p.U4) (-p.U5)
abbrev Q02 : ℝ := p.row (D035_sp p.a0 p.b0 p.h0 p.s p.t - P2_sp p.a2 p.b2 p.h2 p.s p.t)
  (P0_sp p.a0 p.b0 p.h0 p.s p.t - D234_sp p.a2 p.b2 p.h2 p.s p.t) (p.h0 - p.h2) (-p.U4) (-p.U5)
/-- `Q4_neg = -S z4(v_Q)`, `Q5_neg = -S z5(v_Q)`. -/
abbrev Q4n : ℝ := -p.row p.S 0 0 (-p.U4) (-p.U5)
abbrev Q5n : ℝ := -p.row 0 p.S 0 (-p.U4) (-p.U5)
/-- `W21' = S^2 (z1 - z4)(v12 / S)`-row at `v14 = (1 - t) e4 + t e5`, `W23 = S (z2 - z3)(v14)`. -/
abbrev W21 : ℝ := p.row (P2_sp p.a2 p.b2 p.h2 p.s p.t - p.s) (D234_sp p.a2 p.b2 p.h2 p.s p.t - p.t) p.h2 (1 - p.t) p.t
abbrev W23 : ℝ := p.row (P2_sp p.a2 p.b2 p.h2 p.s p.t) (D234_sp p.a2 p.b2 p.h2 p.s p.t) (p.h2 - 1) (1 - p.t) p.t
/-- `F12 = S (z1 - z2)(v012)`. -/
abbrev F12 : ℝ := -p.row (P2_sp p.a2 p.b2 p.h2 p.s p.t - p.s) (D234_sp p.a2 p.b2 p.h2 p.s p.t - p.t) p.h2
  (v4_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t) (v5_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t)

abbrev B05 : ℝ := p.h2 * p.P4 * p.Q05 + p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 + p.h0 * p.G4 * p.F12
abbrev B04 : ℝ := p.h2 * p.P4 * p.Q04 + p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 + p.h0 * p.G4 * p.F12
abbrev H : ℝ := p.h2 * p.W23 - (p.h2 - 1) * p.W21
abbrev J0 : ℝ := p.qA4 * (1 - p.t) * p.B05 + p.P4 * p.w4 * p.U4 * p.H
abbrev del05 : ℝ := p.h0 * (p.h2 - p.h0) * p.D0 * p.qA4 * (1 - p.t) - (p.h2 - 1) * p.P4 * p.w4 * p.U4
abbrev gam05 : ℝ := (1 - p.t) * (p.h2 - 1) * p.D0 * p.w4 - (p.h2 - p.P4) * p.qA4 * p.U4
abbrev K04 : ℝ := (-p.w4p) * p.B05 + p.w4 * p.B04

end L41P

variable (p : L41P)

theorem l41_CQ5 : p.S * (p.h2 - p.h0) * p.Q05 + p.S * p.h0 * p.Q02 + ((-p.chi) + (-p.V)) * p.Q5n =
    (-p.chi) * p.Q4n := by
  simp only [L41P.Q05, L41P.Q02, L41P.Q5n, L41P.Q4n, L41P.row, Row_sp, L41P.chi, L41P.V, L41P.S,
    L41P.P5, L41P.U4, L41P.U5, D035_sp, P0_sp, P2_sp, D234_sp, S_sp, P5C_sp, U4_sp, U5_sp, D023_sp,
    DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]
  ring

theorem l41_CQ5' : ((-p.chi) + p.S * (p.h2 - p.h0)) * p.Q05 + p.S * p.h0 * p.Q02 + (-p.V) * p.Q5n =
    (-p.chi) * p.Q04 := by
  simp only [L41P.Q05, L41P.Q02, L41P.Q5n, L41P.Q04, L41P.row, Row_sp, L41P.chi, L41P.V, L41P.S,
    L41P.P5, L41P.U4, L41P.U5, D035_sp, P0_sp, P2_sp, D234_sp, S_sp, P5C_sp, U4_sp, U5_sp, D023_sp,
    DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]
  ring


theorem l41_Q4n_eq : p.Q4n = p.S * (p.U4 * p.G44 + p.U5 * p.g45) := by
  simp only [L41P.Q4n, L41P.row, Row_sp]; ring

theorem l41_Q5n_eq : p.Q5n = p.S * (p.U4 * p.g45 + p.U5 * p.G55) := by
  simp only [L41P.Q5n, L41P.row, Row_sp]; ring

/-- `B_1^{(05)} = -P4 [w4 U4 G44 + w5 U5 G55 + (w4 U5 + w5 U4) g45]` (no `G33`, `g34`, `g35`). -/
theorem l41_B05_eq : p.B05 = -p.P4 * (p.w4 * p.U4 * p.G44 + p.w5 * p.U5 * p.G55 +
    (p.w4 * p.U5 + p.w5 * p.U4) * p.g45) := by
  simp only [L41P.Q05, L41P.W21, L41P.F12, L41P.B05, L41P.row, Row_sp,
    L41P.S, L41P.D0, L41P.P4, L41P.P5, L41P.G4, L41P.U4, L41P.U5, L41P.w4, L41P.w5,
    D035_sp, P0_sp, P2_sp, D234_sp, S_sp, P5C_sp, P4C_sp, U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp,
    D0_sp, G4_sp, G5_sp, v4_sp, v5_sp]
  ring

theorem l41_B04_eq : p.B04 = -p.P4 * (p.w4p * p.U4 * p.G44 + p.w5p * p.U5 * p.G55 +
    (p.w4p * p.U5 + p.w5p * p.U4) * p.g45) := by
  simp only [L41P.Q04, L41P.W21, L41P.F12, L41P.B04, L41P.row, Row_sp,
    L41P.S, L41P.D0, L41P.P4, L41P.P5, L41P.G4, L41P.U4, L41P.U5, L41P.w4, L41P.w5, L41P.w4p,
    L41P.w5p, D035_sp, P0_sp, P2_sp, D234_sp, S_sp, P5C_sp, P4C_sp, U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp,
    D0_sp, G4_sp, G5_sp, v4_sp, v5_sp]
  ring

theorem l41_H_eq : p.H = p.qA4 * (1 - p.t) * p.G44 + qA5_sp p.a2 p.b2 p.s p.t * p.t * p.G55 +
    (p.qA4 * p.t + qA5_sp p.a2 p.b2 p.s p.t * (1 - p.t)) * p.g45 := by
  simp only [L41P.H, L41P.W21, L41P.W23, L41P.row, Row_sp, L41P.S, L41P.qA4, P2_sp, D234_sp, S_sp,
    qA4_sp, qA5_sp]
  ring

theorem l41_w_sum : p.w4 + p.w5 = p.h2 - p.P4 + p.P5 := by
  simp only [L41P.w4, L41P.w5, L41P.P4, L41P.P5, P4C_sp, P5C_sp]; ring

theorem l41_J0_closed : p.J0 = p.qA4 * (1 - p.t) * (-p.P4 * (p.w4 * p.U4 * p.G44 + p.w5 * p.U5 * p.G55 +
      (p.w4 * p.U5 + p.w5 * p.U4) * p.g45)) +
    p.P4 * p.w4 * p.U4 * (p.qA4 * (1 - p.t) * p.G44 + qA5_sp p.a2 p.b2 p.s p.t * p.t * p.G55 +
      (p.qA4 * p.t + qA5_sp p.a2 p.b2 p.s p.t * (1 - p.t)) * p.g45) := by
  simp only [L41P.J0]; rw [l41_B05_eq, l41_H_eq]

/-- `g45` coefficient of `U4 J0 + P4 gam05 Q5_neg` (scalar relation, ring in the 8 shape parameters). -/
theorem l41_rel_g45 : p.P4 * p.U4 * (p.w4 * p.U4 * (p.qA4 * p.t + qA5_sp p.a2 p.b2 p.s p.t * (1 - p.t)) -
      p.qA4 * (1 - p.t) * (p.w4 * p.U5 + p.w5 * p.U4)) + p.P4 * p.gam05 * p.S * p.U4 = 0 := by
  simp only [L41P.gam05, L41P.S, L41P.D0, L41P.P4, L41P.P5, L41P.U4, L41P.U5, L41P.qA4, L41P.w4, L41P.w5,
    P5C_sp, P4C_sp, D0_sp, S_sp, U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp, G4_sp, G5_sp, qA4_sp, qA5_sp]
  ring

/-- `G55` coefficient of `U4 J0 + P4 gam05 Q5_neg`. -/
theorem l41_rel_G55 : p.U4 * p.P4 * (-p.qA4 * (1 - p.t) * p.w5 * p.U5 +
      p.w4 * p.U4 * qA5_sp p.a2 p.b2 p.s p.t * p.t) + p.P4 * p.gam05 * p.S * p.U5 =
    -(p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.w4) := by
  simp only [L41P.gam05, L41P.S, L41P.D0, L41P.P4, L41P.P5, L41P.G4, L41P.U4, L41P.U5, L41P.qA4, L41P.w4,
    L41P.w5, P5C_sp, P4C_sp, D0_sp, S_sp, U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp, G4_sp, G5_sp, qA4_sp,
    qA5_sp]
  ring

/-- **Case FB-1** final sum (`gam05 ≥ 0`): `U4 J0 + P4 gam05 Q5_neg = -S^2 (h2-1) D0 P4 G4 w4 * G55`. -/
theorem l41_FB1_sum : p.U4 * p.J0 + p.P4 * p.gam05 * p.Q5n =
    -(p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.w4) * p.G55 := by
  rw [l41_J0_closed, l41_Q5n_eq]
  linear_combination p.G55 * l41_rel_G55 p + p.g45 * l41_rel_g45 p

theorem l41_B05_zero : p.S * p.B05 + p.P4 * p.w4 * p.Q4n + p.P4 * p.w5 * p.Q5n = 0 := by
  rw [l41_B05_eq, l41_Q4n_eq, l41_Q5n_eq]; ring

theorem l41_B04_zero : p.S * p.B04 + p.P4 * p.w4p * p.Q4n + p.P4 * p.w5p * p.Q5n = 0 := by
  rw [l41_B04_eq, l41_Q4n_eq, l41_Q5n_eq]; ring

theorem l41_K04_eq : p.K04 = -(p.P4 * p.h2 * (p.h2 - p.P4 + p.P5)) * p.Q5n := by
  simp only [L41P.K04, L41P.w4p] at *
  rw [l41_B05_eq, l41_B04_eq, l41_Q5n_eq]
  simp only [L41P.w4p, L41P.w5p]
  linear_combination (-(p.P4 * p.S * p.h2) * (p.U4 * p.g45 + p.U5 * p.G55)) * l41_w_sum p

/-- **Case FB-2** final sum (`gam05 < 0`, `w5 > 0`). -/
theorem l41_FB2_sum : p.w5 * p.U4 * p.J0 + (-p.gam05) * (p.S * p.B05 + p.P4 * p.w4 * p.Q4n) =
    -(p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.w4 * p.w5) * p.G55 := by
  linear_combination p.w5 * l41_FB1_sum p + (-p.gam05) * l41_B05_zero p

/-- **Case FB-3** final sum (`gam05 < 0`, `w4' < 0`). -/
theorem l41_FB3_sum : p.h2 * (p.h2 - p.P4 + p.P5) * p.U4 * p.J0 + (-p.gam05) * p.K04 =
    -(p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.h2 * p.w4 * (p.h2 - p.P4 + p.P5)) * p.G55 := by
  rw [l41_K04_eq]
  linear_combination p.h2 * (p.h2 - p.P4 + p.P5) * l41_FB1_sum p

theorem l41_J0_expand : p.J0 = p.h2 * p.P4 * p.qA4 * (1 - p.t) * p.Q05 + p.del05 * p.W21 +
    p.h2 * p.P4 * p.w4 * p.U4 * p.W23 + p.h0 * p.G4 * p.qA4 * (1 - p.t) * p.F12 := by
  simp only [L41P.J0, L41P.B05, L41P.H, L41P.del05]; ring

/-- Region facts of Part 1A (`K1a ∩ G* ∩ Cell II`, `chi < 0`, `del05 ≥ 0`, `G55 > 0`). -/
structure L41Facts (p : L41P) : Prop where
  hS : 0 < p.S
  hh0 : 0 < p.h0
  hh02 : p.h0 < p.h2
  hh2 : 1 < p.h2
  hD0 : 0 < p.D0
  hP4 : 0 < p.P4
  hG4 : 0 < p.G4
  hU4 : 0 < p.U4
  hqA4 : 0 < p.qA4
  ht : p.t < 1
  hw4 : 0 < p.w4
  hG55 : 0 < p.G55
  hchi : p.chi < 0
  hV : p.V < 0
  hdel05 : 0 ≤ p.del05

/-- The six valid rows (`F-B ∩ {C_Q2, C_Q5-}`). -/
structure L41Rows (p : L41P) : Prop where
  hQ05 : 0 ≤ p.Q05
  hQ02 : 0 ≤ p.Q02
  hQ5n : 0 ≤ p.Q5n
  hW21 : 0 ≤ p.W21
  hW23 : 0 ≤ p.W23
  hF12 : 0 ≤ p.F12

theorem l41_Q4n_nonneg {p : L41P} (hf : L41Facts p) (hr : L41Rows p) : 0 ≤ p.Q4n := by
  have h := l41_CQ5 p
  have hc : 0 < -p.chi := neg_pos.mpr hf.hchi
  have h1 : 0 ≤ p.S * (p.h2 - p.h0) * p.Q05 + p.S * p.h0 * p.Q02 + ((-p.chi) + (-p.V)) * p.Q5n := by
    have := hf.hS; have := hf.hh02; have := hf.hh0
    have hv : 0 < -p.V := neg_pos.mpr hf.hV
    have e1 : 0 ≤ p.S * (p.h2 - p.h0) * p.Q05 := mul_nonneg (mul_nonneg hf.hS.le (by linarith)) hr.hQ05
    have e2 : 0 ≤ p.S * p.h0 * p.Q02 := mul_nonneg (mul_nonneg hf.hS.le hf.hh0.le) hr.hQ02
    have e3 : 0 ≤ ((-p.chi) + (-p.V)) * p.Q5n := mul_nonneg (by linarith) hr.hQ5n
    linarith
  rw [h] at h1
  exact nonneg_of_mul_nonneg_right h1 hc

theorem l41_Q04_nonneg {p : L41P} (hf : L41Facts p) (hr : L41Rows p) : 0 ≤ p.Q04 := by
  have h := l41_CQ5' p
  have hc : 0 < -p.chi := neg_pos.mpr hf.hchi
  have hv : 0 < -p.V := neg_pos.mpr hf.hV
  have e1 : 0 ≤ ((-p.chi) + p.S * (p.h2 - p.h0)) * p.Q05 :=
    mul_nonneg (by have := hf.hS; have := hf.hh02; nlinarith) hr.hQ05
  have e2 : 0 ≤ p.S * p.h0 * p.Q02 := mul_nonneg (mul_nonneg hf.hS.le hf.hh0.le) hr.hQ02
  have e3 : 0 ≤ (-p.V) * p.Q5n := mul_nonneg hv.le hr.hQ5n
  have h1 : 0 ≤ (-p.chi) * p.Q04 := by rw [← h]; linarith
  exact nonneg_of_mul_nonneg_right h1 hc

theorem l41_J0_nonneg {p : L41P} (hf : L41Facts p) (hr : L41Rows p) : 0 ≤ p.J0 := by
  rw [l41_J0_expand]
  have h1t : 0 < 1 - p.t := by linarith [hf.ht]
  have h2p : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.P4 * p.qA4 * (1 - p.t) * p.Q05 :=
    mul_nonneg (by positivity [hf.hP4, hf.hqA4]) hr.hQ05
  have e2 : 0 ≤ p.del05 * p.W21 := mul_nonneg hf.hdel05 hr.hW21
  have e3 : 0 ≤ p.h2 * p.P4 * p.w4 * p.U4 * p.W23 :=
    mul_nonneg (by positivity [hf.hP4, hf.hw4, hf.hU4]) hr.hW23
  have e4 : 0 ≤ p.h0 * p.G4 * p.qA4 * (1 - p.t) * p.F12 :=
    mul_nonneg (by positivity [hf.hh0, hf.hG4, hf.hqA4]) hr.hF12
  linarith

theorem l41_B05_nonneg {p : L41P} (hf : L41Facts p) (hr : L41Rows p) : 0 ≤ p.B05 := by
  simp only [L41P.B05]
  have h2p : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.P4 * p.Q05 := mul_nonneg (by positivity [hf.hP4]) hr.hQ05
  have e2 : 0 ≤ p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 :=
    mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le (by linarith [hf.hh02])) hf.hD0.le) hr.hW21
  have e3 : 0 ≤ p.h0 * p.G4 * p.F12 := mul_nonneg (mul_nonneg hf.hh0.le hf.hG4.le) hr.hF12
  linarith

theorem l41_B04_nonneg {p : L41P} (hf : L41Facts p) (hr : L41Rows p) : 0 ≤ p.B04 := by
  simp only [L41P.B04]
  have h2p : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.P4 * p.Q04 := mul_nonneg (by positivity [hf.hP4]) (l41_Q04_nonneg hf hr)
  have e2 : 0 ≤ p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 :=
    mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le (by linarith [hf.hh02])) hf.hD0.le) hr.hW21
  have e3 : 0 ≤ p.h0 * p.G4 * p.F12 := mul_nonneg (mul_nonneg hf.hh0.le hf.hG4.le) hr.hF12
  linarith

/-- The common positive constant `S^2 (h2 - 1) D0 P4 G4` of the three final sums. -/
theorem l41_c_pos {p : L41P} (hf : L41Facts p) : 0 < p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 := by
  have := hf.hS; have := hf.hh2; have := hf.hD0; have := hf.hP4; have := hf.hG4
  have : 0 < p.h2 - 1 := by linarith
  positivity

/-- **Case FB-1** (`gam05 ≥ 0`): the rows `Q05, Q02, Q5_neg, W21, W23, F12` cannot all be `≥ 0`. -/
theorem l41_FB1_false {p : L41P} (hf : L41Facts p) (hr : L41Rows p) (hgam : 0 ≤ p.gam05) : False := by
  have h := l41_FB1_sum p
  have h1 : 0 ≤ p.U4 * p.J0 + p.P4 * p.gam05 * p.Q5n :=
    add_nonneg (mul_nonneg hf.hU4.le (l41_J0_nonneg hf hr)) (mul_nonneg (mul_nonneg hf.hP4.le hgam) hr.hQ5n)
  have h2 : 0 < p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.w4 * p.G55 := by
    have := l41_c_pos hf; have := hf.hw4; have := hf.hG55; positivity
  rw [h] at h1
  nlinarith

/-- **Case FB-2** (`gam05 < 0`, `w5 > 0`). -/
theorem l41_FB2_false {p : L41P} (hf : L41Facts p) (hr : L41Rows p) (hgam : p.gam05 < 0)
    (hw5 : 0 < p.w5) : False := by
  have h := l41_FB2_sum p
  have hB := l41_B05_nonneg hf hr
  have hQ := l41_Q4n_nonneg hf hr
  have h1 : 0 ≤ p.w5 * p.U4 * p.J0 + (-p.gam05) * (p.S * p.B05 + p.P4 * p.w4 * p.Q4n) :=
    add_nonneg (mul_nonneg (mul_nonneg hw5.le hf.hU4.le) (l41_J0_nonneg hf hr))
      (mul_nonneg (neg_nonneg.mpr hgam.le)
        (add_nonneg (mul_nonneg hf.hS.le hB) (mul_nonneg (mul_nonneg hf.hP4.le hf.hw4.le) hQ)))
  have h2 : 0 < p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.w4 * p.w5 * p.G55 := by
    have := l41_c_pos hf; have := hf.hw4; have := hf.hG55; positivity
  rw [h] at h1
  nlinarith

/-- **Case FB-3** (`gam05 < 0`, `w4' < 0`; Carbon: `w5 ≤ 0`, see `A41-REFEREE` F4), with `w4 + w5 > 0`. -/
theorem l41_FB3_false {p : L41P} (hf : L41Facts p) (hr : L41Rows p) (hgam : p.gam05 < 0)
    (hw4p : p.w4p < 0) (hws : 0 < p.h2 - p.P4 + p.P5) : False := by
  have h := l41_FB3_sum p
  have hB5 := l41_B05_nonneg hf hr
  have hB4 := l41_B04_nonneg hf hr
  have hK : 0 ≤ p.K04 := add_nonneg (mul_nonneg (neg_nonneg.mpr hw4p.le) hB5) (mul_nonneg hf.hw4.le hB4)
  have h1 : 0 ≤ p.h2 * (p.h2 - p.P4 + p.P5) * p.U4 * p.J0 + (-p.gam05) * p.K04 :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith [hf.hh2]) hws.le) hf.hU4.le)
      (l41_J0_nonneg hf hr)) (mul_nonneg (neg_nonneg.mpr hgam.le) hK)
  have h2 : 0 < p.S ^ 2 * (p.h2 - 1) * p.D0 * p.P4 * p.G4 * p.h2 * p.w4 * (p.h2 - p.P4 + p.P5) * p.G55 := by
    have := l41_c_pos hf; have := hf.hw4; have := hf.hG55; have : 0 < p.h2 := by linarith [hf.hh2]
    positivity
  rw [h] at h1
  nlinarith

/-! ### Bridge to `NF29` and the actual metric -/

variable {x : Fin 7 → ℝ³}

/-- The parameters of `L41P` of an `NF29` shape: `G_ij = ⟪x_i - x_6, x_j - x_6⟫`. -/
noncomputable def l41P_of (N : NF29 x) : L41P :=
  ⟨N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t, ⟪x 4 - x 6, x 4 - x 6⟫, ⟪x 5 - x 6, x 5 - x 6⟫,
    ⟪x 4 - x 6, x 5 - x 6⟫, ⟪x 3 - x 6, x 4 - x 6⟫, ⟪x 3 - x 6, x 5 - x 6⟫⟩

theorem l41_G55_pos (N : NF29 x) : 0 < (l41P_of N).G55 := by
  refine real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => ?_)
  exact absurd (N.inj h) (by decide)

/-- The two `W14` rows of `¬ LexAny29` are the rows `W21`, `W23` of `L41P`. -/
theorem l41_rows_W (N : NF29 x) (ha2 : N.a2 < 0) (ht : N.t < 1) (hdG4 : 0 < N.dG4)
    (hA : 0 < 1 - N.b0 - N.h0) (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ (l41P_of N).W21 ∧ 0 ≤ (l41P_of N).W23 :=
  w14_of_not_lexAny29 N ha2 ht hdG4 hA hnf

/-- `F12 = S (z1 - z2)(v012)` in `Row_sp` form (the form returned by `fb_of_not_lexAny29`). -/
theorem l41_F12_eq (N : NF29 x) : (l41P_of N).F12 =
    Row_sp (N.s - P2_sp N.a2 N.b2 N.h2 N.s N.t) (N.t - D234_sp N.a2 N.b2 N.h2 N.s N.t) (-N.h2)
      (v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫ ⟪x 3 - x 6, x 4 - x 6⟫
      ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  simp only [l41P_of, L41P.F12, L41P.row, Row_sp, L41P.S]; ring

end L41Part1A

end Minimality.NF29
