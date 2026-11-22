import Minimality.M4dType24
import Minimality.Type24QuadW02
import Minimality.Type24Regions

/-!
# Type 24, region A2, line `w02`: the `Lambda5 > omega3` part (group a20)

`w02_cminus_empty` (A20.2), `w02_lam5_false` (A20.5), `splitAny_w02_ppp_e12 / _e36` (A20.3),
`a2_lam5_closed` (A20.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality.GenQuad (FrontDet)

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10
  Minimality.T24.A8 Minimality.T24.Q24 Minimality.T24 Minimality.T24.A15

/-! ### A20.2 `w02_cminus_empty` -/

theorem w02_ident {x : Fin 7 → ℝ³} {a3 b3 c3 a5 b5 c5 : ℝ}
    (h3 : x 3 - x 1 = a3 • (x 0 - x 1) + b3 • (x 2 - x 1) + c3 • (x 6 - x 1))
    (h5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1)) :
    a5 * z x (bW02 x) 3 = a3 * z x (bW02 x) 5 + (a5 * b3 - a3 * b5) * z x (bW02 x) 2 +
      (a5 * c3 - a3 * c5) * z x (bW02 x) 6 := by
  have key : a5 • (x 3 - x 1) - a3 • (x 5 - x 1) =
      (a5 * b3 - a3 * b5) • (x 2 - x 1) + (a5 * c3 - a3 * c5) • (x 6 - x 1) := by
    rw [h3, h5]; module
  have := congrArg (fun v => ⟪v, bW02 x⟫) key
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at this
  simp only [z, inner_sub_left]; linear_combination this

theorem w02_cminus_empty {x : Fin 7 → ℝ³} {a3 b3 c3 a5 b5 c5 : ℝ}
    (h3 : x 3 - x 1 = a3 • (x 0 - x 1) + b3 • (x 2 - x 1) + c3 • (x 6 - x 1))
    (h5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1))
    (ha3 : 0 < a3) (ha5 : 0 < a5)
    (hp : a3 * b5 < a5 * b3) (hr : a3 * c5 ≤ a5 * c3)
    (hs : a5 < a3 + (a5 * b3 - a3 * b5) + (a5 * c3 - a3 * c5))
    (hz2 : z x (bW02 x) 2 < 0)
    (h5' : z x (bW02 x) 5 ≤ min 0 (z x (bW02 x) 3))
    (h26 : max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min 0 (z x (bW02 x) 3)) : False := by
  have e := w02_ident h3 h5
  simp only [le_min_iff, max_le_iff] at h5' h26
  obtain ⟨h50, h53⟩ := h5'
  obtain ⟨⟨h2n, h6n⟩, h23, h63⟩ := h26
  set p := a5 * b3 - a3 * b5 with hpdef
  set r := a5 * c3 - a3 * c5 with hrdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  set z2 := z x (bW02 x) 2
  set z3 := z x (bW02 x) 3
  set z5 := z x (bW02 x) 5
  set z6 := z x (bW02 x) 6
  have hz3le : z3 ≤ 0 := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos ha5 hc, mul_nonneg ha3.le (neg_nonneg.mpr h50), mul_nonneg hp0.le (neg_nonneg.mpr h2n),
      mul_nonneg hr0 (neg_nonneg.mpr h6n)]
  have hz3ge : 0 ≤ z3 := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg ha3.le (sub_nonneg.mpr h53), mul_nonneg hp0.le (sub_nonneg.mpr h23),
      mul_nonneg hr0 (sub_nonneg.mpr h63), mul_pos (show 0 < a3 + p + r - a5 by linarith) (neg_pos.mpr hc)]
  have hz30 : z3 = 0 := le_antisymm hz3le hz3ge
  nlinarith [mul_nonneg ha3.le (neg_nonneg.mpr h50), mul_nonneg hr0 (neg_nonneg.mpr h6n),
    mul_pos hp0 (neg_pos.mpr hz2)]

/-! ### A20.5 `w02_lam5_false` -/

theorem w02_lam5_false {x : Fin 7 → ℝ³} {a5 b5 c5 : ℝ}
    (h5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1))
    (hom5 : c5 * omega5 x = a5 + b5 - 1)
    (hLam : Lam5 x = b5 + c5 + omega3 x * (1 - a5))
    (hom3 : 0 < omega3 x) (hc5 : 0 ≤ c5) (hL : omega3 x < Lam5 x) (h02 : x 0 ≠ x 2)
    (hu07 : 0 ≤ ⟪x 2 - x 0, u07 x⟫) (hu27 : 0 ≤ ⟪x 2 - x 0, u27 x⟫)
    (hz5 : 0 ≤ z x (bW02 x) 5) : False := by
  have hbb : 0 < ⟪bW02 x, bW02 x⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr h02)
  have hb : x 2 - x 0 = -bW02 x := by simp [bW02]
  rw [hb, inner_neg_left] at hu07 hu27
  have hbb' : ⟪bW02 x, bW02 x⟫ = ⟪bW02 x, x 0 - x 1⟫ - ⟪bW02 x, x 2 - x 1⟫ := by
    conv_lhs => rw [show bW02 x = (x 0 - x 1) - (x 2 - x 1) by simp [bW02]]
    rw [← show bW02 x = (x 0 - x 1) - (x 2 - x 1) by simp [bW02]]
    rw [← inner_sub_right]; congr 1; simp [bW02]
  have e5 : z x (bW02 x) 5 = a5 * ⟪bW02 x, x 0 - x 1⟫ + b5 * ⟪bW02 x, x 2 - x 1⟫ +
      c5 * ⟪bW02 x, x 6 - x 1⟫ := by
    simp only [z]
    rw [real_inner_comm, h5]
    simp only [inner_add_right, real_inner_smul_right]
  have e07 : ⟪bW02 x, u07 x⟫ = ⟪bW02 x, x 0 - x 1⟫ + omega3 x * ⟪bW02 x, x 2 - x 1⟫ := by
    simp only [u07, inner_add_right, real_inner_smul_right]
  have e27 : ⟪bW02 x, u27 x⟫ = (1 + omega5 x) * ⟪bW02 x, x 0 - x 1⟫ +
      (omega3 x * omega5 x - 1) * ⟪bW02 x, x 2 - x 1⟫ + (1 + omega3 x) * ⟪bW02 x, x 6 - x 1⟫ := by
    simp only [u27, inner_add_right, real_inner_smul_right]
  rw [e07] at hu07; rw [e27] at hu27
  rw [e5] at hz5
  rw [hbb'] at hbb
  set P0 := ⟪bW02 x, x 0 - x 1⟫
  set P2 := ⟪bW02 x, x 2 - x 1⟫
  set P6 := ⟪bW02 x, x 6 - x 1⟫
  have key : (1 + omega3 x) * (a5 * P0 + b5 * P2 + c5 * P6) =
      (omega3 x - Lam5 x) * (P0 - P2) + (P0 + omega3 x * P2) +
        c5 * ((1 + omega5 x) * P0 + (omega3 x * omega5 x - 1) * P2 + (1 + omega3 x) * P6) := by
    rw [hLam]; linear_combination (-P0 - omega3 x * P2) * hom5
  nlinarith [mul_nonneg hom3.le hz5, mul_nonneg hc5 hu27, mul_pos (sub_pos.mpr hL) hbb]

/-! ### A20.3 level-0 split leaves at `w02+++` -/

private def cW : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
private theorem cW_inj : Function.Injective cW := by decide

/-- Shared setup of the level-0 split leaves at `w02+++` (facings strict except at the facets `0`, `2`,
which are tilted by `d1 = x 0 - x 3`). -/
theorem splitAny_w02_ppp_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (a cc : ZMod 5) (hca : cc ≠ a) (hca1 : cc ≠ a + 1) (σ : ℝ)
    (hrows : ∀ i : ZMod 5, i ≠ a → ∀ j : ZMod 5, (j = i ∨ j = i + 1) → j ≠ cc →
      ∃ s : ℝ, 0 < s * ⟪x (cW j) - x (cW cc), bW02 x⟫ ∧
        0 < σ * s * det3 (x (cW (i + 1)) - x (cW i)) (x (cW (a + 1)) - x (cW a)) (bW02 x)) :
    SplitAny24 F := by
  let pat : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8)
  have hcyc : S0xCycOK s0x_S24 cW pat := by unfold S0xCycOK; decide
  let d1 : ℝ³ := x 0 - x 3
  refine splitAny24_of_lex3' F (by decide) cW cW_inj pat hcyc (bW02 x) d1 0 ?_ a cc hca hca1 σ ?_
  · intro t
    have e : ∀ t : Fin 9, pat t = true ↔ (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8) := by
      intro t; simp only [pat, decide_eq_true_eq]
    by_cases ht : pat t = true
    · simp only [ht, ↓reduceIte]
      rcases (e t).1 ht with rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inr ⟨bW02_N0 F, Or.inl ?_⟩
        simp only [d1, F.inner_sub, F.zero 0 0 (by decide)]
        have := F.neg 0 3 (by decide); linarith
      · exact Or.inl h1
      · refine Or.inr ⟨bW02_N2 F, Or.inl ?_⟩
        simp only [d1, F.inner_sub, F.zero 2 0 (by decide)]
        have := F.neg 2 3 (by decide); linarith
      · exact Or.inl h3
      · exact Or.inl h4
      · exact Or.inl h8
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      have : t = 5 ∨ t = 6 ∨ t = 7 := by
        have := (e t).not.1 ht
        revert this; revert t; decide
      rcases this with rfl | rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
  · intro i hi j hj hjc
    obtain ⟨s, hs, hd⟩ := hrows i hi j hj hjc
    exact ⟨s, Or.inl hs, Or.inl (by simpa using hd)⟩

/-- As `splitAny_w02_ppp_core`, with the tilt `d1 = x 0 - x 6` (Carbon's tie tilt) and rows that may be
lex-positive through the tilt. -/
theorem splitAny_w02_ppp_core_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (a cc : ZMod 5) (hca : cc ≠ a) (hca1 : cc ≠ a + 1) (σ : ℝ)
    (hrows : ∀ i : ZMod 5, i ≠ a → ∀ j : ZMod 5, (j = i ∨ j = i + 1) → j ≠ cc →
      ∃ s : ℝ, (0 < s * ⟪x (cW j) - x (cW cc), bW02 x⟫ ∨
        (s * ⟪x (cW j) - x (cW cc), bW02 x⟫ = 0 ∧ 0 < s * ⟪x (cW j) - x (cW cc), x 0 - x 6⟫)) ∧
        0 < σ * s * det3 (x (cW (i + 1)) - x (cW i)) (x (cW (a + 1)) - x (cW a)) (bW02 x)) :
    SplitAny24 F := by
  let pat : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8)
  have hcyc : S0xCycOK s0x_S24 cW pat := by unfold S0xCycOK; decide
  let d1 : ℝ³ := x 0 - x 6
  refine splitAny24_of_lex3' F (by decide) cW cW_inj pat hcyc (bW02 x) d1 0 ?_ a cc hca hca1 σ ?_
  · intro t
    have e : ∀ t : Fin 9, pat t = true ↔ (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8) := by
      intro t; simp only [pat, decide_eq_true_eq]
    by_cases ht : pat t = true
    · simp only [ht, ↓reduceIte]
      rcases (e t).1 ht with rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inr ⟨bW02_N0 F, Or.inl ?_⟩
        simp only [d1, F.inner_sub, F.zero 0 0 (by decide)]
        have := F.neg 0 6 (by decide); linarith
      · exact Or.inl h1
      · refine Or.inr ⟨bW02_N2 F, Or.inl ?_⟩
        simp only [d1, F.inner_sub, F.zero 2 0 (by decide)]
        have := F.neg 2 6 (by decide); linarith
      · exact Or.inl h3
      · exact Or.inl h4
      · exact Or.inl h8
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      have : t = 5 ∨ t = 6 ∨ t = 7 := by
        have := (e t).not.1 ht
        revert this; revert t; decide
      rcases this with rfl | rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
  · intro i hi j hj hjc
    obtain ⟨s, hs, hd⟩ := hrows i hi j hj hjc
    refine ⟨s, ?_, Or.inl (by simpa using hd)⟩
    rcases hs with hs | ⟨hs0, hs1⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hs0, Or.inl (by simpa using hs1)⟩

theorem inner_sub_w02 (x : Fin 7 → ℝ³) (u v : Fin 7) :
    ⟪x u - x v, bW02 x⟫ = z x (bW02 x) u - z x (bW02 x) v := by
  simp only [z, ← inner_sub_left]; congr 1; abel

theorem z_one_w02 (x : Fin 7 → ℝ³) : z x (bW02 x) 1 = 0 := by simp [z]

/-- The row determinant at `w02` of two frame-coordinate vectors. -/
theorem det3_w02 {x : Fin 7 → ℝ³} {P0 P1 P2 Q0 Q1 Q2 : ℝ} {u v p q : Fin 7}
    (hP : x u - x v = P0 • (x 0 - x 1) + P1 • (x 2 - x 1) + P2 • (x 6 - x 1))
    (hQ : x p - x q = Q0 • (x 0 - x 1) + Q1 • (x 2 - x 1) + Q2 • (x 6 - x 1)) :
    det3 (x u - x v) (x p - x q) (bW02 x) = ((P0 + P1) * Q2 - P2 * (Q0 + Q1)) * det24 x := by
  have hb : bW02 x = (1 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    simp only [bW02]; module
  rw [hP, hQ, hb, Minimality.T24.M4.det3_frame x P0 P1 P2 Q0 Q1 Q2 1 (-1) 0]
  ring

theorem hrep_w02 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  rw [T.rep v]; abel

theorem splitAny_w02_ppp_e12 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (hc5 : 0 < oblX6 x 5) (hc53 : oblX6 x 5 < oblX6 x 3) (hc3 : oblX6 x 3 < 1)
    (hz : max (z x (bW02 x) 2) (max (z x (bW02 x) 5) (z x (bW02 x) 3)) < z x (bW02 x) 6)
    (hz6 : z x (bW02 x) 6 < 0) : SplitAny24 F := by
  have T := type24OfFac F
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  simp only [max_lt_iff] at hz
  obtain ⟨hz2, hz5, hz3⟩ := hz
  have e5 := hrep_w02 F 5
  have e3 := hrep_w02 F 3
  have ed : ∀ u v : Fin 7, ⟪x u - x v, bW02 x⟫ = z x (bW02 x) u - z x (bW02 x) v := inner_sub_w02 x
  have z1 := z_one_w02 x
  refine splitAny_w02_ppp_core F h1 h3 h4 h8 h5 h6 h7 0 4 (by decide) (by decide) (det24 x) ?_
  intro i hi j hj hjc
  have hi'' : ∀ i : ZMod 5, i ≠ 0 → i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  have hi' := hi'' i hi
  have q : x 2 - x 1 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
  rcases hi' with rfl | rfl | rfl | rfl
  · have D := det3_w02 (u := 5) (v := 2) (p := 2) (q := 1)
      (P0 := oblX0 x 5) (P1 := oblX2 x 5 - 1) (P2 := oblX6 x 5) (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, e5]; module) q
    have hj' : j = 1 ∨ j = 2 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 2 - x 6, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 6, bW02 x⟫
        rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 5 - x 2) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * (((oblX0 x 5 + (oblX2 x 5 - 1)) * 0 - oblX6 x 5 * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * oblX6 x 5 := by ring
      rw [this]; exact mul_pos hd2 hc5
  · have D := det3_w02 (u := 3) (v := 5) (p := 2) (q := 1)
      (P0 := oblX0 x 3 - oblX0 x 5) (P1 := oblX2 x 3 - oblX2 x 5) (P2 := oblX6 x 3 - oblX6 x 5)
      (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 3 - x 5 = (x 3 - x 1) - (x 5 - x 1) by abel, e5, e3]; module) q
    have hj' : j = 2 ∨ j = 3 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 6, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 3 - x 6, bW02 x⟫
        rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 3 - x 5) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * ((((oblX0 x 3 - oblX0 x 5) + (oblX2 x 3 - oblX2 x 5)) * 0 -
          (oblX6 x 3 - oblX6 x 5) * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * (oblX6 x 3 - oblX6 x 5) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 6) (v := 3) (p := 2) (q := 1)
      (P0 := -oblX0 x 3) (P1 := -oblX2 x 3) (P2 := 1 - oblX6 x 3)
      (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) by abel, e3]; module) q
    have hj' : j = 3 := by
      rcases hj with h | h
      · exact h
      · exact absurd (h.trans (by decide)) hjc
    subst hj'
    refine ⟨-1, ?_, ?_⟩
    · change 0 < (-1 : ℝ) * ⟪x 3 - x 6, bW02 x⟫
      rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 6 - x 3) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * ((((-oblX0 x 3) + (-oblX2 x 3)) * 0 -
          (1 - oblX6 x 3) * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * (1 - oblX6 x 3) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 1) (v := 6) (p := 2) (q := 1)
      (P0 := 0) (P1 := 0) (P2 := -1) (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by module) q
    have hj' : j = 0 := by
      rcases hj with h | h
      · exact absurd h hjc
      · exact h.trans (by decide)
    subst hj'
    refine ⟨1, ?_, ?_⟩
    · change 0 < (1 : ℝ) * ⟪x 1 - x 6, bW02 x⟫
      rw [ed]; linarith
    · change 0 < det24 x * 1 * det3 (x 1 - x 6) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * 1 * (((0 + 0) * 0 - (-1) * (0 + 1)) * det24 x) = det24 x * det24 x := by ring
      rw [this]; exact hd2

theorem splitAny_w02_ppp_e12_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (hc5 : 0 < oblX6 x 5) (hc53 : oblX6 x 5 < oblX6 x 3) (hc3 : oblX6 x 3 < 1)
    (hz : max (z x (bW02 x) 2) (max (z x (bW02 x) 5) (z x (bW02 x) 3)) < z x (bW02 x) 6)
    (hz6 : z x (bW02 x) 6 ≤ 0) (hCB : 0 < ⟪x 1 - x 6, x 0 - x 6⟫) : SplitAny24 F := by
  have T := type24OfFac F
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  simp only [max_lt_iff] at hz
  obtain ⟨hz2, hz5, hz3⟩ := hz
  have e5 := hrep_w02 F 5
  have e3 := hrep_w02 F 3
  have ed : ∀ u v : Fin 7, ⟪x u - x v, bW02 x⟫ = z x (bW02 x) u - z x (bW02 x) v := inner_sub_w02 x
  have z1 := z_one_w02 x
  refine splitAny_w02_ppp_core_tilt F h1 h3 h4 h8 h5 h6 h7 0 4 (by decide) (by decide) (det24 x) ?_
  intro i hi j hj hjc
  have hi'' : ∀ i : ZMod 5, i ≠ 0 → i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  have hi' := hi'' i hi
  have q : x 2 - x 1 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
  rcases hi' with rfl | rfl | rfl | rfl
  · have D := det3_w02 (u := 5) (v := 2) (p := 2) (q := 1)
      (P0 := oblX0 x 5) (P1 := oblX2 x 5 - 1) (P2 := oblX6 x 5) (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, e5]; module) q
    have hj' : j = 1 ∨ j = 2 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · left
      rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 2 - x 6, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 6, bW02 x⟫
        rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 5 - x 2) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * (((oblX0 x 5 + (oblX2 x 5 - 1)) * 0 - oblX6 x 5 * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * oblX6 x 5 := by ring
      rw [this]; exact mul_pos hd2 hc5
  · have D := det3_w02 (u := 3) (v := 5) (p := 2) (q := 1)
      (P0 := oblX0 x 3 - oblX0 x 5) (P1 := oblX2 x 3 - oblX2 x 5) (P2 := oblX6 x 3 - oblX6 x 5)
      (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 3 - x 5 = (x 3 - x 1) - (x 5 - x 1) by abel, e5, e3]; module) q
    have hj' : j = 2 ∨ j = 3 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · left
      rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 6, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 3 - x 6, bW02 x⟫
        rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 3 - x 5) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * ((((oblX0 x 3 - oblX0 x 5) + (oblX2 x 3 - oblX2 x 5)) * 0 -
          (oblX6 x 3 - oblX6 x 5) * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * (oblX6 x 3 - oblX6 x 5) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 6) (v := 3) (p := 2) (q := 1)
      (P0 := -oblX0 x 3) (P1 := -oblX2 x 3) (P2 := 1 - oblX6 x 3)
      (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by rw [show x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) by abel, e3]; module) q
    have hj' : j = 3 := by
      rcases hj with h | h
      · exact h
      · exact absurd (h.trans (by decide)) hjc
    subst hj'
    refine ⟨-1, ?_, ?_⟩
    · left
      change 0 < (-1 : ℝ) * ⟪x 3 - x 6, bW02 x⟫
      rw [ed]; linarith
    · change 0 < det24 x * (-1) * det3 (x 6 - x 3) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * -1 * ((((-oblX0 x 3) + (-oblX2 x 3)) * 0 -
          (1 - oblX6 x 3) * (0 + 1)) * det24 x) =
        (det24 x * det24 x) * (1 - oblX6 x 3) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 1) (v := 6) (p := 2) (q := 1)
      (P0 := 0) (P1 := 0) (P2 := -1) (Q0 := 0) (Q1 := 1) (Q2 := 0)
      (by module) q
    have hj' : j = 0 := by
      rcases hj with h | h
      · exact absurd h hjc
      · exact h.trans (by decide)
    subst hj'
    refine ⟨1, ?_, ?_⟩
    · rcases lt_or_eq_of_le hz6 with h6l | h6e
      · left
        change 0 < (1 : ℝ) * ⟪x 1 - x 6, bW02 x⟫
        rw [ed]; linarith
      · right
        refine ⟨?_, by change 0 < (1 : ℝ) * ⟪x 1 - x 6, x 0 - x 6⟫; linarith⟩
        change (1 : ℝ) * ⟪x 1 - x 6, bW02 x⟫ = 0
        rw [ed]; linarith
    · change 0 < det24 x * 1 * det3 (x 1 - x 6) (x 2 - x 1) (bW02 x)
      rw [D]
      have : det24 x * 1 * (((0 + 0) * 0 - (-1) * (0 + 1)) * det24 x) = det24 x * det24 x := by ring
      rw [this]; exact hd2

theorem splitAny_w02_ppp_e36 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (hc5 : 0 < oblX6 x 5) (hc3 : oblX6 x 3 < 1) (hS3 : 0 < oblX0 x 3 + oblX2 x 3)
    (hab5 : 0 < oblX0 x 5 + oblX2 x 5 - 1)
    (hconv : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3))
    (hz : max (z x (bW02 x) 2) (max (z x (bW02 x) 5) (z x (bW02 x) 3)) < 0)
    (hz6 : 0 < z x (bW02 x) 6) : SplitAny24 F := by
  have T := type24OfFac F
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  simp only [max_lt_iff] at hz
  obtain ⟨hz2, hz5, hz3⟩ := hz
  have e5 := hrep_w02 F 5
  have e3 := hrep_w02 F 3
  have ed : ∀ u v : Fin 7, ⟪x u - x v, bW02 x⟫ = z x (bW02 x) u - z x (bW02 x) v := inner_sub_w02 x
  have z1 := z_one_w02 x
  refine splitAny_w02_ppp_core F h1 h3 h4 h8 h5 h6 h7 3 0 (by decide) (by decide) (-det24 x) ?_
  intro i hi j hj hjc
  have hi'' : ∀ i : ZMod 5, i ≠ 3 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 := by decide
  have hi' := hi'' i hi
  have q : x 6 - x 3 = (-oblX0 x 3) • (x 0 - x 1) + (-oblX2 x 3) • (x 2 - x 1) +
      (1 - oblX6 x 3) • (x 6 - x 1) := by
    rw [show x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) by abel, e3]; module
  have hn : 0 < -(det24 x) * -(det24 x) := by nlinarith
  rcases hi' with rfl | rfl | rfl | rfl
  · have D := det3_w02 (u := 2) (v := 1) (p := 6) (q := 3)
      (P0 := 0) (P1 := 1) (P2 := 0) (Q0 := -oblX0 x 3) (Q1 := -oblX2 x 3) (Q2 := 1 - oblX6 x 3)
      (by module) q
    have hj' : j = 1 := by
      rcases hj with h | h
      · exact absurd h hjc
      · exact h.trans (by decide)
    subst hj'
    refine ⟨-1, ?_, ?_⟩
    · change 0 < (-1 : ℝ) * ⟪x 2 - x 1, bW02 x⟫
      rw [ed]; linarith
    · change 0 < -(det24 x) * (-1) * det3 (x 2 - x 1) (x 6 - x 3) (bW02 x)
      rw [D]
      have : -(det24 x) * -1 * (((0 + 1) * (1 - oblX6 x 3) - 0 * (-oblX0 x 3 + -oblX2 x 3)) * det24 x) =
        (det24 x * det24 x) * (1 - oblX6 x 3) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 5) (v := 2) (p := 6) (q := 3)
      (P0 := oblX0 x 5) (P1 := oblX2 x 5 - 1) (P2 := oblX6 x 5)
      (Q0 := -oblX0 x 3) (Q1 := -oblX2 x 3) (Q2 := 1 - oblX6 x 3)
      (by rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, e5]; module) q
    have hj' : j = 1 ∨ j = 2 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 2 - x 1, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 1, bW02 x⟫
        rw [ed]; linarith
    · change 0 < -(det24 x) * (-1) * det3 (x 5 - x 2) (x 6 - x 3) (bW02 x)
      rw [D]
      have : -(det24 x) * -1 * (((oblX0 x 5 + (oblX2 x 5 - 1)) * (1 - oblX6 x 3) -
          oblX6 x 5 * (-oblX0 x 3 + -oblX2 x 3)) * det24 x) =
        (det24 x * det24 x) * ((oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 3) +
          oblX6 x 5 * (oblX0 x 3 + oblX2 x 3)) := by ring
      rw [this]; refine mul_pos hd2 ?_
      nlinarith [mul_pos hab5 (sub_pos.mpr hc3), mul_pos hc5 hS3]
  · have D := det3_w02 (u := 3) (v := 5) (p := 6) (q := 3)
      (P0 := oblX0 x 3 - oblX0 x 5) (P1 := oblX2 x 3 - oblX2 x 5) (P2 := oblX6 x 3 - oblX6 x 5)
      (Q0 := -oblX0 x 3) (Q1 := -oblX2 x 3) (Q2 := 1 - oblX6 x 3)
      (by rw [show x 3 - x 5 = (x 3 - x 1) - (x 5 - x 1) by abel, e5, e3]; module) q
    have hj' : j = 2 ∨ j = 3 := by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (by decide))
    refine ⟨-1, ?_, ?_⟩
    · rcases hj' with rfl | rfl
      · change 0 < (-1 : ℝ) * ⟪x 5 - x 1, bW02 x⟫
        rw [ed]; linarith
      · change 0 < (-1 : ℝ) * ⟪x 3 - x 1, bW02 x⟫
        rw [ed]; linarith
    · change 0 < -(det24 x) * (-1) * det3 (x 3 - x 5) (x 6 - x 3) (bW02 x)
      rw [D]
      have : -(det24 x) * -1 * ((((oblX0 x 3 - oblX0 x 5) + (oblX2 x 3 - oblX2 x 5)) * (1 - oblX6 x 3) -
          (oblX6 x 3 - oblX6 x 5) * (-oblX0 x 3 + -oblX2 x 3)) * det24 x) =
        (det24 x * det24 x) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) := by ring
      rw [this]; exact mul_pos hd2 (by linarith)
  · have D := det3_w02 (u := 1) (v := 6) (p := 6) (q := 3)
      (P0 := 0) (P1 := 0) (P2 := -1) (Q0 := -oblX0 x 3) (Q1 := -oblX2 x 3) (Q2 := 1 - oblX6 x 3)
      (by module) q
    have hj' : j = 4 := by
      rcases hj with h | h
      · exact h
      · exact absurd (h.trans (by decide)) hjc
    subst hj'
    refine ⟨1, ?_, ?_⟩
    · change 0 < (1 : ℝ) * ⟪x 6 - x 1, bW02 x⟫
      rw [ed]; linarith
    · change 0 < -(det24 x) * 1 * det3 (x 1 - x 6) (x 6 - x 3) (bW02 x)
      rw [D]
      have : -(det24 x) * 1 * (((0 + 0) * (1 - oblX6 x 3) - (-1) * (-oblX0 x 3 + -oblX2 x 3)) * det24 x) =
        (det24 x * det24 x) * (oblX0 x 3 + oblX2 x 3) := by ring
      rw [this]; exact mul_pos hd2 hS3

/-! ### A20.6 `a2_lam5_closed` -/

/-- Pure linear core, `z6 < 0`: the five `ppp` clauses, the five `pmm` clauses and the failure of the `e12`
split give `C-` or `z5 >= 0`. -/
theorem z_core_neg (z0 z2 z3 z5 z6 : ℝ) (hz2 : z2 < 0) (h6 : z6 < 0)
    (P1 : (max z2 z3 ≤ min 0 z5) ∨ (max z2 z6 ≤ min 0 z5) ∨ (max z2 z6 ≤ min 0 z3) ∨
      (max 0 z3 ≤ min z5 z6) ∨ (max z2 z3 ≤ min z5 z6))
    (P2 : (max 0 z3 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z3) ∨
      (max z6 z5 ≤ min z0 z3) ∨ (max 0 z3 ≤ min z6 z5))
    (S1 : ¬ (max z2 (max z5 z3) < z6)) :
    (z5 ≤ min 0 z3 ∧ max z2 z6 ≤ min 0 z3) ∨ 0 ≤ z5 := by
  simp only [max_lt_iff, not_and_or, not_lt, max_le_iff, le_min_iff] at *
  rcases P1 with ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ <;>
  rcases P2 with ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ <;>
  rcases S1 with s | s | s <;>
  by_cases hq : 0 ≤ z5 <;> first | exact Or.inr hq | (left; push Not at hq; and_intros <;> linarith)

/-- Pure linear core, `0 < z6`. -/
theorem z_core_pos (z0 z2 z3 z5 z6 : ℝ) (hz2 : z2 < 0) (h6 : 0 < z6)
    (P1 : (max z2 z3 ≤ min 0 z5) ∨ (max z2 z6 ≤ min 0 z5) ∨ (max z2 z6 ≤ min 0 z3) ∨
      (max 0 z3 ≤ min z5 z6) ∨ (max z2 z3 ≤ min z5 z6))
    (P2 : (max 0 z3 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z3) ∨
      (max z6 z5 ≤ min z0 z3) ∨ (max 0 z3 ≤ min z6 z5))
    (S2 : ¬ (max z2 (max z5 z3) < 0)) : 0 ≤ z5 := by
  simp only [max_lt_iff, not_and_or, not_lt, max_le_iff, le_min_iff] at *
  rcases P1 with ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ <;>
  rcases P2 with ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ | ⟨⟨b1,b2⟩,b3,b4⟩ <;>
  rcases S2 with s | s | s <;>
  by_contra hh <;> push Not at hh <;> linarith

/-! ### `u27` back-diagonal bound (the U leaf at `u27`) -/

theorem inner_u27 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u27 x⟫ = (1 + omega5 x) * (F.f t (x 0) - F.f t (x 1)) +
      (omega3 x * omega5 x - 1) * (F.f t (x 2) - F.f t (x 1)) +
      (1 + omega3 x) * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [u27, inner_add_right, real_inner_smul_right, ← F.hN t (x 0) (x 1),
    ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem u27_z_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hu3 : 0 < ⟪F.N 3, u27 x⟫) (hu8 : 0 < ⟪F.N 8, u27 x⟫) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 2 - x 0, u27 x⟫ := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hD24 : 0 ≤ Delta24 x := hC.2.2.2
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hu_ne : u27 x ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at hcon; exact lt_irrefl _ hcon
  -- facings at `(u27, x 2 - x 1, 0)`, `U := {2, 3, 7, 8}`, `Dn := {0, 4, 5}`
  have hu0 : ⟪F.N 0, u27 x⟫ < 0 := by
    rw [inner_u27, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    nlinarith [F.neg 0 6 (by decide)]
  have hu5 : ⟪F.N 5, u27 x⟫ < 0 := by
    rw [inner_u27, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    nlinarith [F.neg 5 0 (by decide), mul_neg_of_pos_of_neg (show 0 < 1 + omega5 x by linarith)
      (F.neg 5 0 (by decide))]
  have hu2 : ⟪F.N 2, u27 x⟫ = 0 := by
    have ev := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
    have e5 := Minimality.T24.M4.eq5 F
    have hprod : oblX6 x 5 * ⟪F.N 2, u27 x⟫ = 0 := by
      rw [inner_u27, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
      linear_combination (1 + omega3 x) * (-ev) + (1 + omega3 x) * F.f 2 (x 1) * e5
    exact (mul_eq_zero.mp hprod).resolve_left hc5.ne'
  have hu7 : ⟪F.N 7, u27 x⟫ = 0 := by
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have ev3 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
    have e3 := Minimality.T24.M4.eq3 F
    have h70 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
      have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
        linear_combination -ev3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')
    rw [inner_u27, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    linear_combination (1 + omega5 x) * h70
  have hu4 : ⟪F.N 4, u27 x⟫ ≤ 0 := by
    have ev := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have e4 := Minimality.T24.M4.eq4 F
    have hprod : oblX2 x 4 * ⟪F.N 4, u27 x⟫ = oblX2 x 4 * (F.f 4 (x 1) * Delta24 x) := by
      rw [inner_u27, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
      simp only [Delta24]
      linear_combination (omega3 x * omega5 x - 1) * (-ev) +
        (omega3 x * omega5 x - 1) * F.f 4 (x 1) * e4
    have := mul_left_cancel₀ hb4.ne' hprod
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (F.neg 4 1 (by decide)).le hD24
  have hd2 : 0 < ⟪F.N 2, x 2 - x 1⟫ := by
    rw [← F.hN 2 (x 2) (x 1), F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hd7 : 0 < ⟪F.N 7, x 2 - x 1⟫ := by
    rw [← F.hN 7 (x 2) (x 1), F.zero 7 2 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hd4 : 0 < -⟪F.N 4, x 2 - x 1⟫ := by
    have ev := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have e4 := Minimality.T24.M4.eq4 F
    have hprod : oblX2 x 4 * (F.f 4 (x 2) - F.f 4 (x 1)) = oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
      linear_combination -ev + F.f 4 (x 1) * e4
    have := mul_left_cancel₀ hb4.ne' hprod
    rw [← F.hN 4 (x 2) (x 1), this]
    nlinarith [mul_neg_of_pos_of_neg hom4 (F.neg 4 1 (by decide))]
  -- the front diagonal `24` over `06` at `u27`
  obtain ⟨s, t, γ, hs0, hs1, ht0, ht1, hγ0, hdiag_vec⟩ := u27_bound F hC
  have hdiag_pos : 0 < (1 - s) * (1 - t) * (⟪x 2, u27 x⟫ - ⟪x 0, u27 x⟫) +
      (1 - s) * t * (⟪x 2, u27 x⟫ - ⟪x 6, u27 x⟫) +
      s * (1 - t) * (⟪x 4, u27 x⟫ - ⟪x 0, u27 x⟫) +
      s * t * (⟪x 4, u27 x⟫ - ⟪x 6, u27 x⟫) := by
    have hinner := congrArg (fun w => ⟪w, u27 x⟫) hdiag_vec
    have hrhs : 0 < ⟪γ • u27 x, u27 x⟫ := by
      rw [real_inner_smul_left]
      exact mul_pos hγ0 (real_inner_self_pos.mpr hu_ne)
    rw [← hinner] at hrhs
    have hlhs : ⟪(x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)), u27 x⟫ =
        (1 - s) * (1 - t) * (⟪x 2, u27 x⟫ - ⟪x 0, u27 x⟫) +
        (1 - s) * t * (⟪x 2, u27 x⟫ - ⟪x 6, u27 x⟫) +
        s * (1 - t) * (⟪x 4, u27 x⟫ - ⟪x 0, u27 x⟫) +
        s * t * (⟪x 4, u27 x⟫ - ⟪x 6, u27 x⟫) := by
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
    linarith
  have hex_pos : ∃ q ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), u27 x⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), x 2 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), u27 x⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), x 2 - x 1⟫, (0 : ℝ)) := by
    by_contra hno
    push Not at hno
    have h01 : ⟪x 2, u27 x⟫ - ⟪x 0, u27 x⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h21 : ⟪x 2, u27 x⟫ - ⟪x 6, u27 x⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h03 : ⟪x 4, u27 x⟫ - ⟪x 0, u27 x⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h23 : ⟪x 4, u27 x⟫ - ⟪x 6, u27 x⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht1),
      mul_nonneg (sub_nonneg.mpr hs1) ht0, mul_nonneg hs0 (sub_nonneg.mpr ht1), mul_nonneg hs0 ht0]
  have hex_neg : ∃ p ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), u27 x⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), x 2 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), u27 x⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), x 2 - x 1⟫, (0 : ℝ)) := by
    refine ⟨(0, 1), by decide, Or.inl ?_⟩
    simp only [Matrix.cons_val]
    rw [← sub_pos, ← inner_sub_left, show x 0 - x 2 = -(x 2 - x 0) from by abel, inner_neg_left]
    linarith [hcon]
  apply hL
  refine ⟨4, inferInstance, (![0, 2, 6, 4] : ZMod 4 → Fin 7), {2, 3, 7, 8}, {0, 4, 5},
    u27 x, x 2 - x 1, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_,
    by simpa [inner_zero_right] using robUniLex_four_of_mixed hex_pos hex_neg⟩
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · exact Or.inr ⟨show ⟪F.N ⟨2, by decide⟩, u27 x⟫ = 0 from hu2, Or.inl hd2⟩
    · exact Or.inl (show 0 < ⟪F.N ⟨3, by decide⟩, u27 x⟫ from hu3)
    · exact Or.inr ⟨show ⟪F.N ⟨7, by decide⟩, u27 x⟫ = 0 from hu7, Or.inl hd7⟩
    · exact Or.inl (show 0 < ⟪F.N ⟨8, by decide⟩, u27 x⟫ from hu8)
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · exact Or.inl (by linarith [show ⟪F.N ⟨0, by decide⟩, u27 x⟫ < 0 from hu0])
    · rcases lt_or_eq_of_le (show ⟪F.N ⟨4, by decide⟩, u27 x⟫ ≤ 0 from hu4) with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, Or.inl hd4⟩
    · exact Or.inl (by linarith [show ⟪F.N ⟨5, by decide⟩, u27 x⟫ < 0 from hu5])

/-- Facet facts at `bW02` that follow from `F` alone (all but facet `8`). -/
theorem facets_w02 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 1, bW02 x⟫ ∧ 0 < ⟪F.N 3, bW02 x⟫ ∧ 0 < ⟪F.N 4, bW02 x⟫ ∧
    ⟪F.N 5, bW02 x⟫ < 0 ∧ ⟪F.N 6, bW02 x⟫ < 0 ∧ ⟪F.N 7, bW02 x⟫ < 0 := by
  have e : ∀ t : Fin 9, ⟪F.N t, bW02 x⟫ = F.f t (x 0) - F.f t (x 2) := fun t => by
    rw [F.hN t (x 0) (x 2)]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, F.zero 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]
  · rw [e, F.zero 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]
  · rw [e, F.zero 4 0 (by decide)]; linarith [F.neg 4 2 (by decide)]
  · rw [e, F.zero 5 2 (by decide)]; linarith [F.neg 5 0 (by decide)]
  · rw [e, F.zero 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]
  · rw [e, F.zero 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]

theorem a2_lam5_closed {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hA2 : Minimality.T24.Reg.A2 x F) (hOB : H24K.SAT.OB1 x)
    (hL : omega3 x < Lam5 x)
    (hc3 : oblX6 x 3 < 1) (hc53 : oblX6 x 5 < oblX6 x 3) (hLam1 : Lam5 x < 1 + omega3 x)
    (hp : oblX0 x 3 * oblX2 x 5 < oblX0 x 5 * oblX2 x 3)
    (hr : oblX0 x 3 * oblX6 x 5 ≤ oblX0 x 5 * oblX6 x 3)
    (hconv : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3))
    (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (f1523 : FrontDet (x 1) (x 5) (x 2) (x 3) (bW02 x))
    (f1526 : FrontDet (x 1) (x 5) (x 2) (x 6) (bW02 x))
    (f1326 : FrontDet (x 1) (x 3) (x 2) (x 6) (bW02 x))
    (f5613 : FrontDet (x 5) (x 6) (x 1) (x 3) (bW02 x))
    (f5623 : FrontDet (x 5) (x 6) (x 2) (x 3) (bW02 x))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bW02 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bW02 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bW02 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bW02 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bW02 x))
    (hu3 : 0 < ⟪F.N 3, u27 x⟫) (hu8 : 0 < ⟪F.N 8, u27 x⟫)
    : LexAny F ∨ SplitAny24 F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnL, hnS⟩ := hcon
  have T := type24OfFac F
  obtain ⟨h1, h3, h4, h5, h6, h7⟩ := facets_w02 F
  have z1 := z_one_w02 x
  have e5 := hrep_w02 F 5
  have e3 := hrep_w02 F 3
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ha5 : 1 < oblX0 x 5 := hA2.1
  have hom3 : 0 < omega3 x := hC.1
  -- z2 < 0 from OB1
  have hz2 : z x (bW02 x) 2 < 0 := by
    have hx : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
    have : z x (bW02 x) 2 = ⟪x 0 - x 1, x 2 - x 1⟫ - ⟪x 2 - x 1, x 2 - x 1⟫ := by
      simp only [z, bW02]
      rw [show x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) by abel, inner_sub_right, real_inner_comm]
    have hab := hOB.1
    linarith
  -- the five clauses at each view
  have P1 : (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min 0 (z x (bW02 x) 5)) ∨
      (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min 0 (z x (bW02 x) 5)) ∨
      (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min 0 (z x (bW02 x) 3)) ∨
      (max 0 (z x (bW02 x) 3) ≤ min (z x (bW02 x) 5) (z x (bW02 x) 6)) ∨
      (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 5) (z x (bW02 x) 6)) := by
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨n1, n2, n3, n4, n5⟩ := hno
    rw [← z1] at n1 n2 n3 n4
    exact hnL (lexAny_w02_ppp F h1 h3 h4 h8 h5 h6 h7 f1523 f1526 f1326 f5613 f5623
      n1 n2 n3 n4 n5)
  have P2 : (max 0 (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)) ∨
      (max 0 (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)) ∨
      (max 0 (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)) ∨
      (max (z x (bW02 x) 6) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)) ∨
      (max 0 (z x (bW02 x) 3) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5)) := by
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨n1, n2, n3, n4, n5⟩ := hno
    rw [← z1] at n1 n2 n3 n5
    exact hnL (lexAny_w02_pmm F h1 h3 h4 h8 h5 h6 h7 f0613 f0615 f0315 f0365 f6513
      n1 n2 n3 n4 n5)
  -- the final contradiction from `z5 ≥ 0`
  have hz5_false : 0 ≤ z x (bW02 x) 5 → False := by
    intro hz5
    have hu07 : 0 ≤ ⟪x 2 - x 0, u07 x⟫ := by
      have := u07_bound F hC hc3 hnL
      have e : ⟪x 2 - x 0, u07 x⟫ = omega3 x * ⟪x 2 - x 1, x 2 - x 0⟫ - (-⟪x 0 - x 1, x 2 - x 0⟫) := by
        dsimp [u07]
        rw [inner_add_right, inner_smul_right,
          real_inner_comm (x 2 - x 0) (x 0 - x 1), real_inner_comm (x 2 - x 0) (x 2 - x 1)]
        ring
      rw [e]; exact this
    have hom5 : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
      simp only [omega5]; field_simp
    exact w02_lam5_false e5 hom5 rfl hom3 hc5.le hL
      (fun h => absurd (T.inj h) (by decide)) hu07 (u27_z_bound F hC hu3 hu8 hnL) hz5
  rcases lt_trichotomy (z x (bW02 x) 6) 0 with h6n | h60 | h6p
  · -- `z6 < 0`
    have S1 : ¬ (max (z x (bW02 x) 2) (max (z x (bW02 x) 5) (z x (bW02 x) 3)) < z x (bW02 x) 6) :=
      fun hlt => hnS (splitAny_w02_ppp_e12 F h1 h3 h4 h8 h5 h6 h7 hc5 hc53 hc3 hlt h6n)
    rcases z_core_neg _ _ _ _ _ hz2 h6n P1 P2 S1 with ⟨h5', h26⟩ | hz5
    · have hs : oblX0 x 5 < oblX0 x 3 + (oblX0 x 5 * oblX2 x 3 - oblX0 x 3 * oblX2 x 5) +
          (oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5) := by
        have key : oblX0 x 3 + (oblX0 x 5 * oblX2 x 3 - oblX0 x 3 * oblX2 x 5) +
            (oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5) - oblX0 x 5 =
            oblX0 x 3 * (1 + omega3 x - Lam5 x) := by
          simp only [Lam5]; linear_combination oblX0 x 5 * Minimality.T24.M4.eq3 F
        nlinarith [mul_pos ha3 (sub_pos.mpr hLam1)]
      exact w02_cminus_empty e3 e5 ha3 (by linarith) hp hr hs hz2 h5' h26
    · exact hz5_false hz5
  · -- the tie `z6 = 0`
    by_cases hz5 : 0 ≤ z x (bW02 x) 5
    · exact hz5_false hz5
    · push Not at hz5
      have hid := w02_ident e3 e5
      rw [h60] at hid
      have hp0 : 0 < oblX0 x 5 * oblX2 x 3 - oblX0 x 3 * oblX2 x 5 := by linarith
      have hz3 : z x (bW02 x) 3 < 0 := by
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ oblX0 x 5) hc, mul_pos ha3 (neg_pos.mpr hz5),
          mul_pos hp0 (neg_pos.mpr hz2)]
      have hCB : 0 < ⟪x 1 - x 6, x 0 - x 6⟫ := by
        have hx : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
          real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
        have : ⟪x 1 - x 6, x 0 - x 6⟫ = ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ := by
          rw [show x 1 - x 6 = -(x 6 - x 1) by abel, show x 0 - x 6 = (x 0 - x 1) - (x 6 - x 1) by abel,
            inner_neg_left, inner_sub_right, real_inner_comm (x 6 - x 1) (x 0 - x 1)]
          ring
        have := hOB.2.1
        linarith
      exact hnS (splitAny_w02_ppp_e12_tilt F h1 h3 h4 h8 h5 h6 h7 hc5 hc53 hc3
        (by rw [h60]; exact max_lt hz2 (max_lt hz5 hz3)) h60.le hCB)
  · -- `0 < z6`
    have S2 : ¬ (max (z x (bW02 x) 2) (max (z x (bW02 x) 5) (z x (bW02 x) 3)) < 0) :=
      fun hlt => hnS (splitAny_w02_ppp_e36 F h1 h3 h4 h8 h5 h6 h7 hc5 hc3 (by linarith)
        (by linarith) hconv hlt h6p)
    exact hz5_false (z_core_pos _ _ _ _ _ hz2 h6p P1 P2 S2)

end Minimality.T24.A20
