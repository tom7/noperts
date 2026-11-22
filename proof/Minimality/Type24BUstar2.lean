module

public import Minimality.M4dType24
public import Minimality.Type24BUstar
public import Minimality.GenQuad
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Type 24, region B: R3 (`U**`-Split)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Sym Minimality.T24.A8

private theorem det3_frame24' (x : Fin 7 → ℝ³) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    det3 (a0 • (x 0 - x 1) + a1 • (x 2 - x 1) + a2 • (x 6 - x 1))
         (b0 • (x 0 - x 1) + b1 • (x 2 - x 1) + b2 • (x 6 - x 1))
         (c0 • (x 0 - x 1) + c1 • (x 2 - x 1) + c2 • (x 6 - x 1)) =
      (a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) *
        det24 x := by
  simpa [det24] using Minimality.det3_comb (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) a0 a1 a2 b0 b1 b2 c0 c1 c2



/-- `c5 u**` , `u** = (-a4, a4 + om5 (1 - c4), 1 - c4)` in the oblique frame. -/
noncomputable def ustar2 (x : Fin 7 → ℝ³) : ℝ³ :=
  (-Dl4 x) • (x 2 - x 0) + (1 - oblX6 x 4) • (x 5 - x 0)


/-- `Q = (a3 - a5)(1 - c4) + a4 (c3 - c5)`: the 2D cross product of `x5 - x3` and `x4 - x6`
projected along `x2 - x1`. -/
noncomputable def Qu2 (x : Fin 7 → ℝ³) : ℝ :=
  (oblX0 x 3 - oblX0 x 5) * (1 - oblX6 x 4) + oblX0 x 4 * (oblX6 x 3 - oblX6 x 5)

theorem ustar2_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 ≤ 1) (hc4 : oblX6 x 4 < 1) (hD4 : Dl4 x < 0) :
    ⟪F.N 0, ustar2 x⟫ < 0 ∧ ⟪F.N 1, ustar2 x⟫ < 0 ∧ ⟪F.N 2, ustar2 x⟫ = 0 ∧
    ⟪F.N 3, ustar2 x⟫ < 0 ∧ ⟪F.N 4, ustar2 x⟫ < 0 ∧ 0 < ⟪F.N 5, ustar2 x⟫ ∧
    0 < ⟪F.N 6, ustar2 x⟫ ∧ 0 < ⟪F.N 7, ustar2 x⟫ := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hD4_pos : 0 < -Dl4 x := neg_pos.mpr hD4
  have hc4_pos : 0 < 1 - oblX6 x 4 := sub_pos.mpr hc4
  have hL_pos : 0 < Lam5 x := by dsimp [Lam5]; nlinarith
  have hus : ∀ t : Fin 9, ⟪F.N t, ustar2 x⟫ =
      (-Dl4 x) * (F.f t (x 2) - F.f t (x 0)) + (1 - oblX6 x 4) * (F.f t (x 5) - F.f t (x 0)) := by
    intro t; dsimp [ustar2]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← F.hN t (x 2) (x 0), ← F.hN t (x 5) (x 0)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hus 0, F.zero 0 2 (by decide), F.zero 0 0 (by decide), sub_self, mul_zero, zero_add, sub_zero]
    exact mul_neg_of_pos_of_neg hc4_pos (F.neg 0 5 (by decide))
  · rw [hus 1, F.zero 1 0 (by decide), sub_zero, sub_zero]
    have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
    have h15 : F.f 1 (x 5) < 0 := F.neg 1 5 (by decide)
    nlinarith
  · rw [hus 2, F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide), sub_self]
    ring
  · rw [hus 3, F.zero 3 0 (by decide), F.zero 3 5 (by decide), sub_self, mul_zero, add_zero, sub_zero]
    exact mul_neg_of_pos_of_neg hD4_pos (F.neg 3 2 (by decide))
  · rw [hus 4, F.zero 4 0 (by decide), sub_zero, sub_zero]
    have h42 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
    have h45 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
    nlinarith
  · rw [hus 5]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    have h52 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
    have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    have h55 : F.f 5 (x 5) - F.f 5 (x 0) = (oblX0 x 5 - 1) * F.f 5 (x 0) := by
      rw [ev5]; ring
    rw [h52, zero_sub, h55]
    have t1 : 0 < (-Dl4 x) * (-F.f 5 (x 0)) := mul_pos hD4_pos (neg_pos.mpr h50)
    have t2 : 0 ≤ (1 - oblX6 x 4) * ((oblX0 x 5 - 1) * F.f 5 (x 0)) :=
      mul_nonneg hc4_pos.le (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ha5) h50.le)
    linarith
  · rw [hus 6, F.zero 6 2 (by decide), F.zero 6 5 (by decide), zero_sub]
    have h60 : 0 < -F.f 6 (x 0) := by linarith [F.neg 6 0 (by decide)]
    linarith [mul_pos hD4_pos h60, mul_pos hc4_pos h60]
  · rw [hus 7, F.zero 7 2 (by decide), zero_sub]
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have hdiff : F.f 7 (x 5) - (1 + omega3 x) * F.f 7 (x 1) = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [Lam5]; rw [ev7_5]; ring
    rw [hf7_0, hdiff]
    have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
    have t1 : 0 < (-Dl4 x) * -((1 + omega3 x) * F.f 7 (x 1)) := by
      have : -((1 + omega3 x) * F.f 7 (x 1)) = (1 + omega3 x) * (-F.f 7 (x 1)) := by ring
      rw [this]; exact mul_pos hD4_pos (mul_pos (by linarith) h71)
    have t2 : 0 < (1 - oblX6 x 4) * ((-F.f 7 (x 1)) * Lam5 x) :=
      mul_pos hc4_pos (mul_pos h71 hL_pos)
    linarith


theorem nu346_ustar2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc4 : oblX6 x 4 < 1)
    (hΔ : 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) :
    ∃ k : ℝ, 0 < k ∧ ⟪F.N 8, ustar2 x⟫ = k * nu346b x := by
  have T := type24OfFac F
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc4_pos : 0 < 1 - oblX6 x 4 := sub_pos.mpr hc4
  have e5 := T.eq5
  have hg : 0 < -F.f 8 (x 1) := by linarith [F.neg 8 1 (by decide)]
  have z3 := fac_eval F 8 3
  have z4 := fac_eval F 8 4
  have z6 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
  have f3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have f4 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have z5 := fac_eval F 8 5
  rw [z6] at z3 z4 z5
  rw [f3] at z3
  rw [f4] at z4
  have hus : ⟪F.N 8, ustar2 x⟫ =
      (-Dl4 x) * (F.f 8 (x 2) - F.f 8 (x 0)) + (1 - oblX6 x 4) * (F.f 8 (x 5) - F.f 8 (x 0)) := by
    dsimp [ustar2]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← F.hN 8 (x 2) (x 0),
      ← F.hN 8 (x 5) (x 0)]
  have hM : 0 < (oblX0 x 4 + oblX2 x 4) * oblX6 x 5 + (oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 4) := by
    have : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith
    rw [this]; nlinarith [mul_pos hom5 hc5, mul_pos (mul_pos hom5 hc5) hc4_pos, mul_pos ha4 hc5, mul_pos hb4 hc5]
  refine ⟨(-F.f 8 (x 1)) * ((oblX0 x 4 + oblX2 x 4) * oblX6 x 5 +
      (oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 4)) /
      (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4), by positivity, ?_⟩
  have hE3 : oblX0 x 3 * (F.f 8 (x 0) - F.f 8 (x 1)) + oblX2 x 3 * (F.f 8 (x 2) - F.f 8 (x 1)) =
      (-F.f 8 (x 1)) * (1 - oblX6 x 3) := by linarith
  have hE4 : oblX0 x 4 * (F.f 8 (x 0) - F.f 8 (x 1)) + oblX2 x 4 * (F.f 8 (x 2) - F.f 8 (x 1)) =
      (-F.f 8 (x 1)) * (1 - oblX6 x 4) := by linarith
  rw [hus, z5, div_mul_eq_mul_div, eq_div_iff hΔ.ne']
  simp only [Dl4, nu346b]
  linear_combination
    (-((-(oblX0 x 4 * oblX6 x 5)) * oblX2 x 4 -
      (-((1 - oblX6 x 4) * (1 - oblX0 x 5) - oblX0 x 4 * oblX6 x 5) + (1 - oblX6 x 4) * oblX2 x 5) *
        oblX0 x 4)) * hE3 +
    (-((-((1 - oblX6 x 4) * (1 - oblX0 x 5) - oblX0 x 4 * oblX6 x 5) + (1 - oblX6 x 4) * oblX2 x 5) *
        oblX0 x 3 - (-(oblX0 x 4 * oblX6 x 5)) * oblX2 x 3)) * hE4

theorem splitAny24_Ustar2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 ≤ 1) (hc4 : oblX6 x 4 < 1) (hD4 : Dl4 x < 0)
    (hΔ : 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4)
    (hnu : 0 < nu346b x) (hQ : 0 < Qu2 x)
    (hz : max 0 ⟪x 6 - x 1, ustar2 x⟫ <
      min ⟪x 2 - x 1, ustar2 x⟫ (min ⟪x 4 - x 1, ustar2 x⟫
        (min ⟪x 3 - x 1, ustar2 x⟫ ⟪x 5 - x 1, ustar2 x⟫))) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have ha5_pos : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc4_pos : 0 < 1 - oblX6 x 4 := sub_pos.mpr hc4
  have hfac := ustar2_facings F hC ha5 hc4 hD4
  obtain ⟨k, hk, hk8⟩ := nu346_ustar2 F hC hc4 hΔ
  have h8 : 0 < ⟪F.N 8, ustar2 x⟫ := by rw [hk8]; exact mul_pos hk hnu
  have e5 := eq5 F
  have hMp : 0 < oblX6 x 5 * (oblX0 x 4 + oblX2 x 4) +
      (oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 4) := by
    have : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith
    rw [this]; nlinarith [mul_pos hom5 hc5, mul_pos (mul_pos hom5 hc5) hc4_pos, mul_pos ha4 hc5,
      mul_pos hb4 hc5]
  have hd2_0 : ⟪F.N 2, dstar x⟫ < 0 := by
    dsimp [dstar]
    rw [inner_sub_right, inner_smul_right, ← F.hN 2 (x 2) (x 0), ← F.hN 2 (x 0) (x 1)]
    have h22 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
    have h20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
    have h21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    linarith
  let c : ZMod 6 → Fin 7 := ![1, 6, 4, 3, 5, 2]
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  let pat : Fin 9 → Bool := fun t => decide (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hcyc : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  have hlex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, ustar2 x⟫ else -⟪F.N t, ustar2 x⟫)
              (if pat t then ⟪F.N t, dstar x⟫ else -⟪F.N t, dstar x⟫)
              (if pat t then ⟪F.N t, x 6 - x 1⟫ else -⟪F.N t, x 6 - x 1⟫) := by
    intro t; fin_cases t
    · exact Or.inl (by simp [pat]; linarith [hfac.1])
    · exact Or.inl (by simp [pat]; linarith [hfac.2.1])
    · exact Or.inr ⟨by simp [pat, hfac.2.2.1], Or.inl (by simp [pat]; linarith [hd2_0])⟩
    · exact Or.inl (by simp [pat]; linarith [hfac.2.2.2.1])
    · exact Or.inl (by simp [pat]; linarith [hfac.2.2.2.2.1])
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.1)
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.2.1)
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.2.2)
    · exact Or.inl (by simp [pat]; exact h8)
  have hzp : ∀ w : ℝ, max 0 ⟪x 6 - x 1, ustar2 x⟫ < w → 0 < w ∧ ⟪x 6 - x 1, ustar2 x⟫ < w :=
    fun w h => ⟨lt_of_le_of_lt (le_max_left _ _) h, lt_of_le_of_lt (le_max_right _ _) h⟩
  have hz2 := hzp _ (lt_of_lt_of_le hz (min_le_left _ _))
  have hz4 := hzp _ (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hz3 := hzp _ (lt_of_lt_of_le hz
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hz5 := hzp _ (lt_of_lt_of_le hz
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hus_rep : ustar2 x = (Dl4 x - (1 - oblX6 x 4) * (1 - oblX0 x 5)) • (x 0 - x 1) +
      (-Dl4 x + (1 - oblX6 x 4) * oblX2 x 5) • (x 2 - x 1) +
      ((1 - oblX6 x 4) * oblX6 x 5) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by module, hrep 5]; module
    dsimp [ustar2]; rw [h20, h50]; module
  have hd_rep : dstar x = (-3 : ℝ) • (x 0 - x 1) + (2 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    dsimp [dstar]; rw [h20]; module
  have hdet_sq : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  -- edge forms in the frame
  have fE61 : x 6 - x 1 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by module
  have fE12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
  have fE46 : x 4 - x 6 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      (oblX6 x 4 - 1) • (x 6 - x 1) := by
    rw [show x 4 - x 6 = (x 4 - x 1) - (x 6 - x 1) by module, hrep 4]; module
  have fE34 : x 3 - x 4 = (oblX0 x 3 - oblX0 x 4) • (x 0 - x 1) + (oblX2 x 3 - oblX2 x 4) • (x 2 - x 1) +
      (oblX6 x 3 - oblX6 x 4) • (x 6 - x 1) := by
    rw [show x 3 - x 4 = (x 3 - x 1) - (x 4 - x 1) by module, hrep 3, hrep 4]; module
  have fE53 : x 5 - x 3 = (oblX0 x 5 - oblX0 x 3) • (x 0 - x 1) + (oblX2 x 5 - oblX2 x 3) • (x 2 - x 1) +
      (oblX6 x 5 - oblX6 x 3) • (x 6 - x 1) := by
    rw [show x 5 - x 3 = (x 5 - x 1) - (x 3 - x 1) by module, hrep 5, hrep 3]; module
  have fE25 : x 2 - x 5 = (-oblX0 x 5) • (x 0 - x 1) + (1 - oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 2 - x 5 = (x 2 - x 1) - (x 5 - x 1) by module, hrep 5]; module
  have hKd : 0 < 3 * (1 - oblX6 x 4) := by positivity
  have hK0 : 0 < oblX0 x 4 * oblX6 x 5 := mul_pos ha4 hc5
  have hKnu : 0 < oblX6 x 5 * nu346b x := mul_pos hc5 hnu
  have hKQ : 0 < oblX6 x 5 * Qu2 x := mul_pos hc5 hQ
  have hKD : 0 < oblX6 x 5 * (oblX0 x 5 * (1 - oblX6 x 4) + oblX0 x 4 * oblX6 x 5) :=
    mul_pos hc5 (add_pos (mul_pos ha5_pos hc4_pos) (mul_pos ha4 hc5))
  have hLn : ∀ (p q r : ℝ), p < 0 → LexPos3 (-1 * p) (-1 * q) (-1 * r) := fun p q r h => Or.inl (by linarith)
  have hL1 : ∀ (p q r : ℝ), 0 < p → LexPos3 (1 * p) (1 * q) (1 * r) := fun p q r h => Or.inl (by linarith)
  by_cases hz6_gt : LexPos3 ⟪x 6 - x 1, ustar2 x⟫ ⟪x 6 - x 1, dstar x⟫ ⟪x 6 - x 1, x 6 - x 1⟫
  · refine Minimality.T24.A8.splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc
      (ustar2 x) (dstar x) (x 6 - x 1) hlex 5 1 (by decide) (by decide) (det24 x) ?_
    intro i hia j hj hjc
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact absurd rfl hia
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have hj0 : j = 0 := by
        rcases hj with rfl | rfl
        · rfl
        · exact absurd rfl hjc
      subst hj0
      refine ⟨-1, ?_, Or.inl ?_⟩
      · show LexPos3 (-1 * ⟪x 1 - x 6, ustar2 x⟫) (-1 * ⟪x 1 - x 6, dstar x⟫) (-1 * ⟪x 1 - x 6, x 6 - x 1⟫)
        have h16 : x 1 - x 6 = -(x 6 - x 1) := by module
        rw [h16, inner_neg_left, inner_neg_left, inner_neg_left]
        simp only [neg_one_mul, neg_neg]
        exact hz6_gt
      · show 0 < det24 x * -1 * det3 (x 6 - x 1) (x 1 - x 2) (ustar2 x)
        rw [fE61, fE12, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hK0 hdet_sq) ?_
        simp only [Dl4]; ring
    · have hj2 : j = 2 := by
        rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · rfl
      subst hj2
      refine ⟨1, Or.inl (by
        show 0 < 1 * ⟪x (c 2) - x (c 1), ustar2 x⟫
        rw [one_mul]; change 0 < ⟪x 4 - x 6, ustar2 x⟫
        rw [show x 4 - x 6 = (x 4 - x 1) - (x 6 - x 1) by module, inner_sub_left]
        exact sub_pos.mpr hz4.2), Or.inr ⟨?_, Or.inl ?_⟩⟩
      · show det24 x * 1 * det3 (x 4 - x 6) (x 1 - x 2) (ustar2 x) = 0
        rw [fE46, fE12, hus_rep, det3_frame24']
        simp only [Dl4]; ring
      · show 0 < det24 x * 1 * det3 (x 4 - x 6) (x 1 - x 2) (dstar x)
        rw [fE46, fE12, hd_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hKd hdet_sq) ?_
        ring
    · have hj23 : j = 2 ∨ j = 3 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj23 with rfl | rfl
        · apply hL1
          show 0 < ⟪x 4 - x 6, ustar2 x⟫
          rw [show x 4 - x 6 = (x 4 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz4.2
        · apply hL1
          show 0 < ⟪x 3 - x 6, ustar2 x⟫
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz3.2
      · show 0 < det24 x * 1 * det3 (x 3 - x 4) (x 1 - x 2) (ustar2 x)
        rw [fE34, fE12, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hKnu hdet_sq) ?_
        simp only [Dl4, nu346b]; ring
    · have hj34 : j = 3 ∨ j = 4 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj34 with rfl | rfl
        · apply hL1
          show 0 < ⟪x 3 - x 6, ustar2 x⟫
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz3.2
        · apply hL1
          show 0 < ⟪x 5 - x 6, ustar2 x⟫
          rw [show x 5 - x 6 = (x 5 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz5.2
      · show 0 < det24 x * 1 * det3 (x 5 - x 3) (x 1 - x 2) (ustar2 x)
        rw [fE53, fE12, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hKQ hdet_sq) ?_
        simp only [Dl4, Qu2]; ring
    · have hj45 : j = 4 ∨ j = 5 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj45 with rfl | rfl
        · apply hL1
          show 0 < ⟪x 5 - x 6, ustar2 x⟫
          rw [show x 5 - x 6 = (x 5 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz5.2
        · apply hL1
          show 0 < ⟪x 2 - x 6, ustar2 x⟫
          rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by module, inner_sub_left]
          exact sub_pos.mpr hz2.2
      · show 0 < det24 x * 1 * det3 (x 2 - x 5) (x 1 - x 2) (ustar2 x)
        rw [fE25, fE12, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hKD hdet_sq) ?_
        simp only [Dl4]; ring
  · have hz6_lt : LexPos3 (-⟪x 6 - x 1, ustar2 x⟫) (-⟪x 6 - x 1, dstar x⟫) (-⟪x 6 - x 1, x 6 - x 1⟫) := by
      have h61_ne : x 6 - x 1 ≠ 0 := by
        intro h
        have h0 : ⟪F.N 0, x 6 - x 1⟫ = 0 := by rw [h, inner_zero_right]
        rw [← F.hN 0 (x 6) (x 1), F.zero 0 1 (by decide), sub_zero] at h0
        exact (F.neg 0 6 (by decide)).ne h0
      rcases lt_trichotomy ⟪x 6 - x 1, ustar2 x⟫ 0 with hlt | heq | hgt
      · exact Or.inl (neg_pos.mpr hlt)
      · rw [heq, neg_zero]
        rcases lt_trichotomy ⟪x 6 - x 1, dstar x⟫ 0 with hdlt | hdeq | hdgt
        · exact Or.inr ⟨rfl, Or.inl (neg_pos.mpr hdlt)⟩
        · exfalso; apply hz6_gt
          rw [heq, hdeq]
          exact Or.inr ⟨rfl, Or.inr ⟨rfl, real_inner_self_pos.mpr h61_ne⟩⟩
        · exfalso; apply hz6_gt
          rw [heq]; exact Or.inr ⟨rfl, Or.inl hdgt⟩
      · exfalso; exact hz6_gt (Or.inl hgt)
    refine Minimality.T24.A8.splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc
      (ustar2 x) (dstar x) (x 6 - x 1) hlex 1 0 (by decide) (by decide) (-det24 x) ?_
    intro i hia j hj hjc
    have hi : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      fin_cases i
      · exact Or.inl rfl
      · exact absurd rfl hia
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have hj1 : j = 1 := by
        rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · rfl
      subst hj1
      refine ⟨-1, ?_, Or.inl ?_⟩
      · change LexPos3 (-1 * ⟪x 6 - x 1, ustar2 x⟫) (-1 * ⟪x 6 - x 1, dstar x⟫) (-1 * ⟪x 6 - x 1, x 6 - x 1⟫)
        simp only [neg_one_mul]
        exact hz6_lt
      · show 0 < -det24 x * -1 * det3 (x 6 - x 1) (x 4 - x 6) (ustar2 x)
        rw [fE61, fE46, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos (mul_pos hMp ha4) hdet_sq) ?_
        simp only [Dl4]; ring
    · have hj23 : j = 2 ∨ j = 3 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj23 with rfl | rfl
        · apply hL1; exact hz4.1
        · apply hL1; exact hz3.1
      · show 0 < -det24 x * 1 * det3 (x 3 - x 4) (x 4 - x 6) (ustar2 x)
        rw [fE34, fE46, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos (mul_pos hMp hnu) hdet_sq) ?_
        simp only [Dl4, nu346b]; ring
    · have hj34 : j = 3 ∨ j = 4 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj34 with rfl | rfl
        · apply hL1; exact hz3.1
        · apply hL1; exact hz5.1
      · show 0 < -det24 x * 1 * det3 (x 5 - x 3) (x 4 - x 6) (ustar2 x)
        rw [fE53, fE46, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos (mul_pos hMp hQ) hdet_sq) ?_
        simp only [Dl4, Qu2]; ring
    · have hj45 : j = 4 ∨ j = 5 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, ?_, Or.inl ?_⟩
      · rcases hj45 with rfl | rfl
        · apply hL1; exact hz5.1
        · apply hL1; exact hz2.1
      · show 0 < -det24 x * 1 * det3 (x 2 - x 5) (x 4 - x 6) (ustar2 x)
        rw [fE25, fE46, hus_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos (mul_pos hMp
          (add_pos (mul_pos ha5_pos hc4_pos) (mul_pos ha4 hc5))) hdet_sq) ?_
        simp only [Dl4]; ring
    · have hj5 : j = 5 := by
        rcases hj with rfl | rfl
        · rfl
        · exact absurd rfl hjc
      subst hj5
      refine ⟨1, ?_, Or.inr ⟨?_, Or.inl ?_⟩⟩
      · apply hL1; exact hz2.1
      · show -det24 x * 1 * det3 (x 1 - x 2) (x 4 - x 6) (ustar2 x) = 0
        rw [fE12, fE46, hus_rep, det3_frame24']
        simp only [Dl4]; ring
      · show 0 < -det24 x * 1 * det3 (x 1 - x 2) (x 4 - x 6) (dstar x)
        rw [fE12, fE46, hd_rep, det3_frame24']
        refine lt_of_lt_of_eq (mul_pos hKd hdet_sq) ?_
        ring

/-- `clause_of_gt`: a quartet clause holds when some peak has a smaller `b`-value than some valley. -/
theorem clause_of_gt' {p q r s b d1 d2 : ℝ³}
    (h : ⟪r, b⟫ < ⟪p, b⟫ ∨ ⟪r, b⟫ < ⟪q, b⟫ ∨ ⟪s, b⟫ < ⟪p, b⟫ ∨ ⟪s, b⟫ < ⟪q, b⟫) :
    Minimality.GenQuad.LexClause p q r s b d1 d2 := by
  apply Minimality.GenQuad.lexClause_of_notM
  rintro ⟨h1, h2, h3, h4⟩
  rcases h with h | h | h | h <;> linarith

/-- `z0(u**) <= 0` under the two OB1 face-angle conditions at vertex 1. -/
theorem ustar2_z0_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hD4 : Dl4 x < 0)
    (hc4 : oblX6 x 4 < 1)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) :
    ⟪x 0 - x 1, ustar2 x⟫ ≤ 0 := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc4_pos : 0 < 1 - oblX6 x 4 := sub_pos.mpr hc4
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hus_rep : ustar2 x = (Dl4 x - (1 - oblX6 x 4) * (1 - oblX0 x 5)) • (x 0 - x 1) +
      (-Dl4 x + (1 - oblX6 x 4) * oblX2 x 5) • (x 2 - x 1) +
      ((1 - oblX6 x 4) * oblX6 x 5) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by module, hrep 5]; module
    dsimp [ustar2]; rw [h20, h50]; module
  have hA0 : Dl4 x - (1 - oblX6 x 4) * (1 - oblX0 x 5) = -(oblX0 x 4 * oblX6 x 5) := by
    dsimp [Dl4]; ring
  have hA0n : Dl4 x - (1 - oblX6 x 4) * (1 - oblX0 x 5) ≤ 0 := by
    rw [hA0]; nlinarith [mul_pos ha4 hc5]
  have hA2 : 0 ≤ -Dl4 x + (1 - oblX6 x 4) * oblX2 x 5 := by
    nlinarith [mul_pos hc4_pos hb5]
  have hA6 : 0 ≤ (1 - oblX6 x 4) * oblX6 x 5 := (mul_pos hc4_pos hc5).le
  rw [hus_rep]
  exact Minimality.GenQuad.obtuse_frame hab hac hA0n hA2 hA6

set_option maxHeartbeats 4000000 in
theorem ustar2_collapse {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 ≤ 1) (hc4 : oblX6 x 4 < 1) (hD4 : Dl4 x < 0)
    (hΔ : 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4)
    (hnu : 0 < nu346b x) (hQ : 0 < Qu2 x)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hz : max 0 ⟪x 6 - x 1, ustar2 x⟫ <
      min ⟪x 4 - x 1, ustar2 x⟫ (min ⟪x 3 - x 1, ustar2 x⟫ ⟪x 5 - x 1, ustar2 x⟫)) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  have T := type24OfFac F
  have ha5p : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  by_cases h2 : max 0 ⟪x 6 - x 1, ustar2 x⟫ < ⟪x 2 - x 1, ustar2 x⟫
  · exact Or.inr (splitAny24_Ustar2 F hC ha5 hc4 hD4 hΔ hnu hQ (lt_min h2 hz))
  left
  push Not at h2
  have hz0 := ustar2_z0_nonpos F hD4 hc4 hab hac
  have hz4 : max 0 ⟪x 6 - x 1, ustar2 x⟫ < ⟪x 4 - x 1, ustar2 x⟫ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz3 : max 0 ⟪x 6 - x 1, ustar2 x⟫ < ⟪x 3 - x 1, ustar2 x⟫ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hz5 : max 0 ⟪x 6 - x 1, ustar2 x⟫ < ⟪x 5 - x 1, ustar2 x⟫ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hz5e : ⟪x 5 - x 1, ustar2 x⟫ = oblX0 x 5 * ⟪x 0 - x 1, ustar2 x⟫ +
      oblX2 x 5 * ⟪x 2 - x 1, ustar2 x⟫ + oblX6 x 5 * ⟪x 6 - x 1, ustar2 x⟫ := by
    rw [hrep 5, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp
  have hz6 : 0 < ⟪x 6 - x 1, ustar2 x⟫ := by
    by_contra hn
    push Not at hn
    have hm : max 0 ⟪x 6 - x 1, ustar2 x⟫ = 0 := max_eq_left hn
    rw [hm] at h2 hz5
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha5p.le hz0,
      mul_nonpos_of_nonneg_of_nonpos hb5.le h2, mul_nonpos_of_nonneg_of_nonpos hc5.le hn]
  have hm : max 0 ⟪x 6 - x 1, ustar2 x⟫ = ⟪x 6 - x 1, ustar2 x⟫ := max_eq_right hz6.le
  rw [hm] at h2 hz4 hz3 hz5
  have hfac := ustar2_facings F hC ha5 hc4 hD4
  obtain ⟨k, hk, hk8⟩ := nu346_ustar2 F hC hc4 hΔ
  have h8 : 0 < ⟪F.N 8, ustar2 x⟫ := by rw [hk8]; exact mul_pos hk hnu
  have hd2_0 : ⟪F.N 2, dstar x⟫ < 0 := by
    dsimp [dstar]
    rw [inner_sub_right, inner_smul_right, ← F.hN 2 (x 2) (x 0), ← F.hN 2 (x 0) (x 1)]
    have h22 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
    have h20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
    have h21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    linarith
  let c : ZMod 6 → Fin 7 := ![1, 6, 4, 3, 5, 2]
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc : S0xCycUD s0x_S24 c ({5, 6, 7, 8} : Finset (Fin 9)) ({0, 1, 2, 3, 4} : Finset (Fin 9)) := by
    unfold S0xCycUD; decide
  have hU : ∀ t ∈ ({5, 6, 7, 8} : Finset (Fin 9)),
      LexPos3 ⟪F.N t, ustar2 x⟫ ⟪F.N t, dstar x⟫ ⟪F.N t, x 6 - x 1⟫ := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl hfac.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2
    · exact Or.inl h8
  have hD' : ∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)),
      LexPos3 (-⟪F.N t, ustar2 x⟫) (-⟪F.N t, dstar x⟫) (-⟪F.N t, x 6 - x 1⟫) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith [hfac.1])
    · exact Or.inl (by linarith [hfac.2.1])
    · exact Or.inr ⟨by simp [hfac.2.2.1], Or.inl (by linarith [hd2_0])⟩
    · exact Or.inl (by linarith [hfac.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.1])
  have w6 : ⟪x 6, ustar2 x⟫ = ⟪x 1, ustar2 x⟫ + ⟪x 6 - x 1, ustar2 x⟫ := by
    rw [inner_sub_left]; ring
  have w4 : ⟪x 4, ustar2 x⟫ = ⟪x 1, ustar2 x⟫ + ⟪x 4 - x 1, ustar2 x⟫ := by
    rw [inner_sub_left]; ring
  have w3 : ⟪x 3, ustar2 x⟫ = ⟪x 1, ustar2 x⟫ + ⟪x 3 - x 1, ustar2 x⟫ := by
    rw [inner_sub_left]; ring
  have w5 : ⟪x 5, ustar2 x⟫ = ⟪x 1, ustar2 x⟫ + ⟪x 5 - x 1, ustar2 x⟫ := by
    rw [inner_sub_left]; ring
  have w2 : ⟪x 2, ustar2 x⟫ = ⟪x 1, ustar2 x⟫ + ⟪x 2 - x 1, ustar2 x⟫ := by
    rw [inner_sub_left]; ring
  have cl : ∀ (i j k l : Fin 7),
      (⟪x i, ustar2 x⟫ < ⟪x k, ustar2 x⟫ ∨ ⟪x i, ustar2 x⟫ < ⟪x l, ustar2 x⟫ ∨
        ⟪x j, ustar2 x⟫ < ⟪x k, ustar2 x⟫ ∨ ⟪x j, ustar2 x⟫ < ⟪x l, ustar2 x⟫) →
      Minimality.GenQuad.LexClause (x k) (x l) (x i) (x j) (ustar2 x) (dstar x) (x 6 - x 1) :=
    fun i j k l h => clause_of_gt' h
  obtain ⟨s, t, hs, ht, hst, hM⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hz3m : ⟪x 3 - x 1, ustar2 x⟫ = (1 - s - t) * ⟪x 0 - x 1, ustar2 x⟫ +
      s * ⟪x 4 - x 1, ustar2 x⟫ + t * ⟪x 5 - x 1, ustar2 x⟫ := by
    have e : x 3 - x 1 = (x 0 - x 1) + s • ((x 4 - x 1) - (x 0 - x 1)) +
        t • ((x 5 - x 1) - (x 0 - x 1)) := by
      rw [show x 3 - x 1 = (x 0 - x 1) + (x 3 - x 0) by module, hM]; module
    rw [e]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    ring
  have hlt : ⟪x 4, ustar2 x⟫ < ⟪x 3, ustar2 x⟫ ∨ ⟪x 5, ustar2 x⟫ < ⟪x 3, ustar2 x⟫ := by
    by_contra hn
    push Not at hn
    obtain ⟨h4, h5⟩ := hn
    have h4'' : 0 ≤ ⟪x 4 - x 1, ustar2 x⟫ - ⟪x 3 - x 1, ustar2 x⟫ := by linarith
    have h5'' : 0 ≤ ⟪x 5 - x 1, ustar2 x⟫ - ⟪x 3 - x 1, ustar2 x⟫ := by linarith
    have hd : 0 < ⟪x 3 - x 1, ustar2 x⟫ - ⟪x 0 - x 1, ustar2 x⟫ := by linarith
    nlinarith [mul_nonneg hs.le h4'', mul_nonneg ht.le h5'', mul_pos (sub_pos.2 hst) hd]
  refine Minimality.GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) hc_inj hcyc
    (ustar2 x) (dstar x) (x 6 - x 1) hU hD' ?_
  refine Minimality.GenQuad.clauses_six (p := fun i => x (c i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp only [c, Matrix.cons_val]
    rcases hlt with hlt | hlt <;>
    first
      | exact cl _ _ _ _ (by first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith))

end Minimality.T24.A10
