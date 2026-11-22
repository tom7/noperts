module

public import Minimality.Type24A2Lam

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality.GenQuad (FrontDet)

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10
  Minimality.T24.A8 Minimality.T24.Q24 Minimality.T24 Minimality.T24.A15

/-- S1: the NoA identity. -/
theorem w02_u27_noA {x : Fin 7 → ℝ³} {a5 b5 c5 : ℝ}
    (h5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1))
    (hom5 : c5 * omega5 x = a5 + b5 - 1)
    (hLam : Lam5 x = b5 + c5 + omega3 x * (1 - a5)) :
    (omega5 x + 1) * z x (bW02 x) 5 + (1 + omega3 x - Lam5 x) * z x (bW02 x) 6 +
        a5 * ⟪x 2 - x 0, u27 x⟫ =
      (omega5 x * (omega3 x - Lam5 x) - 1) * (-(z x (bW02 x) 2)) := by
  have hb : x 2 - x 0 = -bW02 x := by simp [bW02]
  rw [hb, inner_neg_left]
  have e5 : z x (bW02 x) 5 = a5 * ⟪bW02 x, x 0 - x 1⟫ + b5 * ⟪bW02 x, x 2 - x 1⟫ +
      c5 * ⟪bW02 x, x 6 - x 1⟫ := by
    simp only [z]
    rw [real_inner_comm, h5]
    simp only [inner_add_right, real_inner_smul_right]
  have e2 : z x (bW02 x) 2 = ⟪bW02 x, x 2 - x 1⟫ := by simp only [z]; rw [real_inner_comm]
  have e6 : z x (bW02 x) 6 = ⟪bW02 x, x 6 - x 1⟫ := by simp only [z]; rw [real_inner_comm]
  have e27 : ⟪bW02 x, u27 x⟫ = (1 + omega5 x) * ⟪bW02 x, x 0 - x 1⟫ +
      (omega3 x * omega5 x - 1) * ⟪bW02 x, x 2 - x 1⟫ + (1 + omega3 x) * ⟪bW02 x, x 6 - x 1⟫ := by
    simp only [u27, inner_add_right, real_inner_smul_right]
  rw [e27, e5, e2, e6]
  have hb5 : b5 = c5 * omega5 x - a5 + 1 := by linarith
  rw [hLam, hb5]
  ring

theorem z_core_neg_z3 (z0 z3 z5 z6 : ℝ) (h6 : z6 < 0) (h5 : 0 ≤ z5)
    (P2 : (max 0 z3 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z6) ∨ (max 0 z5 ≤ min z0 z3) ∨
      (max z6 z5 ≤ min z0 z3) ∨ (max 0 z3 ≤ min z6 z5)) :
    z5 ≤ z3 ∧ 0 ≤ z3 := by
  simp only [max_le_iff, le_min_iff] at P2
  rcases P2 with ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ | ⟨⟨a1,a2⟩,a3,a4⟩ <;>
    constructor <;> linarith

theorem w02_neg_false {x : Fin 7 → ℝ³} {a3 b3 c3 a5 b5 c5 : ℝ}
    (h3 : x 3 - x 1 = a3 • (x 0 - x 1) + b3 • (x 2 - x 1) + c3 • (x 6 - x 1))
    (h5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1))
    (ha3 : 0 < a3) (hp : a3 * b5 < a5 * b3) (hr : a3 * c5 ≤ a5 * c3) (ha35 : a3 ≤ a5)
    (hz2 : z x (bW02 x) 2 < 0) (h6 : z x (bW02 x) 6 < 0)
    (h53 : z x (bW02 x) 5 ≤ z x (bW02 x) 3) (h50 : 0 ≤ z x (bW02 x) 5) : False := by
  have e := w02_ident h3 h5
  have hp0 : 0 < a5 * b3 - a3 * b5 := by linarith
  have hr0 : 0 ≤ a5 * c3 - a3 * c5 := by linarith
  nlinarith [mul_pos hp0 (neg_pos.mpr hz2), mul_nonneg hr0 (neg_nonneg.mpr h6.le),
    mul_nonneg ha3.le (sub_nonneg.mpr h53), mul_nonneg (sub_nonneg.mpr ha35) (h50.trans h53)]

/-- The ten `FrontDet` diagonals at `bW02 x` shared by the `a2_band_closed*` leaves. -/
structure W02Fronts (x : Fin 7 → ℝ³) : Prop where
  f1523 : FrontDet (x 1) (x 5) (x 2) (x 3) (bW02 x)
  f1526 : FrontDet (x 1) (x 5) (x 2) (x 6) (bW02 x)
  f1326 : FrontDet (x 1) (x 3) (x 2) (x 6) (bW02 x)
  f5613 : FrontDet (x 5) (x 6) (x 1) (x 3) (bW02 x)
  f5623 : FrontDet (x 5) (x 6) (x 2) (x 3) (bW02 x)
  f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bW02 x)
  f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bW02 x)
  f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bW02 x)
  f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bW02 x)
  f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bW02 x)

theorem a2_band_closed_gen {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hOB : H24K.SAT.OB1 x)
    (hband : omega5 x * (omega3 x - Lam5 x) < 1) (ha35 : oblX0 x 3 ≤ oblX0 x 5)
    (hc3 : oblX6 x 3 < 1) (hc53 : oblX6 x 5 < oblX6 x 3) (hLam1 : Lam5 x < 1 + omega3 x)
    (hp : oblX0 x 3 * oblX2 x 5 < oblX0 x 5 * oblX2 x 3)
    (hr : oblX0 x 3 * oblX6 x 5 ≤ oblX0 x 5 * oblX6 x 3)
    (hconv : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3))
    (h8 : 0 < ⟪F.N 8, bW02 x⟫) (hF : W02Fronts x)
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
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
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
    exact hnL (lexAny_w02_ppp F h1 h3 h4 h8 h5 h6 h7 hF.f1523 hF.f1526 hF.f1326 hF.f5613 hF.f5623
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
    exact hnL (lexAny_w02_pmm F h1 h3 h4 h8 h5 h6 h7 hF.f0613 hF.f0615 hF.f0315 hF.f0365 hF.f6513
      n1 n2 n3 n4 n5)
  have hom5 : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
    simp only [omega5]; field_simp
  have hu27 := u27_z_bound F hC hu3 hu8 hnL
  -- `z5 ≥ 0` and `0 ≤ z6` are impossible (NoA identity)
  have hz5_false : 0 ≤ z x (bW02 x) 6 → 0 ≤ z x (bW02 x) 5 → False := by
    intro hz6 hz5
    have id := w02_u27_noA e5 hom5 rfl
    have hom5p : 0 < omega5 x := hC.2.2.1
    have h1 : 0 < 1 + omega3 x - Lam5 x := by linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ omega5 x + 1) hz5, mul_nonneg h1.le hz6,
      mul_nonneg (by linarith : (0:ℝ) ≤ oblX0 x 5) hu27, mul_pos (sub_pos.mpr hband) (neg_pos.mpr hz2)]
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
    · have hc := z_core_neg_z3 _ _ _ _ h6n hz5 P2
      exact w02_neg_false e3 e5 ha3 hp hr ha35 hz2 h6n hc.1 hz5
  · -- the tie `z6 = 0`
    by_cases hz5 : 0 ≤ z x (bW02 x) 5
    · exact hz5_false h60.ge hz5
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
      fun hlt => hnS (splitAny_w02_ppp_e36 F h1 h3 h4 h8 h5 h6 h7 hc5 hc3
        (by linarith) (by nlinarith [mul_pos hc5 hC.2.2.1]) hconv hlt h6p)
    exact hz5_false h6p.le (z_core_pos _ _ _ _ _ hz2 h6p P1 P2 S2)

theorem a2_band_closed {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (_hA2 : Minimality.T24.Reg.A2 x F) (hOB : H24K.SAT.OB1 x)
    (hband : omega5 x * (omega3 x - Lam5 x) < 1) (ha35 : oblX0 x 3 ≤ oblX0 x 5)
    (hc3 : oblX6 x 3 < 1) (hc53 : oblX6 x 5 < oblX6 x 3) (hLam1 : Lam5 x < 1 + omega3 x)
    (hp : oblX0 x 3 * oblX2 x 5 < oblX0 x 5 * oblX2 x 3)
    (hr : oblX0 x 3 * oblX6 x 5 ≤ oblX0 x 5 * oblX6 x 3)
    (hconv : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3))
    (h8 : 0 < ⟪F.N 8, bW02 x⟫) (hF : W02Fronts x)
    (hu3 : 0 < ⟪F.N 3, u27 x⟫) (hu8 : 0 < ⟪F.N 8, u27 x⟫) :
    LexAny F ∨ SplitAny24 F :=
  a2_band_closed_gen F hC hOB hband ha35 hc3 hc53 hLam1 hp hr hconv h8 hF hu3 hu8

end Minimality.T24.A20
