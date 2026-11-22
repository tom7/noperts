module

public import Minimality.Type24BUstar
public import Minimality.Type24A1Z54
public import Minimality.Type24A2Lam
public import Minimality.M4cType24

/-!
# Type 24, region B: `Cert_W26` (the z3 branch of `ustar_collapse`)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Sym Minimality.T24.A8 Minimality.T24.A1 Minimality.T24.A20

theorem cert_w26_alg {a3 t3 om3 om5 A B C al be ga : ℝ}
    (ha3 : 0 < a3) (ht3 : 0 < t3) (ho3 : 0 < om3) (ho5 : 0 < om5) (hB : 0 < B) (hga : 0 ≤ ga)
    (hZ : 0 ≤ a3^2*A - (om3*a3+t3)*(a3+om5*t3)*B + t3^2*C + a3*((a3+om5*t3) - (om3*a3+t3))*al
               + 2*a3*t3*be + t3*((om3*a3+t3) - (a3+om5*t3))*ga)
    (h20 : 0 ≤ -(om5+1)*A + (om3*om5-1)*B + (om3*om5-om5-2)*al + (om3+1)*be - (om3+1)*ga)
    (h26 : 0 ≤ (om3*om5-1)*B - (om3+1)*C - (om5+1)*al + (om5+1)*be + (om3*om5-om3-2)*ga)
    (hN : 0 < (om5+1)^2*A + (om3*om5-1)^2*B + (om3+1)^2*C - 2*(om5+1)*(om3*om5-1)*al
               - 2*(om5+1)*(om3+1)*be - 2*(om3*om5-1)*(om3+1)*ga)
    (hW : be ≤ al) : False := by
  set mu : ℝ := (om3+1)*a3 + (om5+1)*t3 with hmu
  have hmu0 : 0 < mu := by positivity
  have key : (om5+1)*(om3+1)*(a3^2*A - (om3*a3+t3)*(a3+om5*t3)*B + t3^2*C
      + a3*((a3+om5*t3) - (om3*a3+t3))*al + 2*a3*t3*be
      + t3*((om3*a3+t3) - (a3+om5*t3))*ga)
    + a3*mu*(-(om5+1)*A + (om3*om5-1)*B + (om3*om5-om5-2)*al + (om3+1)*be - (om3+1)*ga)
    + t3*mu*((om3*om5-1)*B - (om3+1)*C - (om5+1)*al + (om5+1)*be + (om3*om5-om3-2)*ga)
    + a3*t3*((om5+1)^2*A + (om3*om5-1)^2*B + (om3+1)^2*C - 2*(om5+1)*(om3*om5-1)*al
               - 2*(om5+1)*(om3+1)*be - 2*(om3*om5-1)*(om3+1)*ga)
    + mu^2*(al - be) = -mu^2*(B+ga) := by
    rw [hmu]; ring
  have p1 : 0 ≤ (om5+1)*(om3+1)*(a3^2*A - (om3*a3+t3)*(a3+om5*t3)*B + t3^2*C
      + a3*((a3+om5*t3) - (om3*a3+t3))*al + 2*a3*t3*be
      + t3*((om3*a3+t3) - (a3+om5*t3))*ga) := by positivity
  have p2 := mul_nonneg (mul_pos ha3 hmu0).le h20
  have p3 := mul_nonneg (mul_pos ht3 hmu0).le h26
  have p4 := mul_pos (mul_pos ha3 ht3) hN
  have p5 : 0 ≤ mu^2*(al - be) := mul_nonneg (sq_nonneg _) (by linarith)
  have p6 : 0 ≤ mu^2*(B+ga) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith


/-! ### Geometric inputs -/

theorem hom3_mul {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX2 x 3 = omega3 x * oblX0 x 3 + (1 - oblX6 x 3) := by
  have := (type24OfFac F).eq3; linarith

theorem hom5_mul {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 5 = omega5 x * oblX6 x 5 + 1 - oblX2 x 5 := by
  have := Minimality.T24.M4.eq5 F; linarith

theorem z63_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 6 - x 1, ustar x⟫ - ⟪x 3 - x 1, ustar x⟫ = oblX6 x 5 *
      (oblX0 x 3 ^ 2 * gA x - (omega3 x * oblX0 x 3 + (1 - oblX6 x 3)) *
        (oblX0 x 3 + omega5 x * (1 - oblX6 x 3)) * gB x + (1 - oblX6 x 3) ^ 2 * gC x
        + oblX0 x 3 * ((oblX0 x 3 + omega5 x * (1 - oblX6 x 3)) -
          (omega3 x * oblX0 x 3 + (1 - oblX6 x 3))) * gal x
        + 2 * oblX0 x 3 * (1 - oblX6 x 3) * gbe x
        + (1 - oblX6 x 3) * ((omega3 x * oblX0 x 3 + (1 - oblX6 x 3)) -
          (oblX0 x 3 + omega5 x * (1 - oblX6 x 3))) * gga x) := by
  have hrep := hrep_z54 F
  have hus : ustar x = (-(oblX0 x 3 * oblX6 x 5)) • (x 0 - x 1) +
      (oblX0 x 3 * oblX6 x 5 + (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5 - 1)) • (x 2 - x 1) +
      ((1 - oblX6 x 3) * oblX6 x 5) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by module, hrep 5]; module
    have hD : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
    dsimp [ustar]; rw [h20, h50, hD]; module
  have e : (x 6 - x 1) - (x 3 - x 1) = (-oblX0 x 3) • (x 0 - x 1) + (-oblX2 x 3) • (x 2 - x 1) +
      (1 - oblX6 x 3) • (x 6 - x 1) := by
    rw [hrep 3]; module
  rw [← inner_sub_left, e, hus, gram_expand]
  simp only [gA, gB, gC, gal, gbe, gga]
  have h3 := hom3_mul F
  have h5 := hom5_mul F
  rw [h3]
  have h5' : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith
  rw [h5']
  ring

theorem u20_geom {x : Fin 7 → ℝ³} :
    ⟪x 2 - x 0, u27 x⟫ =
      -(omega5 x + 1) * gA x + (omega3 x * omega5 x - 1) * gB x
        + (omega3 x * omega5 x - omega5 x - 2) * gal x + (omega3 x + 1) * gbe x
        - (omega3 x + 1) * gga x := by
  have e1 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    module
  rw [e1]; unfold u27; rw [gram_expand]; simp only [gA, gB, gal, gbe, gga]; ring

theorem u26_geom {x : Fin 7 → ℝ³} :
    ⟪x 2 - x 6, u27 x⟫ =
      (omega3 x * omega5 x - 1) * gB x - (omega3 x + 1) * gC x - (omega5 x + 1) * gal x
        + (omega5 x + 1) * gbe x + (omega3 x * omega5 x - omega3 x - 2) * gga x := by
  have e1 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  rw [e1]; unfold u27; rw [gram_expand]; simp only [gB, gC, gal, gbe, gga]; ring

theorem nrm_geom {x : Fin 7 → ℝ³} :
    ⟪u27 x, u27 x⟫ =
      (omega5 x + 1) ^ 2 * gA x + (omega3 x * omega5 x - 1) ^ 2 * gB x + (omega3 x + 1) ^ 2 * gC x
        - 2 * (omega5 x + 1) * (omega3 x * omega5 x - 1) * gal x
        - 2 * (omega5 x + 1) * (omega3 x + 1) * gbe x
        - 2 * (omega3 x * omega5 x - 1) * (omega3 x + 1) * gga x := by
  unfold u27; rw [gram_expand]; simp only [gA, gB, gC, gal, gbe, gga]; ring


/-- Region fact: `0 < ⟪N3, u27⟫` for `a5 < 1` (only `CbarIn` for `om3, om5 > 0` is used). -/
theorem hu3_of_a5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 ≤ 1) : 0 < ⟪F.N 3, u27 x⟫ := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hD := d45_pos F
  have f1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have f2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have f30 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f35 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  obtain ⟨e2, e1⟩ := fac3_lin F
  have ev5 := fac_eval F 3 5
  rw [f35, f30] at ev5
  have hom5e := hom5_mul F
  have hα : 0 < -F.f 3 (x 1) := by linarith
  -- c5 nC = D45 (1 - a5) - b5 nB
  have hnC : oblX6 x 5 * nC x = D45 x * (1 - oblX0 x 5) - oblX2 x 5 * nB x := by
    have h : (-F.f 3 (x 1)) * (oblX6 x 5 * nC x - (D45 x * (1 - oblX0 x 5) - oblX2 x 5 * nB x)) = 0 := by
      linear_combination oblX6 x 5 * e2 + oblX2 x 5 * e1 - D45 x * ev5
    have := (mul_eq_zero.mp h).resolve_left hα.ne'
    linarith
  have hT : D45 x * ⟪F.N 3, u27 x⟫ = (-F.f 3 (x 1)) * ((1 + omega5 x) * D45 x +
      (omega3 x * omega5 x - 1) * nB x + (1 + omega3 x) * nC x) := by
    rw [inner_u27_z54, f30]
    linear_combination -(omega3 x * omega5 x - 1) * e1 - (1 + omega3 x) * e2
  have hid : oblX6 x 5 * (D45 x * ⟪F.N 3, u27 x⟫) = (-F.f 3 (x 1)) *
      ((omega3 x * (1 - oblX0 x 5) + oblX2 x 5 + oblX6 x 5) * (D45 x - nB x)) := by
    rw [hT]
    linear_combination (-F.f 3 (x 1)) * ((1 + omega3 x) * hnC +
      (omega3 x * nB x + D45 x) * hom5e.symm)
  have hDn : 0 < D45 x - nB x := by
    have h : (-F.f 3 (x 1)) * (D45 x - nB x) = (-F.f 3 (x 2)) * D45 x := by
      linear_combination -e1
    have : 0 < (-F.f 3 (x 1)) * (D45 x - nB x) := by rw [h]; exact mul_pos (by linarith) hD
    exact pos_of_mul_pos_right this hα.le
  have hK : 0 < omega3 x * (1 - oblX0 x 5) + oblX2 x 5 + oblX6 x 5 := by
    have : 0 ≤ omega3 x * (1 - oblX0 x 5) := mul_nonneg hom3.le (by linarith)
    linarith
  have hpos : 0 < oblX6 x 5 * (D45 x * ⟪F.N 3, u27 x⟫) := by
    rw [hid]; exact mul_pos hα (mul_pos hK hDn)
  have := pos_of_mul_pos_right hpos hc5.le
  exact pos_of_mul_pos_right this hD.le


/-- Region fact: `0 < ⟪N8, u27⟫` for `c3 < 1`. -/
theorem hu8_of_c3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 < 1) : 0 < ⟪F.N 8, u27 x⟫ := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have f2 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
  have f36 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
  have f33 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have ev3 := fac_eval F 8 3
  rw [f33, f36, hom3_mul F] at ev3
  have hmu : 0 < (omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3) := by
    have : 0 < 1 - oblX6 x 3 := by linarith
    positivity
  have hid : oblX0 x 3 * ⟪F.N 8, u27 x⟫ =
      ((omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3)) * (-F.f 8 (x 2)) := by
    rw [inner_u27_z54, f36]
    linear_combination -(1 + omega5 x) * ev3
  have hpos : 0 < oblX0 x 3 * ⟪F.N 8, u27 x⟫ := by
    rw [hid]; exact mul_pos hmu (by linarith)
  exact pos_of_mul_pos_right hpos ha3.le


theorem f3_lt_of_nB_lt_nC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : nB x < nC x) :
    F.f 3 (x 2) < F.f 3 (x 6) := by
  have hD := d45_pos F
  have hα : 0 < -F.f 3 (x 1) := by linarith [F.neg 3 1 (by decide)]
  obtain ⟨e2, e1⟩ := fac3_lin F
  have : 0 < (-F.f 3 (x 1)) * (nC x - nB x) := mul_pos hα (by linarith)
  have h2 : (-F.f 3 (x 1)) * (nC x - nB x) = (F.f 3 (x 6) - F.f 3 (x 2)) * D45 x := by
    linear_combination e2 - e1
  rw [h2] at this
  have := pos_of_mul_pos_left this hD.le
  linarith

/-- **Cert_W26, geometric version**: in region B with `nB < nC`, `z3(u*) <= z6(u*)` is impossible
(away from `LexAny`). -/
theorem cert_w26_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 ≤ 1) (hc3 : oblX6 x 3 < 1)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : nB x < nC x) (hU : ¬ Minimality.Gen.LexAny F)
    (hz3 : ⟪x 3 - x 1, ustar x⟫ ≤ ⟪x 6 - x 1, ustar x⟫) : False := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hu3 := hu3_of_a5 F hC ha5
  have hu8 := hu8_of_c3 F hC hc3
  have hz20 := u27_z_bound F hC hu3 hu8 hU
  have hz26 := u27_z26_bound F hC hu3 hu8 hU
  have hW := w26_geom (w26_bound F hC hbc (f3_lt_of_nB_lt_nC F hn) hU)
  have hne : u27 x ≠ 0 := by
    intro h0; rw [h0] at hu3; simp at hu3
  have hN : 0 < ⟪u27 x, u27 x⟫ := real_inner_self_pos.mpr hne
  have hB : 0 < gB x := by
    have : x 2 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
    exact real_inner_self_pos.mpr this
  have hga : 0 ≤ gga x := by simp only [gga]; linarith
  have hZ := z63_geom F
  have hZ' : 0 ≤ oblX6 x 5 * (oblX0 x 3 ^ 2 * gA x - (omega3 x * oblX0 x 3 + (1 - oblX6 x 3)) *
        (oblX0 x 3 + omega5 x * (1 - oblX6 x 3)) * gB x + (1 - oblX6 x 3) ^ 2 * gC x
        + oblX0 x 3 * ((oblX0 x 3 + omega5 x * (1 - oblX6 x 3)) -
          (omega3 x * oblX0 x 3 + (1 - oblX6 x 3))) * gal x
        + 2 * oblX0 x 3 * (1 - oblX6 x 3) * gbe x
        + (1 - oblX6 x 3) * ((omega3 x * oblX0 x 3 + (1 - oblX6 x 3)) -
          (oblX0 x 3 + omega5 x * (1 - oblX6 x 3))) * gga x) := by
    rw [← hZ]; linarith
  have hZ'' := (mul_nonneg_iff_of_pos_left hc5).mp hZ'
  rw [u20_geom] at hz20
  rw [u26_geom] at hz26
  rw [nrm_geom] at hN
  exact cert_w26_alg (a3 := oblX0 x 3) (t3 := 1 - oblX6 x 3) ha3 (by linarith) hom3 hom5 hB hga
    (by linarith) hz20 hz26 hN hW


/-- **`ustar_collapse` without the `z6 < z3` part of its depth condition** (when `nB < nC`): only
`0 < z3(u*)` and `max 0 z6(u*) < z5(u*)` remain. -/
theorem ustar_closed_W26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 ≤ 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : nB x < nC x)
    (hz3 : 0 < ⟪x 3 - x 1, ustar x⟫)
    (hz5 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  by_cases hU : Minimality.Gen.LexAny F
  · exact Or.inl hU
  have h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ := by
    by_contra h
    exact cert_w26_geom F hC ha5 hc3 hbc hn hU (not_lt.mp h)
  exact ustar_collapse F hC ha5 hc3 hD h8 hab hac
    (lt_min (max_lt hz3 h63) hz5)

/-- Variant: when `0 ≤ z6(u*)` the whole `z3` condition is dropped. -/
theorem ustar_closed_W26_z6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 ≤ 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : nB x < nC x)
    (hz6 : 0 ≤ ⟪x 6 - x 1, ustar x⟫)
    (hz5 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  by_cases hU : Minimality.Gen.LexAny F
  · exact Or.inl hU
  have h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ := by
    by_contra h
    exact cert_w26_geom F hC ha5 hc3 hbc hn hU (not_lt.mp h)
  rw [← max_eq_right hz6] at h63 hz5
  exact ustar_collapse F hC ha5 hc3 hD h8 hab hac (lt_min h63 hz5)

end Minimality.T24.A10
