module

public import Minimality.Type24A2Lam
public import Minimality.Type24BSharp

@[expose] public section

/-!
# Type 24, region A2 (`band > 1`): confirmed chain pieces (`A33-REFEREE`)

Formalizes the referee-confirmed pieces of Carbon A33 in `Minimality.T24.A20`:
1. `w63_syzygy`: `(omega3 x + 1) • (x 3 - x 6) + (1 - oblX6 x 3) • u27 x = muStar • u07 x`;
2. `u07_alphaBound_id`, `z2_w63_eq`, `w63_z2gtz0_id`: the `U07-AlphaBound` and `W63-Z2gtZ0`
   Gram-coordinate identities (with `al = -⟪x 0 - x 1, x 2 - x 1⟫`, `ga = -⟪x 2 - x 1, x 6 - x 1⟫`);
3. `z2_pos_w63` and `z2_gt_z0_w63`: `z2(w63) > 0` and `z2(w63) > z0(w63)` on `OB1` from `u07_bound`,
   Cauchy–Schwarz, and `0 ≤ z6(x 2 - x 0)`;
4. `w63_facings` and `w63_collapse_z0_neg` / `w63_collapse_z0_nonpos`: unconditional facet signs
   of `w63 = x 3 - x 6` on `{CbarIn, c3 < 1}` and the `z0(w63) ≤ 0` half of `W63-SharpCollapse`
   on the 5-rim `![1, 2, 3, 4, 0]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10
  Minimality.T24.A8 Minimality.T24.Q24 Minimality.T24 Minimality.T24.A15

/-- **1. `F236` syzygy**: `(om3 + 1) w63 + t3 u27 = mu* u07` with `w63 = x 3 - x 6`. -/
theorem w63_syzygy {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (omega3 x + 1) • (x 3 - x 6) + (1 - oblX6 x 3) • u27 x =
      ((omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3)) • u07 x := by
  have T := type24OfFac F
  have h3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
  have hw : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      (oblX6 x 3 - 1) • (x 6 - x 1) := by
    have h36 : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
    rw [h36, h3]
    module
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by
    linarith [eq3 F]
  rw [hw, hb3]
  dsimp only [u27, u07]
  module

/-- **2a. `U07-AlphaBound` identity**: `(om3 B - al)(B + al) = B * U07_20 + (A B - al^2)`
with `al = -⟪x 0 - x 1, x 2 - x 1⟫`. -/
theorem u07_alphaBound_id (x : Fin 7 → ℝ³) :
    let A := ⟪x 0 - x 1, x 0 - x 1⟫
    let B := ⟪x 2 - x 1, x 2 - x 1⟫
    let al := -⟪x 0 - x 1, x 2 - x 1⟫
    (omega3 x * B - al) * (B + al) = B * ⟪x 2 - x 0, u07 x⟫ + (A * B - al ^ 2) := by
  have h20 : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
  have eu07 : ⟪x 2 - x 0, u07 x⟫ =
      (⟪x 2 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 0 - x 1⟫) +
        omega3 x * (⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫) := by
    dsimp only [u07]
    rw [h20, inner_add_right, real_inner_smul_right,
      inner_sub_left (x 2 - x 1) (x 0 - x 1) (x 0 - x 1),
      inner_sub_left (x 2 - x 1) (x 0 - x 1) (x 2 - x 1)]
  rw [eu07, real_inner_comm (x 2 - x 1) (x 0 - x 1)]
  ring

/-- **2b. `z2(w63)` formula**: `z2(w63) = a3 (om3 B - al) + t3 (B + ga)`
with `al = -⟪x 0 - x 1, x 2 - x 1⟫` and `ga = -⟪x 2 - x 1, x 6 - x 1⟫`. -/
theorem z2_w63_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 2 - x 1, x 3 - x 6⟫ =
      oblX0 x 3 * (omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ - (-⟪x 0 - x 1, x 2 - x 1⟫)) +
        (1 - oblX6 x 3) * (⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 2 - x 1, x 6 - x 1⟫)) := by
  have h36 : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
  have e32 : ⟪x 2 - x 1, x 3 - x 6⟫ = ⟪x 3 - x 1, x 2 - x 1⟫ - ⟪x 6 - x 1, x 2 - x 1⟫ := by
    rw [h36, inner_sub_right, real_inner_comm (x 2 - x 1) (x 3 - x 1),
      real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  rw [e32, inner_rep F 3 (x 2 - x 1), real_inner_comm (x 6 - x 1) (x 2 - x 1)]
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
  rw [hb3]
  ring

/-- **2c. `W63-Z2gtZ0` identity**:
`z0(w63) - z2(w63) + a3 U07_20 + t3 z6(x 0 - x 2) = -t3 (B + al)`
with `al = -⟪x 0 - x 1, x 2 - x 1⟫`. -/
theorem w63_z2gtz0_id {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 0 - x 1, x 3 - x 6⟫ - ⟪x 2 - x 1, x 3 - x 6⟫ +
      oblX0 x 3 * ⟪x 2 - x 0, u07 x⟫ + (1 - oblX6 x 3) * ⟪x 6 - x 1, x 0 - x 2⟫ =
      -(1 - oblX6 x 3) * (⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 0 - x 1, x 2 - x 1⟫)) := by
  have h36 : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
  have h20 : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
  have h02 : x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) := by abel
  have e30 : ⟪x 0 - x 1, x 3 - x 6⟫ = ⟪x 3 - x 1, x 0 - x 1⟫ - ⟪x 6 - x 1, x 0 - x 1⟫ := by
    rw [h36, inner_sub_right, real_inner_comm (x 0 - x 1) (x 3 - x 1),
      real_inner_comm (x 0 - x 1) (x 6 - x 1)]
  have e32 : ⟪x 2 - x 1, x 3 - x 6⟫ = ⟪x 3 - x 1, x 2 - x 1⟫ - ⟪x 6 - x 1, x 2 - x 1⟫ := by
    rw [h36, inner_sub_right, real_inner_comm (x 2 - x 1) (x 3 - x 1),
      real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  have e602 : ⟪x 6 - x 1, x 0 - x 2⟫ = ⟪x 6 - x 1, x 0 - x 1⟫ - ⟪x 6 - x 1, x 2 - x 1⟫ := by
    rw [h02, inner_sub_right]
  have eu07 : ⟪x 2 - x 0, u07 x⟫ =
      (⟪x 2 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 0 - x 1⟫) +
        omega3 x * (⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫) := by
    dsimp only [u07]
    rw [h20, inner_add_right, real_inner_smul_right,
      inner_sub_left (x 2 - x 1) (x 0 - x 1) (x 0 - x 1),
      inner_sub_left (x 2 - x 1) (x 0 - x 1) (x 2 - x 1)]
  rw [e30, e32, e602, eu07, inner_rep F 3 (x 0 - x 1), inner_rep F 3 (x 2 - x 1)]
  rw [real_inner_comm (x 2 - x 1) (x 0 - x 1)]
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
  rw [hb3]
  ring

/-- **3a. `z2(w63) > 0`** on `OB1` from `u07_bound` and Cauchy–Schwarz (`A B - al^2 > 0`). -/
theorem z2_pos_w63 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (hL : ¬ LexAny F)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    0 < ⟪x 2 - x 1, x 3 - x 6⟫ := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ht3 : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have hu07 : 0 ≤ ⟪x 2 - x 0, u07 x⟫ := by
    have := u07_bound F hC hc3 hL
    have e : ⟪x 2 - x 0, u07 x⟫ =
        omega3 x * ⟪x 2 - x 1, x 2 - x 0⟫ - (-⟪x 0 - x 1, x 2 - x 0⟫) := by
      dsimp [u07]
      rw [inner_add_right, real_inner_smul_right,
        real_inner_comm (x 2 - x 0) (x 0 - x 1), real_inner_comm (x 2 - x 0) (x 2 - x 1)]
      ring
    linarith
  have hB : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hBal : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 0 - x 1, x 2 - x 1⟫) := by linarith
  have hBga : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 2 - x 1, x 6 - x 1⟫) := by linarith
  have hCS : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 2 - x 1, x 2 - x 1⟫ -
      (-⟪x 0 - x 1, x 2 - x 1⟫) ^ 2 := by
    let r : ℝ := ⟪x 0 - x 1, x 2 - x 1⟫ / ⟪x 2 - x 1, x 2 - x 1⟫
    have hne : (x 0 - x 1) - r • (x 2 - x 1) ≠ 0 := by
      intro h0
      have hr : x 0 - x 1 = r • (x 2 - x 1) := sub_eq_zero.mp h0
      have h03 : ⟪F.N 5, x 0 - x 1⟫ = r * ⟪F.N 5, x 2 - x 1⟫ := by
        rw [hr, real_inner_smul_right]
      rw [← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 2) (x 1), F.zero 5 1 (by decide),
        F.zero 5 2 (by decide), sub_zero, sub_self, mul_zero] at h03
      exact (F.neg 5 0 (by decide)).ne h03
    set u := x 0 - x 1
    set v := x 2 - x 1
    have hpos := real_inner_self_pos.mpr hne
    change 0 < ⟪u - r • v, u - r • v⟫ at hpos
    rw [inner_sub_left u (r • v), inner_sub_right u u (r • v),
      inner_sub_right (r • v) u (r • v), real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm v u] at hpos
    have hdiv : r * ⟪v, v⟫ = ⟪u, v⟫ := div_mul_cancel₀ _ hB.ne'
    have hvu : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm u v
    rw [hvu] at hpos
    have hpos2 : 0 < ⟪u, u⟫ - 2 * r * ⟪u, v⟫ + r * (r * ⟪v, v⟫) := by linarith
    nlinarith [mul_pos hpos2 hB]
  have hid := u07_alphaBound_id x
  dsimp only at hid
  have hprod : 0 < (omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ - (-⟪x 0 - x 1, x 2 - x 1⟫)) *
      (⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 0 - x 1, x 2 - x 1⟫)) := by
    nlinarith
  have homB : 0 < omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ - (-⟪x 0 - x 1, x 2 - x 1⟫) :=
    pos_of_mul_pos_left hprod hBal.le
  rw [z2_w63_eq F]
  nlinarith

/-- **3b. `z2(w63) > z0(w63)`** on `OB1` from `u07_bound` and `0 ≤ z6(x 0 - x 2)`. -/
theorem z2_gt_z0_w63 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (hL : ¬ LexAny F)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hz6 : 0 ≤ ⟪x 6 - x 1, x 0 - x 2⟫) :
    ⟪x 0 - x 1, x 3 - x 6⟫ < ⟪x 2 - x 1, x 3 - x 6⟫ := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ht3 : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have hB : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hBal : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ + (-⟪x 0 - x 1, x 2 - x 1⟫) := by linarith
  have hu07 : 0 ≤ ⟪x 2 - x 0, u07 x⟫ := by
    have := u07_bound F hC hc3 hL
    have e : ⟪x 2 - x 0, u07 x⟫ =
        omega3 x * ⟪x 2 - x 1, x 2 - x 0⟫ - (-⟪x 0 - x 1, x 2 - x 0⟫) := by
      dsimp [u07]
      rw [inner_add_right, real_inner_smul_right,
        real_inner_comm (x 2 - x 0) (x 0 - x 1), real_inner_comm (x 2 - x 0) (x 2 - x 1)]
      ring
    linarith
  have hid := w63_z2gtz0_id F
  nlinarith

/-- **4a. Unconditional facet signs at `w63 = x 3 - x 6`** on `{CbarIn x, c3 < 1}`:
`Up = {0, 2, 3, 6}`, `Dn = {1, 4, 5}`, on-line `{7, 8}`. -/
theorem w63_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) :
    0 < ⟪F.N 0, x 3 - x 6⟫ ∧ ⟪F.N 1, x 3 - x 6⟫ < 0 ∧ 0 < ⟪F.N 2, x 3 - x 6⟫ ∧
    0 < ⟪F.N 3, x 3 - x 6⟫ ∧ ⟪F.N 4, x 3 - x 6⟫ < 0 ∧ ⟪F.N 5, x 3 - x 6⟫ < 0 ∧
    0 < ⟪F.N 6, x 3 - x 6⟫ ∧ ⟪F.N 7, x 3 - x 6⟫ = 0 ∧ ⟪F.N 8, x 3 - x 6⟫ = 0 := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3_pos : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have hw : ∀ t : Fin 9, ⟪F.N t, x 3 - x 6⟫ = F.f t (x 3) - F.f t (x 6) :=
    fun t => (F.hN t (x 3) (x 6)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 0]
    have ev0 := fac_eval F 0 3
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev0
    have h06 : 0 < -F.f 0 (x 6) := by linarith [F.neg 0 6 (by decide)]
    have hd : F.f 0 (x 3) - F.f 0 (x 6) = (1 - oblX6 x 3) * (-F.f 0 (x 6)) := by
      rw [ev0]; ring
    rw [hd]; exact mul_pos hc3_pos h06
  · rw [hw 1, F.zero 1 6 (by decide), sub_zero]
    exact F.neg 1 3 (by decide)
  · rw [hw 2]
    have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
      have ev2_5 := fac_eval F 2 5
      rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
      have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
      have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
        simp only [omega5]; field_simp
      have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
        linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
    have ev2_3 := fac_eval F 2 3
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_3
    have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
    have hd : F.f 2 (x 3) - (1 + omega5 x) * F.f 2 (x 1) =
        (-F.f 2 (x 1)) * ((omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3)) := by
      rw [ev2_3, hb3]; ring
    rw [hf2_6, hd]
    have h21 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
    exact mul_pos h21 (by nlinarith)
  · rw [hw 3, F.zero 3 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 3 6 (by decide))
  · rw [hw 4, F.zero 4 6 (by decide), sub_zero]
    exact F.neg 4 3 (by decide)
  · rw [hw 5, F.zero 5 6 (by decide), sub_zero]
    exact F.neg 5 3 (by decide)
  · rw [hw 6, F.zero 6 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 6 6 (by decide))
  · rw [hw 7, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self]
  · rw [hw 8, F.zero 8 3 (by decide), F.zero 8 6 (by decide), sub_self]

private def c_w63 : ZMod 5 → Fin 7 := ![1, 2, 3, 4, 0]
private def U_w63 : Finset (Fin 9) := {0, 2, 3, 6}
private def Dn_w63 : Finset (Fin 9) := {1, 4, 5, 7, 8}

private theorem c_w63_inj : Function.Injective c_w63 := by decide
private theorem cyc_w63 : S0xCycUD s0x_S24 c_w63 U_w63 Dn_w63 := by decide

private theorem w63_lex_of_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1)
    (hz2 : 0 < ⟪x 2 - x 1, x 3 - x 6⟫)
    (hz3 : ⟪x 3 - x 1, x 3 - x 6⟫ < 0)
    (hz4 : ⟪x 4 - x 1, x 3 - x 6⟫ < 0)
    (hz0 : ⟪x 0 - x 1, x 3 - x 6⟫ ≤ 0)
    (hF3014 : GenQuad.FrontOf (x 3) (x 0) (x 1) (x 4) (x 3 - x 6))
    (hF3024 : GenQuad.FrontOf (x 3) (x 0) (x 2) (x 4) (x 3 - x 6))
    (d1 : ℝ³) (hd7 : ⟪F.N 7, d1⟫ < 0) (hd8 : ⟪F.N 8, d1⟫ < 0)
    (hd0 : ⟪x 0 - x 1, x 3 - x 6⟫ = 0 → ⟪x 0 - x 1, d1⟫ < 0) :
    LexAny F := by
  have T := type24OfFac F
  have hw_ne : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hfac := w63_facings F hC hc3
  have hU : ∀ t ∈ U_w63, LexPos3 ⟪F.N t, x 3 - x 6⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
    intro t ht
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl hfac.1
    · exact Or.inl hfac.2.2.1
    · exact Or.inl hfac.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.1
  have hD : ∀ t ∈ Dn_w63, LexPos3 (-⟪F.N t, x 3 - x 6⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
    intro t ht
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr hfac.2.1)
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.1, Or.inl (neg_pos.mpr hd7)⟩
    · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.2, Or.inl (neg_pos.mpr hd8)⟩
  have hcl_gt : ∀ (p q r s : Fin 7),
      (⟪x r - x 1, x 3 - x 6⟫ < ⟪x p - x 1, x 3 - x 6⟫ ∨
       ⟪x s - x 1, x 3 - x 6⟫ < ⟪x p - x 1, x 3 - x 6⟫ ∨
       ⟪x r - x 1, x 3 - x 6⟫ < ⟪x q - x 1, x 3 - x 6⟫ ∨
       ⟪x s - x 1, x 3 - x 6⟫ < ⟪x q - x 1, x 3 - x 6⟫) →
      Minimality.GenQuad.LexClause (x p) (x q) (x r) (x s) (x 3 - x 6) d1 0 := by
    intro p q r s h
    apply Minimality.GenQuad.lexClause_of_notM
    rintro ⟨h1, h2, h3, h4⟩
    rcases h with h | h | h | h <;>
    · rw [inner_sub_left, inner_sub_left] at h; linarith
  refine Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c_w63_inj cyc_w63
    (x 3 - x 6) d1 0 hU hD ?_
  refine Minimality.GenQuad.clauses_five (p := fun i => x (c_w63 i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp only [c_w63, Matrix.cons_val]
  · exact hcl_gt 2 4 1 3 (Or.inr (Or.inl (by linarith)))
  · exact hcl_gt 1 3 2 4 (Or.inr (Or.inl (by rw [sub_self, inner_zero_left]; exact hz4)))
  · exact hcl_gt 2 0 1 3 (Or.inr (Or.inl (by linarith)))
  · rcases eq_or_lt_of_le hz0 with hz0_eq | hz0_lt
    · refine Or.inr (Or.inl (Or.inr ⟨?_, Or.inl ?_⟩))
      · dsimp only; rw [inner_sub_left] at hz0_eq; linarith
      · dsimp only; have h0d := hd0 hz0_eq; rw [inner_sub_left] at h0d; linarith
    · exact hcl_gt 1 3 2 0 (Or.inr (Or.inl (by rw [sub_self, inner_zero_left]; exact hz0_lt)))
  · exact hcl_gt 2 0 1 4 (Or.inr (Or.inl (by linarith)))
  · rcases eq_or_lt_of_le hz0 with hz0_eq | hz0_lt
    · refine Or.inr (Or.inl (Or.inr ⟨?_, Or.inl ?_⟩))
      · dsimp only; rw [inner_sub_left] at hz0_eq; linarith
      · dsimp only; have h0d := hd0 hz0_eq; rw [inner_sub_left] at h0d; linarith
    · exact hcl_gt 1 4 2 0 (Or.inr (Or.inl (by rw [sub_self, inner_zero_left]; exact hz0_lt)))
  · exact Minimality.GenQuad.lexClause_of_frontOf hw_ne hF3014
  · exact hcl_gt 1 4 3 0 (Or.inl (by rw [sub_self, inner_zero_left]; exact hz3))
  · exact Minimality.GenQuad.lexClause_of_frontOf hw_ne hF3024
  · exact hcl_gt 2 4 3 0 (Or.inl (by linarith))

/-- **4b. `z0(w63) < 0` half of `W63-SharpCollapse`** (no tilt-direction hypothesis needed;
uses `d1 = x 0 - x 6`). -/
theorem w63_collapse_z0_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1)
    (hz2 : 0 < ⟪x 2 - x 1, x 3 - x 6⟫)
    (hz0 : ⟪x 0 - x 1, x 3 - x 6⟫ < 0)
    (hF3014 : GenQuad.FrontOf (x 3) (x 0) (x 1) (x 4) (x 3 - x 6))
    (hF3024 : GenQuad.FrontOf (x 3) (x 0) (x 2) (x 4) (x 3 - x 6))
    (hL : ¬ LexAny F) :
    0 ≤ max ⟪x 3 - x 1, x 3 - x 6⟫ ⟪x 4 - x 1, x 3 - x 6⟫ := by
  by_contra hneg
  push Not at hneg
  rw [max_lt_iff] at hneg
  have hd7 : ⟪F.N 7, x 0 - x 6⟫ < 0 := by
    rw [← F.hN 7 (x 0) (x 6), F.zero 7 6 (by decide), sub_zero]
    exact F.neg 7 0 (by decide)
  have hd8 : ⟪F.N 8, x 0 - x 6⟫ < 0 := by
    rw [← F.hN 8 (x 0) (x 6), F.zero 8 6 (by decide), sub_zero]
    exact F.neg 8 0 (by decide)
  exact hL (w63_lex_of_tilt F hC hc3 hz2 hneg.1 hneg.2 hz0.le hF3014 hF3024 (x 0 - x 6) hd7 hd8
    (fun heq => absurd heq hz0.ne))

/-- **4c. `z0(w63) ≤ 0` half of `W63-SharpCollapse`** (with a `{236-, 346-}` tilt `d1` for
the `z0 = 0` boundary). -/
theorem w63_collapse_z0_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1)
    (hz2 : 0 < ⟪x 2 - x 1, x 3 - x 6⟫)
    (hz0 : ⟪x 0 - x 1, x 3 - x 6⟫ ≤ 0)
    (hF3014 : GenQuad.FrontOf (x 3) (x 0) (x 1) (x 4) (x 3 - x 6))
    (hF3024 : GenQuad.FrontOf (x 3) (x 0) (x 2) (x 4) (x 3 - x 6))
    (hd1 : ∃ d1 : ℝ³, ⟪F.N 7, d1⟫ < 0 ∧ ⟪F.N 8, d1⟫ < 0 ∧
      (⟪x 0 - x 1, x 3 - x 6⟫ = 0 → ⟪x 0 - x 1, d1⟫ < 0))
    (hL : ¬ LexAny F) :
    0 ≤ max ⟪x 3 - x 1, x 3 - x 6⟫ ⟪x 4 - x 1, x 3 - x 6⟫ := by
  by_contra hneg
  push Not at hneg
  rw [max_lt_iff] at hneg
  rcases hd1 with ⟨d1, hd7, hd8, hd0⟩
  exact hL (w63_lex_of_tilt F hC hc3 hz2 hneg.1 hneg.2 hz0 hF3014 hF3024 d1 hd7 hd8 hd0)

end Minimality.T24.A20
