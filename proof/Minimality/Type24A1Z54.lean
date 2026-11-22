module

public import Minimality.Type24A1E25
public import Minimality.Type24A1Tie

/-!
# Type 24, region A1 off the tie: the step `z54_half` (T2: `z4(w05) < z5(w05)`)

A22-REFEREE section 3.3 (exact `t = 1/2` identity) in Lean: `z54_half_alg` (pure algebra), `z54_A1`
(geometric version), `a1_offtie_rupert` (off-tie A1 closes except the named sample facts `A1Z54Sample`
and `A1E25Sample`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.A10 Minimality.T24.Q24 Minimality.T24 Minimality.GenQuad Minimality.T24.A15


/-- Shape reals of the A1 corner frame (`y_v = (a_v, b_v, c_v)`, `om3`, `om5`). -/
structure Z54Shape where
  a4 : ℝ
  b4 : ℝ
  c4 : ℝ
  a5 : ℝ
  b5 : ℝ
  c5 : ℝ
  om3 : ℝ
  om5 : ℝ

noncomputable section
namespace Z54Shape
variable (s : Z54Shape)

def mu : ℝ := (s.c4 - s.c5) * s.c5
def Lam5 : ℝ := s.b5 + s.c5 + s.om3 * (1 - s.a5)
def Kal : ℝ := (s.a5 - s.a4) * s.b5 + (s.b5 - s.b4) * (s.a5 - 1)
def Kbe : ℝ := (s.a5 - s.a4) * s.c5 + (s.c5 - s.c4) * (s.a5 - 1)
def Kga : ℝ := (s.b5 - s.b4) * s.c5 + (s.c5 - s.c4) * s.b5
def PA : ℝ := (1 + s.om3) * (s.a5 - s.a4) * (s.a5 - 1)
def PB : ℝ := (1 + s.om3) * (s.b5 - s.b4) * s.b5 - s.mu * (s.om3 * s.om5 - 1)
def Qal : ℝ := (1 + s.om3) * s.Kal - s.mu * (s.om5 + 1)
def Qbe : ℝ := (1 + s.om3) * s.Kbe + s.mu * (s.om5 + 1)
def Qga : ℝ := (1 + s.om3) * s.Kga + s.mu * (s.om3 * s.om5 - s.om3 - 2)
def PAh : ℝ := s.c4 * s.PA + (1 - s.a4) * s.Qbe / 2
def PBh : ℝ := s.c4 * s.PB - s.b4 * s.om3 * s.Qbe / 2
def Qalh : ℝ := s.c4 * s.Qal + ((1 - s.a4) * s.om3 - s.b4 + s.c4) * s.Qbe / 2
def Qgah : ℝ := s.c4 * s.Qga - s.c4 * s.om3 * s.Qbe / 2

/-- `Z45 = z4(w05) - z5(w05)` in the corner frame. -/
def Z45 (A B C al be ga : ℝ) : ℝ :=
  -(s.a5 - s.a4) * (s.a5 - 1) * A - (s.b5 - s.b4) * s.b5 * B + (s.c4 - s.c5) * s.c5 * C
    + s.Kal * al + s.Kbe * be + s.Kga * ga
/-- `U27_26 = (z2 - z6)(u27)`. -/
def U27 (B C al be ga : ℝ) : ℝ :=
  (s.om3 * s.om5 - 1) * B - (1 + s.om3) * C - (s.om5 + 1) * al + (s.om5 + 1) * be
    + (s.om3 * s.om5 - s.om3 - 2) * ga
/-- `U07_40 = (z4 - z0)(u07)`. -/
def U07 (A B al be ga : ℝ) : ℝ :=
  -(1 - s.a4) * A + s.b4 * s.om3 * B + ((1 - s.a4) * s.om3 - s.b4) * al - s.c4 * be
    - s.c4 * s.om3 * ga

/-- The exact `t = 1/2` identity (A22-REFEREE 3.3). -/
theorem ident (A B C al be ga : ℝ) :
    s.c4 * (1 + s.om3) * s.Z45 A B C al be ga + s.c4 * s.mu * s.U27 B C al be ga
      + s.Qbe / 2 * s.U07 A B al be ga + s.c4 * s.Qbe / 2 * (al - be)
    = -s.PAh * A - s.PBh * B + s.Qalh * al + s.Qgah * ga := by
  simp only [Z45, U27, U07, mu, Kal, Kbe, Kga, PA, PB, Qal, Qbe, Qga, PAh, PBh, Qalh, Qgah]
  ring

theorem Qbe_eq (hom5 : s.a5 + s.b5 - 1 = s.om5 * s.c5) :
    s.Qbe = (1 + s.om3) * (s.a5 - s.a4) * s.c5 + (s.c4 - s.c5) * s.Lam5 := by
  simp only [Qbe, mu, Kbe, Lam5]
  linear_combination (s.c4 - s.c5) * hom5 * (-1)

/-- Lemma Qbe-Pos (case `c4 > c5`). -/
theorem Qbe_pos (hom5 : s.a5 + s.b5 - 1 = s.om5 * s.c5) (ha5 : 1 < s.a5) (ha4 : s.a4 ≤ 1)
    (hc5 : 0 < s.c5) (hom3 : 0 < s.om3) (hL : 0 < s.Lam5) (hc45 : s.c5 < s.c4) : 0 < s.Qbe := by
  rw [Qbe_eq s hom5]
  have h1 : 0 < (1 + s.om3) * (s.a5 - s.a4) * s.c5 :=
    mul_pos (mul_pos (by linarith) (by linarith)) hc5
  have h2 : 0 < (s.c4 - s.c5) * s.Lam5 := mul_pos (by linarith) hL
  linarith

theorem PAh_pos (hom5 : s.a5 + s.b5 - 1 = s.om5 * s.c5) (ha5 : 1 < s.a5) (ha4 : s.a4 ≤ 1)
    (hc5 : 0 < s.c5) (hom3 : 0 < s.om3) (hL : 0 < s.Lam5) (hc45 : s.c5 < s.c4) : 0 < s.PAh := by
  have hQ := Qbe_pos s hom5 ha5 ha4 hc5 hom3 hL hc45
  have h1 : 0 < s.c4 * s.PA :=
    mul_pos (by linarith) (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
  have h2 : 0 ≤ (1 - s.a4) * s.Qbe / 2 := by
    have : 0 ≤ (1 - s.a4) * s.Qbe := mul_nonneg (by linarith) hQ.le
    linarith
  simp only [PAh]; linarith

/-- Core: the PD step, with the quadratic form at `v = (2 PAh, max 0 Qalh)` positive. -/
theorem half_core (A B C al be ga : ℝ) (hom5 : s.a5 + s.b5 - 1 = s.om5 * s.c5)
    (ha5 : 1 < s.a5) (ha4 : s.a4 ≤ 1) (hc5 : 0 < s.c5) (hom3 : 0 < s.om3) (hL : 0 < s.Lam5)
    (hc45 : s.c5 < s.c4) (hQg : s.Qgah ≤ 0) (hQ : max 0 s.Qalh ^ 2 ≤ 4 * s.PAh * s.PBh)
    (hZ : 0 ≤ s.Z45 A B C al be ga) (hU27 : 0 ≤ s.U27 B C al be ga)
    (hU07 : 0 ≤ s.U07 A B al be ga) (hW : be ≤ al) (hal : 0 ≤ al) (hga : 0 ≤ ga)
    (hB : 0 ≤ B)
    (hv : 0 < 4 * s.PAh ^ 2 * A - 4 * s.PAh * max 0 s.Qalh * al + max 0 s.Qalh ^ 2 * B) :
    False := by
  have hQbe := Qbe_pos s hom5 ha5 ha4 hc5 hom3 hL hc45
  have hPA := PAh_pos s hom5 ha5 ha4 hc5 hom3 hL hc45
  have hc4 : 0 < s.c4 := by linarith
  have hmu : 0 ≤ s.mu := mul_nonneg (by linarith) hc5.le
  have hid := ident s A B C al be ga
  have h0 : 0 ≤ -s.PAh * A - s.PBh * B + s.Qalh * al + s.Qgah * ga := by
    rw [← hid]
    have a1 : 0 ≤ s.c4 * (1 + s.om3) * s.Z45 A B C al be ga :=
      mul_nonneg (mul_nonneg hc4.le (by linarith)) hZ
    have a2 : 0 ≤ s.c4 * s.mu * s.U27 B C al be ga := mul_nonneg (mul_nonneg hc4.le hmu) hU27
    have a3 : 0 ≤ s.Qbe / 2 * s.U07 A B al be ga := mul_nonneg (by linarith) hU07
    have a4 : 0 ≤ s.c4 * s.Qbe / 2 * (al - be) :=
      mul_nonneg (by have := mul_pos hc4 hQbe; linarith) (by linarith)
    linarith
  set q := max 0 s.Qalh with hqdef
  have hqa : s.Qalh ≤ q := le_max_right _ _
  have h1 : s.Qalh * al ≤ q * al := mul_le_mul_of_nonneg_right hqa hal
  have h2 : s.Qgah * ga ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hQg hga
  have h3 : 0 ≤ -s.PAh * A - s.PBh * B + q * al := by linarith
  have h4 : 0 ≤ 4 * s.PAh * (-s.PAh * A - s.PBh * B + q * al) :=
    mul_nonneg (by linarith) h3
  have h5 : 0 ≤ B * (4 * s.PAh * s.PBh - q ^ 2) := mul_nonneg hB (by linarith)
  nlinarith

end Z54Shape
end

/-- Pure algebra of `z54_half` (A22-REFEREE 3.3). -/
theorem z54_half_alg (s : Z54Shape) (A B C al be ga : ℝ)
    (hom5 : s.a5 + s.b5 - 1 = s.om5 * s.c5)
    (ha5 : 1 < s.a5) (ha4 : s.a4 ≤ 1) (hc5 : 0 < s.c5) (hom3 : 0 < s.om3) (hL : 0 < s.Lam5)
    (hc45 : s.c5 < s.c4) (hQg : s.Qgah ≤ 0) (hQ : max 0 s.Qalh ^ 2 ≤ 4 * s.PAh * s.PBh)
    (hZ : 0 ≤ s.Z45 A B C al be ga) (hU27 : 0 ≤ s.U27 B C al be ga)
    (hU07 : 0 ≤ s.U07 A B al be ga) (hW : be ≤ al) (hal : 0 ≤ al) (hga : 0 ≤ ga)
    (hA : 0 < A) (hAB : al ^ 2 < A * B) : False := by
  have hB : 0 < B := by
    by_contra h; push Not at h
    nlinarith [sq_nonneg al, mul_nonpos_of_nonneg_of_nonpos hA.le h]
  have hPA := s.PAh_pos hom5 ha5 ha4 hc5 hom3 hL hc45
  refine s.half_core A B C al be ga hom5 ha5 ha4 hc5 hom3 hL hc45 hQg hQ hZ hU27 hU07 hW hal hga
    hB.le ?_
  set q := max 0 s.Qalh
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hAv : 0 < A * (4 * s.PAh ^ 2 * A - 4 * s.PAh * q * al + q ^ 2 * B) := by
    by_cases hq : q = 0
    · rw [hq]; nlinarith [mul_pos hA (mul_pos hA (sq_pos_of_pos hPA))]
    · have hq' : 0 < q ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * s.PAh * A - q * al), mul_pos (sub_pos.mpr hAB) hq']
  exact pos_of_mul_pos_right hAv hA.le


/-! ### The weak-shadow bounds at `u07` (`z4 >= z0`) and `u27` (`z2 >= z6`) -/

theorem u07_z40_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 4 - x 0, (x 0 - x 1) + omega3 x • (x 2 - x 1)⟫ := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3_pos : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  let u07 : ℝ³ := (x 0 - x 1) + omega3 x • (x 2 - x 1)
  have hz40 : ⟪x 4 - x 0, u07⟫ < 0 := hcon
  have hu07_ne : u07 ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at hz40; exact lt_irrefl _ hz40
  -- Facings at `(u07, x 6 - x 1, 0)` on `c := ![0, 2, 6, 4]`, `U := {2, 3, 7, 8}`, `Dn := {0, 4, 5}`:
  have hu0 : ⟪F.N 0, u07⟫ = 0 := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 0 (x 0) (x 1), ← F.hN 0 (x 2) (x 1),
      F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    ring
  have hu7 : ⟪F.N 7, u07⟫ = 0 := by
    have ev := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 7, u07⟫ = 0 := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 7 (x 0) (x 1), ← F.hN 7 (x 2) (x 1),
        F.zero 7 2 (by decide)]
      linear_combination -ev + F.f 7 (x 1) * e3
    exact (mul_eq_zero.mp hprod).resolve_left ha3.ne'
  have hu2 : 0 < ⟪F.N 2, u07⟫ := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 2 (x 0) (x 1), ← F.hN 2 (x 2) (x 1),
      F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    have : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
    nlinarith
  have hu3 : 0 < ⟪F.N 3, u07⟫ := by
    have ev := fac_eval F 3 3
    rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 3, u07⟫ =
        (oblX6 x 3 - 1) * F.f 3 (x 2) - oblX6 x 3 * F.f 3 (x 6) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 3 (x 0) (x 1), ← F.hN 3 (x 2) (x 1),
        F.zero 3 0 (by decide)]
      linear_combination -ev + (F.f 3 (x 1) - F.f 3 (x 2)) * e3
    have hpos : 0 < (oblX6 x 3 - 1) * F.f 3 (x 2) - oblX6 x 3 * F.f 3 (x 6) := by
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      nlinarith
    rw [← hprod] at hpos
    exact pos_of_mul_pos_right hpos ha3.le
  have hu8 : 0 < ⟪F.N 8, u07⟫ := by
    have ev := fac_eval F 8 3
    rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 8, u07⟫ = (oblX6 x 3 - 1) * F.f 8 (x 2) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 8 (x 0) (x 1), ← F.hN 8 (x 2) (x 1)]
      linear_combination -ev + (F.f 8 (x 1) - F.f 8 (x 2)) * e3
    have hpos : 0 < (oblX6 x 3 - 1) * F.f 8 (x 2) :=
      mul_pos_of_neg_of_neg (by linarith) (F.neg 8 2 (by decide))
    rw [← hprod] at hpos
    exact pos_of_mul_pos_right hpos ha3.le
  have hu4 : ⟪F.N 4, u07⟫ < 0 := by
    have ev := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have e4 := eq4 F
    have hprod : oblX2 x 4 * ⟪F.N 4, u07⟫ =
        oblX2 x 4 * F.f 4 (x 1) * (omega3 x * omega4 x - 1) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 4 (x 0) (x 1), ← F.hN 4 (x 2) (x 1),
        F.zero 4 0 (by decide)]
      linear_combination -omega3 x * ev + omega3 x * F.f 4 (x 1) * e4
    have hneg : oblX2 x 4 * F.f 4 (x 1) * (omega3 x * omega4 x - 1) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb4 (F.neg 4 1 (by decide))) (by linarith)
    rw [← hprod] at hneg
    by_contra h; push Not at h
    nlinarith [mul_nonneg hb4.le h]
  have hu5 : ⟪F.N 5, u07⟫ < 0 := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 2) (x 1),
      F.zero 5 1 (by decide), F.zero 5 2 (by decide), sub_zero, sub_self, mul_zero, add_zero]
    exact F.neg 5 0 (by decide)
  -- Front diagonal `24` over `06` at `u07`:
  set den : ℝ := (1 + omega3 x) + oblX2 x 4 * (omega3 x * omega4 x - 1)
  have hden_pos : 0 < den := by
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  set s : ℝ := (1 + omega3 x) / den
  set t : ℝ := s * oblX6 x 4
  set γ : ℝ := oblX2 x 4 * (1 + omega4 x) / den
  have hs0 : 0 < s := div_pos (by linarith) hden_pos
  have hs1 : s < 1 := by
    rw [div_lt_one hden_pos]
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  have ht0 : 0 < t := mul_pos hs0 hc4
  have ht1 : t < 1 := by
    have h236_4 : oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 < 1 := by
      have ev := fac_eval F 7 4
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
      have e3 := eq3 F
      have h70 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
        have ev3 := fac_eval F 7 3
        rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
        have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
          linear_combination -ev3 + F.f 7 (x 1) * e3
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')
      have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have hprod : (-F.f 7 (x 1)) * (oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 - 1) = F.f 7 (x 4) := by
        rw [ev, h70]; ring
      nlinarith [F.neg 7 4 (by decide)]
    -- From `h236_4` and `eq4 F`: `(1 + omega3) * c4 < (1 + omega3) + b4 * (omega3 * omega4 - 1) = den`!
    have hlt_den : (1 + omega3 x) * oblX6 x 4 < den := by
      have := eq4 F
      dsimp [den]
      nlinarith
    dsimp [t, s]
    rw [div_mul_eq_mul_div, div_lt_one hden_pos]
    exact hlt_den
  have hγ0 : 0 < γ := div_pos (mul_pos hb4 (by linarith)) hden_pos
  have hdiag_vec : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) = γ • u07 := by
    have hrep4 : x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
        oblX6 x 4 • (x 6 - x 1) := by rw [T.rep 4]; abel
    have hshift : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) =
        (1 - s) • (x 2 - x 1) + s • (x 4 - x 1) - (1 - t) • (x 0 - x 1) - t • (x 6 - x 1) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hshift, hrep4]
    have e4 := eq4 F
    have hden_ne : den ≠ 0 := hden_pos.ne'
    have c0 : s * oblX0 x 4 - (1 - t) = γ := by
      dsimp [s, t, γ]
      field_simp [hden_ne]
      dsimp [den]
      linear_combination (1 + omega3 x) * e4
    have c2 : (1 - s) + s * oblX2 x 4 = γ * omega3 x := by
      dsimp [s, γ]
      field_simp [hden_ne]
      dsimp [den]; ring
    have c6 : s * oblX6 x 4 - t = 0 := by dsimp [t]; ring
    dsimp [u07]
    calc (1 - s) • (x 2 - x 1) +
          s • (oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1)) -
          (1 - t) • (x 0 - x 1) - t • (x 6 - x 1)
        = (s * oblX0 x 4 - (1 - t)) • (x 0 - x 1) + ((1 - s) + s * oblX2 x 4) • (x 2 - x 1) +
          (s * oblX6 x 4 - t) • (x 6 - x 1) := by
          simp only [smul_add, smul_smul, add_smul, sub_smul]; abel
      _ = γ • (x 0 - x 1) + (γ * omega3 x) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
          rw [c0, c2, c6]
      _ = γ • ((x 0 - x 1) + omega3 x • (x 2 - x 1)) := by
          simp only [zero_smul, add_zero, smul_add, smul_smul]
  -- Take inner product with `u07`:
  have hdiag_pos : 0 < (1 - s) * (1 - t) * (⟪x 2, u07⟫ - ⟪x 0, u07⟫) +
      (1 - s) * t * (⟪x 2, u07⟫ - ⟪x 6, u07⟫) +
      s * (1 - t) * (⟪x 4, u07⟫ - ⟪x 0, u07⟫) +
      s * t * (⟪x 4, u07⟫ - ⟪x 6, u07⟫) := by
    have hinner := congrArg (fun w => ⟪w, u07⟫) hdiag_vec
    have hrhs : 0 < ⟪γ • u07, u07⟫ := by
      rw [real_inner_smul_left]
      exact mul_pos hγ0 (real_inner_self_pos.mpr hu07_ne)
    rw [← hinner] at hrhs
    have hlhs : ⟪(x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)), u07⟫ =
        (1 - s) * (1 - t) * (⟪x 2, u07⟫ - ⟪x 0, u07⟫) +
        (1 - s) * t * (⟪x 2, u07⟫ - ⟪x 6, u07⟫) +
        s * (1 - t) * (⟪x 4, u07⟫ - ⟪x 0, u07⟫) +
        s * t * (⟪x 4, u07⟫ - ⟪x 6, u07⟫) := by
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
    linarith
  have hex_pos : ∃ q ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), x 6 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), x 6 - x 1⟫, (0 : ℝ)) := by
    by_contra hno
    push Not at hno
    have h01 : ⟪x 2, u07⟫ - ⟪x 0, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h21 : ⟪x 2, u07⟫ - ⟪x 6, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h03 : ⟪x 4, u07⟫ - ⟪x 0, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h23 : ⟪x 4, u07⟫ - ⟪x 6, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr ht1),
      mul_pos (sub_pos.mpr hs1) ht0, mul_pos hs0 (sub_pos.mpr ht1), mul_pos hs0 ht0]
  have hex_neg : ∃ p ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), x 6 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), x 6 - x 1⟫, (0 : ℝ)) := by
    refine ⟨(0, 3), by decide, Or.inl ?_⟩
    simp only [Matrix.cons_val]
    rw [← sub_pos, ← inner_sub_left, show x 0 - x 4 = -(x 4 - x 0) from by abel, inner_neg_left]
    linarith [hz40]
  apply hL
  refine ⟨4, inferInstance, (![0, 2, 6, 4] : ZMod 4 → Fin 7), {2, 3, 7, 8}, {0, 4, 5},
    u07, x 6 - x 1, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_,
    by simpa [inner_zero_right] using robUniLex_four_of_mixed hex_pos hex_neg⟩
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · exact Or.inl (show 0 < ⟪F.N ⟨2, by decide⟩, u07⟫ from hu2)
    · exact Or.inl (show 0 < ⟪F.N ⟨3, by decide⟩, u07⟫ from hu3)
    · refine Or.inr ⟨show ⟪F.N ⟨7, by decide⟩, u07⟫ = 0 from hu7, Or.inl ?_⟩
      change 0 < ⟪F.N 7, x 6 - x 1⟫
      rw [← F.hN 7 (x 6) (x 1), F.zero 7 6 (by decide), zero_sub, neg_pos]
      exact F.neg 7 1 (by decide)
    · exact Or.inl (show 0 < ⟪F.N ⟨8, by decide⟩, u07⟫ from hu8)
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · refine Or.inr ⟨by linarith [show ⟪F.N ⟨0, by decide⟩, u07⟫ = 0 from hu0], Or.inl ?_⟩
      change 0 < -⟪F.N 0, x 6 - x 1⟫
      rw [← F.hN 0 (x 6) (x 1), F.zero 0 1 (by decide), sub_zero, neg_pos]
      exact F.neg 0 6 (by decide)
    · exact Or.inl (by linarith [show ⟪F.N ⟨4, by decide⟩, u07⟫ < 0 from hu4])
    · exact Or.inl (by linarith [show ⟪F.N ⟨5, by decide⟩, u07⟫ < 0 from hu5])


theorem inner_u27_z54 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u27 x⟫ = (1 + omega5 x) * (F.f t (x 0) - F.f t (x 1)) +
      (omega3 x * omega5 x - 1) * (F.f t (x 2) - F.f t (x 1)) +
      (1 + omega3 x) * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [u27, inner_add_right, real_inner_smul_right, ← F.hN t (x 0) (x 1),
    ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem u27_z26_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hu3 : 0 < ⟪F.N 3, u27 x⟫) (hu8 : 0 < ⟪F.N 8, u27 x⟫) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 2 - x 6, u27 x⟫ := by
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
    rw [inner_u27_z54, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    nlinarith [F.neg 0 6 (by decide)]
  have hu5 : ⟪F.N 5, u27 x⟫ < 0 := by
    rw [inner_u27_z54, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    nlinarith [F.neg 5 0 (by decide), mul_neg_of_pos_of_neg (show 0 < 1 + omega5 x by linarith)
      (F.neg 5 0 (by decide))]
  have hu2 : ⟪F.N 2, u27 x⟫ = 0 := by
    have ev := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
    have e5 := Minimality.T24.M4.eq5 F
    have hprod : oblX6 x 5 * ⟪F.N 2, u27 x⟫ = 0 := by
      rw [inner_u27_z54, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
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
    rw [inner_u27_z54, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    linear_combination (1 + omega5 x) * h70
  have hu4 : ⟪F.N 4, u27 x⟫ ≤ 0 := by
    have ev := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have e4 := Minimality.T24.M4.eq4 F
    have hprod : oblX2 x 4 * ⟪F.N 4, u27 x⟫ = oblX2 x 4 * (F.f 4 (x 1) * Delta24 x) := by
      rw [inner_u27_z54, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
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
    refine ⟨(2, 1), by decide, Or.inl ?_⟩
    simp only [Matrix.cons_val]
    rw [← sub_pos, ← inner_sub_left, show x 6 - x 2 = -(x 2 - x 6) from by abel, inner_neg_left]
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


/-! ### Translation to the corner frame -/

/-- Gram entries of the corner frame at vertex `1` (`G = [[A, -al, -be], [-al, B, -ga], [-be, -ga, C]]`). -/
noncomputable def gA (x : Fin 7 → ℝ³) : ℝ := ⟪x 0 - x 1, x 0 - x 1⟫
noncomputable def gB (x : Fin 7 → ℝ³) : ℝ := ⟪x 2 - x 1, x 2 - x 1⟫
noncomputable def gC (x : Fin 7 → ℝ³) : ℝ := ⟪x 6 - x 1, x 6 - x 1⟫
noncomputable def gal (x : Fin 7 → ℝ³) : ℝ := -⟪x 0 - x 1, x 2 - x 1⟫
noncomputable def gbe (x : Fin 7 → ℝ³) : ℝ := -⟪x 0 - x 1, x 6 - x 1⟫
noncomputable def gga (x : Fin 7 → ℝ³) : ℝ := -⟪x 2 - x 1, x 6 - x 1⟫

/-- The shape reals of `x` in the vertex-1 frame. -/
noncomputable def z54Shape (x : Fin 7 → ℝ³) : Z54Shape :=
  ⟨oblX0 x 4, oblX2 x 4, oblX6 x 4, oblX0 x 5, oblX2 x 5, oblX6 x 5, omega3 x, omega5 x⟩

theorem gram_expand (e0 e2 e6 : ℝ³) (p q r p' q' r' : ℝ) :
    ⟪p • e0 + q • e2 + r • e6, p' • e0 + q' • e2 + r' • e6⟫ =
      p * p' * ⟪e0, e0⟫ + q * q' * ⟪e2, e2⟫ + r * r' * ⟪e6, e6⟫
        - (p * q' + q * p') * (-⟪e0, e2⟫) - (p * r' + r * p') * (-⟪e0, e6⟫)
        - (q * r' + r * q') * (-⟪e2, e6⟫) := by
  have h20 : ⟪e2, e0⟫ = ⟪e0, e2⟫ := real_inner_comm _ _
  have h60 : ⟪e6, e0⟫ = ⟪e0, e6⟫ := real_inner_comm _ _
  have h62 : ⟪e6, e2⟫ = ⟪e2, e6⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h20, h60, h62]
  ring

theorem hrep_z54 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  rw [T.rep v]; abel

theorem z45_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 4 - x 5, x 5 - x 0⟫ =
      (z54Shape x).Z45 (gA x) (gB x) (gC x) (gal x) (gbe x) (gga x) := by
  have e1 : x 4 - x 5 = (oblX0 x 4 - oblX0 x 5) • (x 0 - x 1) + (oblX2 x 4 - oblX2 x 5) • (x 2 - x 1)
      + (oblX6 x 4 - oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 4 - x 5 = (x 4 - x 1) - (x 5 - x 1) by abel, hrep_z54 F 4, hrep_z54 F 5]; module
  have e2 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1)
      + oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep_z54 F 5]; module
  rw [e1, e2, gram_expand]
  simp only [z54Shape, Z54Shape.Z45, Z54Shape.Kal, Z54Shape.Kbe, Z54Shape.Kga, gA, gB, gC, gal, gbe, gga]
  ring

theorem u07_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 4 - x 0, (x 0 - x 1) + omega3 x • (x 2 - x 1)⟫ =
      (z54Shape x).U07 (gA x) (gB x) (gal x) (gbe x) (gga x) := by
  have e1 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1)
      + oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep_z54 F 4]; module
  have e2 : (x 0 - x 1) + omega3 x • (x 2 - x 1) =
      (1 : ℝ) • (x 0 - x 1) + omega3 x • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
  rw [e1, e2, gram_expand]
  simp only [z54Shape, Z54Shape.U07, gA, gB, gal, gbe, gga]
  ring

theorem u27_geom {x : Fin 7 → ℝ³} :
    ⟪x 2 - x 6, u27 x⟫ = (z54Shape x).U27 (gB x) (gC x) (gal x) (gbe x) (gga x) := by
  have e1 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  rw [e1]
  unfold u27
  rw [gram_expand]
  simp only [z54Shape, Z54Shape.U27, gB, gC, gal, gbe, gga]
  ring

theorem w26_geom {x : Fin 7 → ℝ³} (h : ⟪x 0 - x 1, x 2 - x 6⟫ ≤ 0) : gbe x ≤ gal x := by
  rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel, inner_sub_right] at h
  simp only [gbe, gal]; linarith

/-- The Gram quadratic form at `v = (p, q)`: `A p^2 - 2 al p q + B q^2 = ‖p e0 + q e2‖^2`. -/
theorem quad_geom {x : Fin 7 → ℝ³} (p q : ℝ) :
    ⟪p • (x 0 - x 1) + q • (x 2 - x 1), p • (x 0 - x 1) + q • (x 2 - x 1)⟫ =
      p ^ 2 * gA x - 2 * p * q * gal x + q ^ 2 * gB x := by
  have h20 : ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h20,
    gA, gB, gal]
  ring

/-! ### Sample facts and the geometric step -/

/-- `0 < ⟪F.N 3, u27 x⟫` on `Reg.A1` (region fact: `lam5_pos_of_sigma`, `d45_pos`, `F.f 2 (x 3) < 0`). -/
theorem hu3_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F) :
    0 < ⟪F.N 3, u27 x⟫ := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hLam : 0 < Lam5 x := lam5_pos_of_sigma F hA1.2
  have hD45 : 0 < D45 x := d45_pos F
  obtain ⟨s, t, hs, ht, -, -, hb3, hc3⟩ := lemmaM_coords F
  have hD35 : oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5 = s * D45 x := by
    rw [hb3, hc3]; dsimp [D45]; ring
  have hD35_pos : 0 < oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5 := by
    rw [hD35]; exact mul_pos hs hD45
  have e33 := fac_eval F 3 3
  have e35 := fac_eval F 3 5
  rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at e33
  rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e35
  have e23 := fac_eval F 2 3
  have e25 := fac_eval F 2 5
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e23
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e25
  have h23_prod : (oblX6 x 5 * (1 - oblX0 x 3 - oblX2 x 3 - oblX6 x 3) +
      oblX6 x 3 * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) * (-F.f 2 (x 1)) =
      oblX6 x 5 * (-F.f 2 (x 3)) := by
    linear_combination oblX6 x 5 * e23 - oblX6 x 3 * e25
  have h23_pos : 0 < oblX6 x 5 * (1 - oblX0 x 3 - oblX2 x 3 - oblX6 x 3) +
      oblX6 x 3 * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by
    by_contra hle; push Not at hle
    have hlhs := mul_nonpos_of_nonpos_of_nonneg hle (neg_nonneg.2 (F.neg 2 1 (by decide)).le)
    have hrhs := mul_pos hc5 (neg_pos.2 (F.neg 2 3 (by decide)))
    linarith
  have hf32 : F.f 3 (x 2) - F.f 3 (x 1) =
      ((1 - oblX0 x 3) * oblX6 x 5 - (1 - oblX0 x 5) * oblX6 x 3) * F.f 3 (x 1) /
        (oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5) := by
    rw [eq_div_iff hD35_pos.ne']
    linear_combination oblX6 x 5 * e33 - oblX6 x 3 * e35
  have hf36 : F.f 3 (x 6) - F.f 3 (x 1) =
      (oblX2 x 3 * (1 - oblX0 x 5) - oblX2 x 5 * (1 - oblX0 x 3)) * F.f 3 (x 1) /
        (oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5) := by
    rw [eq_div_iff hD35_pos.ne']
    linear_combination oblX2 x 3 * e35 - oblX2 x 5 * e33
  have hom3 : omega3 x = (oblX2 x 3 + oblX6 x 3 - 1) / oblX0 x 3 := by
    rw [eq_div_iff ha3.ne']; linear_combination -Minimality.T24.M4.eq3 F
  have hom5 : omega5 x = (oblX0 x 5 + oblX2 x 5 - 1) / oblX6 x 5 := by
    rw [eq_div_iff hc5.ne']; linear_combination -Minimality.T24.M4.eq5 F
  have hid : oblX0 x 3 * oblX6 x 5 * (oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5) *
      ⟪F.N 3, u27 x⟫ =
      (-F.f 3 (x 1)) * (oblX0 x 3 * Lam5 x) *
        (oblX6 x 5 * (1 - oblX0 x 3 - oblX2 x 3 - oblX6 x 3) +
          oblX6 x 3 * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) := by
    rw [inner_u27_z54, F.zero 3 0 (by decide), hf32, hf36]
    dsimp [Lam5]
    rw [hom3, hom5]
    have hD35' : oblX2 x 5 * oblX6 x 3 - oblX6 x 5 * oblX2 x 3 ≠ 0 := by linarith
    field_simp [ha3.ne', hc5.ne', hD35_pos.ne', hD35']
    ring
  have hprod : 0 < oblX0 x 3 * oblX6 x 5 * (oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5) *
      ⟪F.N 3, u27 x⟫ := by
    rw [hid]
    exact mul_pos (mul_pos (neg_pos.2 (F.neg 3 1 (by decide))) (mul_pos ha3 hLam)) h23_pos
  exact pos_of_mul_pos_right hprod (mul_pos (mul_pos ha3 hc5) hD35_pos).le

/-- Sample facts for the off-tie A1 step `z54`: the `227/227` facts of A22-REFEREE (`c4 > c5`, `Qgah <= 0`) and
the `226/227` residual `4 PAh PBh >= max(0, Qalh)^2` (fails only at `r391`), plus the remaining facings
`c3 < 1`, `0 < <N8, u27>` (`227/227`) that the weak-shadow bounds need. -/
structure A1Z54Sample (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop where
  hc3 : oblX6 x 3 < 1
  hu8 : 0 < ⟪F.N 8, u27 x⟫
  hc45 : oblX6 x 5 < oblX6 x 4
  hQg : (z54Shape x).Qgah ≤ 0
  hQ : max 0 (z54Shape x).Qalh ^ 2 ≤ 4 * (z54Shape x).PAh * (z54Shape x).PBh

/-- **Step T2 (`z54_A1`)**: on `A1` with `OB1`, `4 < 5` at the view `w05 = x5 - x0`. -/
theorem z54_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hnQ45 : ¬ Q45HalfPred F) (hC : CbarIn x) (hO : H24K.SAT.OB1 x) (hL : ¬ LexAny F)
    (hS : A1Z54Sample x F) : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hZ : 0 ≤ (z54Shape x).Z45 (gA x) (gB x) (gC x) (gal x) (gbe x) (gga x) := by
    rw [← z45_geom F, inner_sub_left]; linarith
  have ha5 : 1 < oblX0 x 5 := hA1.1
  have ha4 : oblX0 x 4 ≤ 1 := a4_le_of_hA1 F hA1 hnQ45
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hom3 : 0 < omega3 x := hC.1
  have hLam : 0 < (z54Shape x).Lam5 := lam5_pos_of_sigma F hA1.2
  have hom5 : (z54Shape x).a5 + (z54Shape x).b5 - 1 = (z54Shape x).om5 * (z54Shape x).c5 := eq5 F
  have hU07 : 0 ≤ (z54Shape x).U07 (gA x) (gB x) (gal x) (gbe x) (gga x) := by
    rw [← u07_geom F]; exact u07_z40_bound F hC hS.hc3 hL
  have hU27 : 0 ≤ (z54Shape x).U27 (gB x) (gC x) (gal x) (gbe x) (gga x) := by
    rw [← u27_geom]; exact u27_z26_bound F hC (hu3_of_region F hA1) hS.hu8 hL
  -- W26
  have hnC : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp (nC_pos_of F ha4 ha5)
  have hnB : F.f 3 (x 2) < F.f 3 (x 1) := by
    have hlin := (fac3_lin F).2
    have hnB0 : nB x < 0 := by
      dsimp [nB]; nlinarith
    have hD : 0 < D45 x := d45_pos F
    have h1 : 0 < -F.f 3 (x 1) := by linarith [F.neg 3 1 (by decide)]
    by_contra hge; push Not at hge
    nlinarith [mul_nonneg (sub_nonneg.mpr hge) hD.le, mul_pos h1 (neg_pos.mpr hnB0)]
  have hW : gbe x ≤ gal x := w26_geom (w26_bound F hC hO.2.2 (lt_trans hnB hnC) hL)
  have hal : 0 ≤ gal x := by simp only [gal]; linarith [hO.1]
  have hga : 0 ≤ gga x := by simp only [gga]; linarith [hO.2.2]
  have hB : 0 ≤ gB x := real_inner_self_nonneg
  -- positivity of the quadratic form at `v = (2 PAh, max 0 Qalh)`
  have hPA := (z54Shape x).PAh_pos hom5 ha5 ha4 hc5 hom3 hLam hS.hc45
  have hv : 0 < 4 * (z54Shape x).PAh ^ 2 * gA x
      - 4 * (z54Shape x).PAh * max 0 (z54Shape x).Qalh * gal x
      + max 0 (z54Shape x).Qalh ^ 2 * gB x := by
    set p : ℝ := 2 * (z54Shape x).PAh
    set q : ℝ := max 0 (z54Shape x).Qalh
    have hp : 0 < p := by simp only [p]; linarith
    have hN : ⟪F.N 5, p • (x 0 - x 1) + q • (x 2 - x 1)⟫ < 0 := by
      rw [inner_add_right, inner_smul_right, inner_smul_right, ← F.hN 5 (x 0) (x 1),
        ← F.hN 5 (x 2) (x 1), F.zero 5 1 (by decide), F.zero 5 2 (by decide)]
      have := F.neg 5 0 (by decide)
      nlinarith
    have hne : p • (x 0 - x 1) + q • (x 2 - x 1) ≠ 0 := by
      intro h0; rw [h0, inner_zero_right] at hN; exact lt_irrefl _ hN
    have := real_inner_self_pos.mpr hne
    rw [quad_geom] at this
    simp only [p] at this ⊢
    nlinarith
  exact (z54Shape x).half_core (gA x) (gB x) (gC x) (gal x) (gbe x) (gga x) hom5 ha5 ha4 hc5 hom3
    hLam hS.hc45 hS.hQg hS.hQ hZ hU27 hU07 hW hal hga hB hv

/-- **Off-tie A1 (`a1_offtie_rupert`)**: `Hole24R`, `A1`, `OB1`, strictly off the tie, and the sample bundles
`A1E25Sample`, `A1Z54Sample` are contradictory. -/
theorem a1_offtie_rupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x)
    (hntie : ⟪x 2 - x 5, x 5 - x 0⟫ ≠ 0) (hS25 : A1E25Sample x F) (hS54 : A1Z54Sample x F) :
    False := by
  have hlt := a1_e25_lt F hR hA1 hO hS25 hntie
  have hz := z54_A1 F hA1 hR.2.2.1 hR.1 hO hR.2.2.2.2.1 hS54
  have hA4 := a4_le_of_hA1 F hA1 hR.2.2.1
  rcases E05P5U_A1 F hR.1 hA1.1 hA4 hA1.2 ⟨hz, hlt⟩ with h | h
  · exact hR.2.2.2.2.1 h
  · exact hR.2.2.2.2.2 h

end Minimality.T24.A1
