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
  obtain ⟨hU, hD⟩ := Minimality.T24.M4.u07_facings F hC hc3
  have hw := Minimality.T24.M4.weak_shadow_of_frontDiag F ![0, 2, 6, 4]
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    {2, 3, 7, 8} {0, 4, 5} (by unfold S0xCycUD; decide)
    ((x 0 - x 1) + omega3 x • (x 2 - x 1)) (x 6 - x 1) 0
    (by simpa [inner_zero_right] using hU)
    (by simpa [inner_zero_right] using hD)
    (Minimality.T24.M4.u07_frontDiag F hC) (i := 3) (j := 0) (by decide) hL
  simpa only [Matrix.cons_val] using hw


theorem inner_u27_z54 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u27 x⟫ = (1 + omega5 x) * (F.f t (x 0) - F.f t (x 1)) +
      (omega3 x * omega5 x - 1) * (F.f t (x 2) - F.f t (x 1)) +
      (1 + omega3 x) * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [u27, inner_add_right, real_inner_smul_right, ← F.hN t (x 0) (x 1),
    ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem u27_z26_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hu3 : 0 < ⟪F.N 3, u27 x⟫) (hu8 : 0 < ⟪F.N 8, u27 x⟫) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 2 - x 6, u27 x⟫ := by
  obtain ⟨hU, hD⟩ := u27_facings F hC hu3 hu8
  have hw := Minimality.T24.M4.weak_shadow_of_frontDiag F ![0, 2, 6, 4]
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    {2, 3, 7, 8} {0, 4, 5} (by unfold S0xCycUD; decide)
    (u27 x) (x 2 - x 1) 0
    (by simpa [inner_zero_right] using hU)
    (by simpa [inner_zero_right] using hD)
    (u27_bound F hC) (i := 1) (j := 2) (by decide) hL
  simpa only [Matrix.cons_val] using hw


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
