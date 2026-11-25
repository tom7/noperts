module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top

/-!
# Type 24: the 4-rim pieces I and III of circle 236 in the hidden-cap cone

Formalizes the closed-cell region lemmas (`(i)`) and Q4 leaves (`(ii)`) for the two 4-rim pieces
of circle `236` (`0 5 2 6` = piece I, `0 2 6 4` = piece III) in `Minimality.T24.EG`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EG

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

/-! ## Cells and cycles -/

/-- Up facets of the piece-I cell (rim `0 5 2 6`): `0345, 046, 235, 236, 346`. -/
def UI : Finset (Fin 9) := {3, 4, 6, 7, 8}
/-- Down facets of the piece-I cell: `012, 016, 025, 126`. -/
def DnI : Finset (Fin 9) := {0, 1, 2, 5}
/-- Rim cycle of piece I. -/
def cI : ZMod 4 → Fin 7 := ![0, 5, 2, 6]

/-- Up facets of the piece-III cell (rim `0 2 6 4`): `025, 0345, 235, 236, 346`. -/
def UIII : Finset (Fin 9) := {2, 3, 6, 7, 8}
/-- Down facets of the piece-III cell: `012, 016, 046, 126`. -/
def DnIII : Finset (Fin 9) := {0, 1, 4, 5}
/-- Rim cycle of piece III. -/
def cIII : ZMod 4 → Fin 7 := ![0, 2, 6, 4]

theorem cycI : S0xCycUD s0x_S24 cI UI DnI := by decide
theorem cycIII : S0xCycUD s0x_S24 cIII UIII DnIII := by decide

theorem injI : Function.Injective cI := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injIII : Function.Injective cIII := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## The shape-only end views -/

/-- Wall end `c_0` of piece I, scaled by `ω3`: `(1, 0, ω3)` (on plane `016`, `cb = 0`). -/
noncomputable def wallI (x : Fin 7 → ℝ³) : ℝ³ := capView x 1 0 (omega3 x)
/-- `M74 = N_7 × N_4 = (1 + ω4, 1 + ω3, ω3 ω4 - 1)`: facets `236` and `046` edge-on. -/
noncomputable def viewM74 (x : Fin 7 → ℝ³) : ℝ³ :=
  capView x (1 + omega4 x) (1 + omega3 x) (omega3 x * omega4 x - 1)
/-- `M27 = N_2 × N_7 = (1 + ω5, ω3 ω5 - 1, 1 + ω3)`: facets `025` and `236` edge-on. -/
noncomputable def viewM27 (x : Fin 7 → ℝ³) : ℝ³ :=
  capView x (1 + omega5 x) (omega3 x * omega5 x - 1) (1 + omega3 x)
/-- Wall end `c_∞` of piece III, scaled by `ω3`: `(1, ω3, 0)` (on plane `012`, `cc = 0`). -/
noncomputable def wallIII (x : Fin 7 → ℝ³) : ℝ³ := capView x 1 (omega3 x) 0

/-- Left end of piece I: `c_0` if `b3 ≤ 1`, else the edge view `u_32 = x 3 - x 2`. -/
noncomputable def endIL (x : Fin 7 → ℝ³) : ℝ³ := if oblX2 x 3 ≤ 1 then wallI x else x 3 - x 2
/-- Right end of piece III: `c_∞` if `c3 ≤ 1`, else the edge view `u_36 = x 3 - x 6`. -/
noncomputable def endIIIR (x : Fin 7 → ℝ³) : ℝ³ := if oblX6 x 3 ≤ 1 then wallIII x else x 3 - x 6

/-! ## Private algebraic helpers -/

private theorem rep_sub (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
  have h := (M4.type24OfFac F).rep v
  rw [sub_eq_iff_eq_add, h]; abel

private theorem inner_capView_0 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 0, capView x ca cb cc⟫ = cc * F.f 0 (x 6) := by
  obtain ⟨⟨a0, b0, _⟩, _, _⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, a0, b0]
  rw [F.inner_sub, F.zero 0 1 (by decide)]; ring

private theorem inner_capView_1 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 1, capView x ca cb cc⟫ = cb * F.f 1 (x 2) := by
  obtain ⟨_, ⟨a1, c1, _⟩, _⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, a1, c1]
  rw [F.inner_sub, F.zero 1 1 (by decide)]; ring

private theorem inner_capView_5 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 5, capView x ca cb cc⟫ = ca * F.f 5 (x 0) := by
  obtain ⟨_, _, ⟨b5, c5, _⟩⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, b5, c5]
  rw [F.inner_sub, F.zero 5 1 (by decide)]; ring

private theorem inner_capView_7 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 7, capView x ca cb cc⟫ = (-F.f 7 (x 1)) * (-omega3 x * ca + cb + cc) := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ev := M4.fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
  have e3 := M4.eq3 F
  have hprod : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
    linear_combination -ev + F.f 7 (x 1) * e3
  have hd0 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
    have := (mul_eq_zero.mp hprod).resolve_left ha3.ne'
    linarith
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 7 2 (by decide), F.zero 7 6 (by decide), hd0]
  ring

private theorem inner_capView_4 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 4, capView x ca cb cc⟫ = (-F.f 4 (x 1)) * (ca - omega4 x * cb + cc) := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have ev := M4.fac_eval F 4 4
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
  have e4 := M4.eq4 F
  have hprod : oblX2 x 4 * ((F.f 4 (x 2) - F.f 4 (x 1)) - omega4 x * F.f 4 (x 1)) = 0 := by
    linear_combination -ev + F.f 4 (x 1) * e4
  have hd2 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
    have := (mul_eq_zero.mp hprod).resolve_left hb4.ne'
    linarith
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 4 0 (by decide), F.zero 4 6 (by decide), hd2]
  ring

private theorem inner_capView_2 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 2, capView x ca cb cc⟫ = (-F.f 2 (x 1)) * (ca + cb - omega5 x * cc) := by
  have T := M4.type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ev := M4.fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
  have e5 := M4.eq5 F
  have hprod : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - omega5 x * F.f 2 (x 1)) = 0 := by
    linear_combination -ev + F.f 2 (x 1) * e5
  have hd6 : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
    have := (mul_eq_zero.mp hprod).resolve_left hc5.ne'
    linarith
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 2 0 (by decide), F.zero 2 2 (by decide), hd6]
  ring

private theorem inner_wallI_368 (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ∈ ({3, 6, 8} : Finset (Fin 9))) :
    oblX0 x 3 * ⟪F.N t, wallI x⟫ = (oblX2 x 3 - 1) * F.f t (x 6) - oblX2 x 3 * F.f t (x 2) := by
  have ht3 : 3 ∈ s0x_S24 t := by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  have ev := M4.fac_eval F t 3
  rw [F.zero t 3 ht3] at ev
  have e3 := M4.eq3 F
  dsimp [wallI, capView]
  simp only [inner_add_right, real_inner_smul_right, F.inner_sub]
  linear_combination -ev + (F.f t (x 1) - F.f t (x 6)) * e3

private theorem inner_wallIII_368 (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ∈ ({3, 6, 8} : Finset (Fin 9))) :
    oblX0 x 3 * ⟪F.N t, wallIII x⟫ = (oblX6 x 3 - 1) * F.f t (x 2) - oblX6 x 3 * F.f t (x 6) := by
  have ht3 : 3 ∈ s0x_S24 t := by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  have ev := M4.fac_eval F t 3
  rw [F.zero t 3 ht3] at ev
  have e3 := M4.eq3 F
  dsimp [wallIII, capView]
  simp only [inner_add_right, real_inner_smul_right, F.inner_sub]
  linear_combination -ev + (F.f t (x 1) - F.f t (x 2)) * e3

private theorem det_ratio_pos (F : S0xFac 9 s0x_S24 x) {N A B u v : ℝ³}
    (hA : ⟪N, A⟫ = 0) (hB : ⟪N, B⟫ = 0) (hv : ⟪N, v⟫ < 0)
    {du dv : ℝ} (hdu : det3 A B u = du * det24 x) (hdv : det3 A B v = dv * det24 x)
    (hdu_neg : du < 0) (hdv_pos : 0 < dv) : 0 < ⟪N, u⟫ := by
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hv; linarith
  have hNN : 0 < ⟪N, N⟫ := real_inner_self_pos.2 hN0
  have hdet24 : det24 x ≠ 0 := (M4.type24OfFac F).det_ne
  have e1 := det_perp' A B u N hA hB
  have e2 := det_perp' A B v N hA hB
  rw [hdu] at e1
  rw [hdv] at e2
  have hABN : det3 A B N ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e2
    have h1 : dv * det24 x * ⟪N, N⟫ ≠ 0 := mul_ne_zero (mul_ne_zero hdv_pos.ne' hdet24) hNN.ne'
    exact h1 e2
  have hprod : det3 A B N * (dv * ⟪N, u⟫ - du * ⟪N, v⟫) = 0 := by
    linear_combination -dv * e1 + du * e2
  have heq : dv * ⟪N, u⟫ = du * ⟪N, v⟫ := by
    linarith [(mul_eq_zero.mp hprod).resolve_left hABN]
  nlinarith

private theorem det_same_neg (F : S0xFac 9 s0x_S24 x) {N A B u v : ℝ³}
    (hA : ⟪N, A⟫ = 0) (hB : ⟪N, B⟫ = 0) (hu : ⟪N, u⟫ < 0) (hv : ⟪N, v⟫ < 0)
    {du dv : ℝ} (hdu : det3 A B u = du * det24 x) (hdv : det3 A B v = dv * det24 x)
    (hdv_neg : dv < 0) : du < 0 := by
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hv; linarith
  have hNN : 0 < ⟪N, N⟫ := real_inner_self_pos.2 hN0
  have hdet24 : det24 x ≠ 0 := (M4.type24OfFac F).det_ne
  have e1 := det_perp' A B u N hA hB
  have e2 := det_perp' A B v N hA hB
  rw [hdu] at e1
  rw [hdv] at e2
  have hABN : det3 A B N ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e2
    have h1 : dv * det24 x * ⟪N, N⟫ ≠ 0 := mul_ne_zero (mul_ne_zero hdv_neg.ne hdet24) hNN.ne'
    exact h1 e2
  have hprod : det3 A B N * (dv * ⟪N, u⟫ - du * ⟪N, v⟫) = 0 := by
    linear_combination -dv * e1 + du * e2
  have heq : dv * ⟪N, u⟫ = du * ⟪N, v⟫ := by
    linarith [(mul_eq_zero.mp hprod).resolve_left hABN]
  nlinarith

/-! ## (i) Region lemmas

Nondegeneracy hypotheses of the edge cases (gate: necessary and sufficient on the pool):
* piece I: `h4 : 0 < ⟪F.N 4, x 3 - x 2⟫` (facet `046` faces front at `u_32`; in corner coordinates
  `a3 - ω4 (b3 - 1) + c3 > 0`, i.e. `s74 > 0`: `M74` comes after `u_32` on the pencil).  Automatic when
  `b3 ≤ 1` (`h4_of_b3_le`).  When it fails (`1 < b3`, `s74 ≤ 0`) the chord-26 sector has no piece I.
* piece III: `h2 : 0 < ⟪F.N 2, x 3 - x 6⟫` (facet `025` faces front at `u_36`; `a3 + b3 - ω5 (c3 - 1) > 0`,
  i.e. `s27 < 1`).  Automatic when `c3 ≤ 1` (`h2_of_c3_le`). -/

private theorem h4_equiv (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 4, x 3 - x 2⟫ = (-F.f 4 (x 1)) * (oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + oblX6 x 3) := by
  have hrep : x 3 - x 2 = capView x (oblX0 x 3) (oblX2 x 3 - 1) (oblX6 x 3) := by
    have h3 := rep_sub F 3
    dsimp [capView]
    rw [show x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) by abel, h3]
    module
  rw [hrep, inner_capView_4]

private theorem h2_equiv (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 2, x 3 - x 6⟫ = (-F.f 2 (x 1)) * (oblX0 x 3 + oblX2 x 3 - omega5 x * (oblX6 x 3 - 1)) := by
  have hrep : x 3 - x 6 = capView x (oblX0 x 3) (oblX2 x 3) (oblX6 x 3 - 1) := by
    have h3 := rep_sub F 3
    dsimp [capView]
    rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by abel, h3]
    module
  rw [hrep, inner_capView_2]

/-- `046` faces front at `u_32` when `b3 ≤ 1`. -/
theorem h4_of_b3_le (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb : oblX2 x 3 ≤ 1) :
    0 < ⟪F.N 4, x 3 - x 2⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hom4 : 0 < omega4 x := hC.2.1
  have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
  rw [h4_equiv F]
  exact mul_pos hk4 (by nlinarith)

/-- `025` faces front at `u_36` when `c3 ≤ 1`. -/
theorem h2_of_c3_le (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hc : oblX6 x 3 ≤ 1) :
    0 < ⟪F.N 2, x 3 - x 6⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
  rw [h2_equiv F]
  exact mul_pos hk2 (by nlinarith)

private theorem viewM74_6_pos (F : S0xFac 9 s0x_S24 x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    0 < ⟪F.N 6, viewM74 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
  have h4' : 0 < oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + oblX6 x 3 := by
    rw [h4_equiv F] at h4
    exact (mul_pos_iff_of_pos_left hk4).mp h4
  have hdecomp : viewM74 x = (1 + omega4 x) • wallI x + (1 + omega3 x) • (x 2 - x 6) := by
    dsimp [viewM74, wallI, capView]
    rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel]
    module
  have hwall := inner_wallI_368 F (t := 6) (by decide)
  rw [F.zero 6 2 (by decide)] at hwall
  have h26 : ⟪F.N 6, x 2 - x 6⟫ = -F.f 6 (x 6) := by
    rw [F.inner_sub, F.zero 6 2 (by decide)]; ring
  have e3 := M4.eq3 F
  have hprod : oblX0 x 3 * ⟪F.N 6, viewM74 x⟫ =
      (oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + oblX6 x 3) * (-F.f 6 (x 6)) := by
    rw [hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right, h26]
    linear_combination (1 + omega4 x) * hwall - (-F.f 6 (x 6)) * e3
  have hf6 : 0 < -F.f 6 (x 6) := by linarith [F.neg 6 6 (by decide)]
  exact pos_of_mul_pos_right (by rw [hprod]; exact mul_pos h4' hf6) ha3.le

private theorem viewM74_8_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 8, viewM74 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have e3 := M4.eq3 F
  have e4 := M4.eq4 F
  have hlt3 := T.lt046 (v := 3) (by decide)
  have hlt4 := T.lt236 (v := 4) (by decide)
  have hf1 : (1 + omega3 x) * oblX0 x 3 - (1 + omega4 x) * oblX2 x 3 < 0 := by linarith
  have hf2 : 0 < (1 + omega3 x) * oblX0 x 4 - (1 + omega4 x) * oblX2 x 4 := by linarith
  have hA : ⟪F.N 8, x 3 - x 6⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 3 (by decide), F.zero 8 6 (by decide), sub_self]
  have hB : ⟪F.N 8, x 4 - x 6⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 6 (by decide), sub_self]
  have hv : ⟪F.N 8, x 2 - x 6⟫ < 0 := by
    rw [F.inner_sub, F.zero 8 6 (by decide), sub_zero]; exact F.neg 8 2 (by decide)
  have hA_rep : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      (oblX6 x 3 - 1) • (x 6 - x 1) := by
    rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by abel, rep_sub F 3]; module
  have hB_rep : x 4 - x 6 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      (oblX6 x 4 - 1) • (x 6 - x 1) := by
    rw [show x 4 - x 6 = (x 4 - x 1) - (x 6 - x 1) by abel, rep_sub F 4]; module
  have hv_rep : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) +
      (-1 : ℝ) • (x 6 - x 1) := by
    rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel]; module
  set du := ((1 + omega3 x) * oblX0 x 4 - (1 + omega4 x) * oblX2 x 4) *
    ((1 + omega3 x) * oblX0 x 3 - (1 + omega4 x) * oblX2 x 3)
  set dv := oblX0 x 3 * (omega3 x * oblX0 x 4 - (oblX2 x 4 + oblX6 x 4 - 1))
  have hdu_alg : oblX0 x 3 * (oblX2 x 4 * (omega3 x * omega4 x - 1) - (oblX6 x 4 - 1) * (1 + omega3 x)) -
      oblX2 x 3 * (oblX0 x 4 * (omega3 x * omega4 x - 1) - (oblX6 x 4 - 1) * (1 + omega4 x)) +
      (oblX6 x 3 - 1) * (oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) = du := by
    dsimp [du]
    linear_combination (oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) * e3 -
      (oblX0 x 3 * (1 + omega3 x) - oblX2 x 3 * (1 + omega4 x)) * e4
  have hdu : det3 (x 3 - x 6) (x 4 - x 6) (viewM74 x) = du * det24 x := by
    rw [hA_rep, hB_rep]; dsimp [viewM74, capView]; rw [M4.det3_frame, hdu_alg]
  have hdv_alg : oblX0 x 3 * (oblX2 x 4 * (-1) - (oblX6 x 4 - 1) * 1) -
      oblX2 x 3 * (oblX0 x 4 * (-1) - (oblX6 x 4 - 1) * 0) +
      (oblX6 x 3 - 1) * (oblX0 x 4 * 1 - oblX2 x 4 * 0) = dv := by
    dsimp [dv]
    linear_combination oblX0 x 4 * e3
  have hdv : det3 (x 3 - x 6) (x 4 - x 6) (x 2 - x 6) = dv * det24 x := by
    rw [hA_rep, hB_rep, hv_rep, M4.det3_frame, hdv_alg]
  have hdu_neg : du < 0 := mul_neg_of_pos_of_neg hf2 hf1
  have hdv_pos : 0 < dv := mul_pos ha3 (by linarith)
  exact det_ratio_pos F hA hB hv hdu hdv hdu_neg hdv_pos

private theorem viewM74_3_pos (F : S0xFac 9 s0x_S24 x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    0 < ⟪F.N 3, viewM74 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
  have h4' : 0 < oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + oblX6 x 3 := by
    rw [h4_equiv F] at h4
    exact (mul_pos_iff_of_pos_left hk4).mp h4
  have e3 := M4.eq3 F
  have e4 := M4.eq4 F
  have hlt3 := T.lt046 (v := 3) (by decide)
  have hA : ⟪F.N 3, x 3 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 0 (by decide), sub_self]
  have hB : ⟪F.N 3, x 4 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
  have hv2 : ⟪F.N 3, x 2 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 2 (by decide)
  have hv6 : ⟪F.N 3, x 6 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 6 (by decide)
  have hA_rep : x 3 - x 0 = (oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by
    rw [show x 3 - x 0 = (x 3 - x 1) - (x 0 - x 1) by abel, rep_sub F 3]; module
  have hB_rep : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, rep_sub F 4]; module
  have hv2_rep : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) +
      (0 : ℝ) • (x 6 - x 1) := by
    rw [show x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) by abel]; module
  have hv6_rep : x 6 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) +
      (1 : ℝ) • (x 6 - x 1) := by
    rw [show x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) by abel]; module
  set d2 := -(1 + omega3 x) * oblX0 x 3 * oblX6 x 4 + (1 + omega4 x) * oblX2 x 4 * oblX6 x 3
  set d6 := oblX2 x 4 * (oblX0 x 3 + oblX6 x 3 - 1 - omega4 x * oblX2 x 3)
  have hd2_alg : (oblX0 x 3 - 1) * (oblX2 x 4 * 0 - oblX6 x 4 * 1) -
      oblX2 x 3 * ((oblX0 x 4 - 1) * 0 - oblX6 x 4 * (-1)) +
      oblX6 x 3 * ((oblX0 x 4 - 1) * 1 - oblX2 x 4 * (-1)) = d2 := by
    dsimp [d2]
    linear_combination -oblX6 x 4 * e3 + oblX6 x 3 * e4
  have hd2 : det3 (x 3 - x 0) (x 4 - x 0) (x 2 - x 0) = d2 * det24 x := by
    rw [hA_rep, hB_rep, hv2_rep, M4.det3_frame, hd2_alg]
  have hd6_alg : (oblX0 x 3 - 1) * (oblX2 x 4 * 1 - oblX6 x 4 * 0) -
      oblX2 x 3 * ((oblX0 x 4 - 1) * 1 - oblX6 x 4 * (-1)) +
      oblX6 x 3 * ((oblX0 x 4 - 1) * 0 - oblX2 x 4 * (-1)) = d6 := by
    dsimp [d6]
    linear_combination -oblX2 x 3 * e4
  have hd6 : det3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) = d6 * det24 x := by
    rw [hA_rep, hB_rep, hv6_rep, M4.det3_frame, hd6_alg]
  have hd6_neg : d6 < 0 := mul_neg_of_pos_of_neg hb4 (by linarith)
  have hd2_neg : d2 < 0 := det_same_neg F hA hB hv2 hv6 hd2 hd6 hd6_neg
  have hgap_eq : (1 + omega4 x) * (1 + omega3 x * oblX0 x 3 - oblX2 x 3) -
      (omega3 x * omega4 x - 1) * oblX0 x 3 =
      oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + (1 + omega3 x * oblX0 x 3 - oblX2 x 3) := by ring
  rw [show 1 + omega3 x * oblX0 x 3 - oblX2 x 3 = oblX6 x 3 by linarith] at hgap_eq
  have hgap : (omega3 x * omega4 x - 1) * oblX0 x 3 < (1 + omega4 x) * oblX6 x 3 := by
    linarith only [h4', hgap_eq]
  have hprod_gap : (omega3 x * omega4 x - 1) * oblX0 x 3 * oblX2 x 4 <
      (1 + omega4 x) * oblX6 x 3 * oblX2 x 4 := mul_lt_mul_of_pos_right hgap hb4
  have hprod_d2 : (1 + omega4 x) * oblX6 x 3 * oblX2 x 4 <
      (1 + omega3 x) * oblX0 x 3 * oblX6 x 4 := by linarith only [hprod_gap, hd2_neg]
  have h_a4_b4 : (omega3 x * omega4 x - 1) * oblX2 x 4 < (1 + omega3 x) * oblX6 x 4 := by
    have : oblX0 x 3 * ((omega3 x * omega4 x - 1) * oblX2 x 4) <
        oblX0 x 3 * ((1 + omega3 x) * oblX6 x 4) := by linarith only [hprod_gap, hprod_d2]
    exact lt_of_mul_lt_mul_left this ha3.le
  have hf_a4_eq : (1 + omega3 x) * (oblX0 x 4 - 1) - (1 + omega4 x) * oblX2 x 4 =
      (omega3 x * omega4 x - 1) * oblX2 x 4 - (1 + omega3 x) * oblX6 x 4 +
      (1 + omega3 x) * (oblX0 x 4 + oblX6 x 4 - 1 - omega4 x * oblX2 x 4) := by ring
  rw [sub_eq_zero.mpr e4, mul_zero, add_zero] at hf_a4_eq
  have hf_a4 : (1 + omega3 x) * (oblX0 x 4 - 1) - (1 + omega4 x) * oblX2 x 4 < 0 := by
    linarith only [h_a4_b4, hf_a4_eq]
  have hf_a3 : (1 + omega3 x) * oblX0 x 3 - (1 + omega4 x) * oblX2 x 3 < 0 := by
    linarith only [hlt3, e3]
  set du := ((1 + omega3 x) * (oblX0 x 4 - 1) - (1 + omega4 x) * oblX2 x 4) *
    ((1 + omega3 x) * oblX0 x 3 - (1 + omega4 x) * oblX2 x 3)
  have hdu_alg : (oblX0 x 3 - 1) * (oblX2 x 4 * (omega3 x * omega4 x - 1) - oblX6 x 4 * (1 + omega3 x)) -
      oblX2 x 3 * ((oblX0 x 4 - 1) * (omega3 x * omega4 x - 1) - oblX6 x 4 * (1 + omega4 x)) +
      oblX6 x 3 * ((oblX0 x 4 - 1) * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) = du := by
    dsimp [du]
    linear_combination ((oblX0 x 4 - 1) * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) * e3 -
      ((oblX0 x 3 - 1) * (1 + omega3 x) - oblX2 x 3 * (1 + omega4 x)) * e4
  have hdu : det3 (x 3 - x 0) (x 4 - x 0) (viewM74 x) = du * det24 x := by
    rw [hA_rep, hB_rep]; dsimp [viewM74, capView]; rw [M4.det3_frame, hdu_alg]
  have hdu_pos : 0 < du := mul_pos_of_neg_of_neg hf_a4 hf_a3
  have hN0 : F.N 3 ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hv6; linarith
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.2 hN0
  have hdet24 : det24 x ≠ 0 := T.det_ne
  have e1 := det_perp' (x 3 - x 0) (x 4 - x 0) (viewM74 x) (F.N 3) hA hB
  have e2 := det_perp' (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) (F.N 3) hA hB
  rw [hdu] at e1; rw [hd6] at e2
  have hABN : det3 (x 3 - x 0) (x 4 - x 0) (F.N 3) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e2
    exact (mul_ne_zero (mul_ne_zero hd6_neg.ne hdet24) hNN.ne') e2
  have hprod : det3 (x 3 - x 0) (x 4 - x 0) (F.N 3) *
      (d6 * ⟪F.N 3, viewM74 x⟫ - du * ⟪F.N 3, x 6 - x 0⟫) = 0 := by
    linear_combination -d6 * e1 + du * e2
  have heq : d6 * ⟪F.N 3, viewM74 x⟫ = du * ⟪F.N 3, x 6 - x 0⟫ := by
    linarith only [(mul_eq_zero.mp hprod).resolve_left hABN]
  nlinarith only [hd6_neg, hdu_pos, heq, hv6]

private theorem viewM27_8_pos (F : S0xFac 9 s0x_S24 x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    0 < ⟪F.N 8, viewM27 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
  have h2' : 0 < oblX0 x 3 + oblX2 x 3 - omega5 x * (oblX6 x 3 - 1) := by
    rw [h2_equiv F] at h2
    exact (mul_pos_iff_of_pos_left hk2).mp h2
  have hdecomp : viewM27 x = (1 + omega5 x) • wallIII x + (1 + omega3 x) • (x 6 - x 2) := by
    dsimp [viewM27, wallIII, capView]
    rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]
    module
  have hwall := inner_wallIII_368 F (t := 8) (by decide)
  rw [F.zero 8 6 (by decide)] at hwall
  have h62 : ⟪F.N 8, x 6 - x 2⟫ = -F.f 8 (x 2) := by
    rw [F.inner_sub, F.zero 8 6 (by decide)]; ring
  have e3 := M4.eq3 F
  have hprod : oblX0 x 3 * ⟪F.N 8, viewM27 x⟫ =
      (oblX0 x 3 + oblX2 x 3 - omega5 x * (oblX6 x 3 - 1)) * (-F.f 8 (x 2)) := by
    rw [hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right, h62]
    linear_combination (1 + omega5 x) * hwall - (-F.f 8 (x 2)) * e3
  have hf8 : 0 < -F.f 8 (x 2) := by linarith [F.neg 8 2 (by decide)]
  exact pos_of_mul_pos_right (by rw [hprod]; exact mul_pos h2' hf8) ha3.le

private theorem viewM27_6_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 6, viewM27 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have e3 := M4.eq3 F
  have e5 := M4.eq5 F
  have hlt3 := T.lt025 (v := 3) (by decide)
  have hlt5 := T.lt236 (v := 5) (by decide)
  have hf1 : (1 + omega3 x) * oblX0 x 3 - (1 + omega5 x) * oblX6 x 3 < 0 := by linarith
  have hf2 : 0 < (1 + omega3 x) * oblX0 x 5 - (1 + omega5 x) * oblX6 x 5 := by linarith
  have hA : ⟪F.N 6, x 3 - x 2⟫ = 0 := by
    rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self]
  have hB : ⟪F.N 6, x 5 - x 2⟫ = 0 := by
    rw [F.inner_sub, F.zero 6 5 (by decide), F.zero 6 2 (by decide), sub_self]
  have hv : ⟪F.N 6, x 6 - x 2⟫ < 0 := by
    rw [F.inner_sub, F.zero 6 2 (by decide), sub_zero]; exact F.neg 6 6 (by decide)
  have hA_rep : x 3 - x 2 = oblX0 x 3 • (x 0 - x 1) + (oblX2 x 3 - 1) • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by
    rw [show x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) by abel, rep_sub F 3]; module
  have hB_rep : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, rep_sub F 5]; module
  have hv_rep : x 6 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) +
      (1 : ℝ) • (x 6 - x 1) := by
    rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]; module
  set du := ((1 + omega3 x) * oblX0 x 5 - (1 + omega5 x) * oblX6 x 5) *
    ((1 + omega3 x) * oblX0 x 3 - (1 + omega5 x) * oblX6 x 3)
  set dv := oblX0 x 3 * (omega3 x * oblX0 x 5 - (oblX2 x 5 + oblX6 x 5 - 1))
  have hdu_alg : oblX0 x 5 * ((oblX2 x 3 - 1) * (1 + omega3 x) - oblX6 x 3 * (omega3 x * omega5 x - 1)) -
      (oblX2 x 5 - 1) * (oblX0 x 3 * (1 + omega3 x) - oblX6 x 3 * (1 + omega5 x)) +
      oblX6 x 5 * (oblX0 x 3 * (omega3 x * omega5 x - 1) - (oblX2 x 3 - 1) * (1 + omega5 x)) = du := by
    rw [show oblX2 x 3 - 1 = omega3 x * oblX0 x 3 - oblX6 x 3 by linarith,
      show oblX2 x 5 - 1 = omega5 x * oblX6 x 5 - oblX0 x 5 by linarith]
    dsimp [du]; ring
  have hdu : det3 (x 5 - x 2) (x 3 - x 2) (viewM27 x) = du * det24 x := by
    rw [hB_rep, hA_rep]; dsimp [viewM27, capView]; rw [M4.det3_frame, hdu_alg]
  have hdv_alg : oblX0 x 5 * ((oblX2 x 3 - 1) * 1 - oblX6 x 3 * (-1)) -
      (oblX2 x 5 - 1) * (oblX0 x 3 * 1 - oblX6 x 3 * 0) +
      oblX6 x 5 * (oblX0 x 3 * (-1) - (oblX2 x 3 - 1) * 0) = dv := by
    dsimp [dv]
    linear_combination oblX0 x 5 * e3
  have hdv : det3 (x 5 - x 2) (x 3 - x 2) (x 6 - x 2) = dv * det24 x := by
    rw [hB_rep, hA_rep, hv_rep, M4.det3_frame, hdv_alg]
  have hdu_neg : du < 0 := mul_neg_of_pos_of_neg hf2 hf1
  have hdv_pos : 0 < dv := mul_pos ha3 (by linarith)
  exact det_ratio_pos F hB hA hv hdu hdv hdu_neg hdv_pos

private theorem viewM27_3_pos (F : S0xFac 9 s0x_S24 x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    0 < ⟪F.N 3, viewM27 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
  have h2' : 0 < oblX0 x 3 + oblX2 x 3 - omega5 x * (oblX6 x 3 - 1) := by
    rw [h2_equiv F] at h2
    exact (mul_pos_iff_of_pos_left hk2).mp h2
  have e3 := M4.eq3 F
  have e5 := M4.eq5 F
  have hlt3 := T.lt025 (v := 3) (by decide)
  have hA : ⟪F.N 3, x 3 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 0 (by decide), sub_self]
  have hB : ⟪F.N 3, x 5 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have hv2 : ⟪F.N 3, x 2 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 2 (by decide)
  have hv6 : ⟪F.N 3, x 6 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 6 (by decide)
  have hA_rep : x 3 - x 0 = (oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by
    rw [show x 3 - x 0 = (x 3 - x 1) - (x 0 - x 1) by abel, rep_sub F 3]; module
  have hB_rep : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, rep_sub F 5]; module
  have hv2_rep : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) +
      (0 : ℝ) • (x 6 - x 1) := by
    rw [show x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) by abel]; module
  have hv6_rep : x 6 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) +
      (1 : ℝ) • (x 6 - x 1) := by
    rw [show x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) by abel]; module
  set d2 := oblX6 x 5 * (oblX0 x 3 + oblX2 x 3 - 1 - omega5 x * oblX6 x 3)
  set d6 := -(1 + omega3 x) * oblX0 x 3 * oblX2 x 5 + (1 + omega5 x) * oblX6 x 5 * oblX2 x 3
  have hd2_alg : (oblX0 x 5 - 1) * (oblX2 x 3 * 0 - oblX6 x 3 * 1) -
      oblX2 x 5 * ((oblX0 x 3 - 1) * 0 - oblX6 x 3 * (-1)) +
      oblX6 x 5 * ((oblX0 x 3 - 1) * 1 - oblX2 x 3 * (-1)) = d2 := by
    dsimp [d2]
    linear_combination -oblX6 x 3 * e5
  have hd2 : det3 (x 5 - x 0) (x 3 - x 0) (x 2 - x 0) = d2 * det24 x := by
    rw [hB_rep, hA_rep, hv2_rep, M4.det3_frame, hd2_alg]
  have hd6_alg : (oblX0 x 5 - 1) * (oblX2 x 3 * 1 - oblX6 x 3 * 0) -
      oblX2 x 5 * ((oblX0 x 3 - 1) * 1 - oblX6 x 3 * (-1)) +
      oblX6 x 5 * ((oblX0 x 3 - 1) * 0 - oblX2 x 3 * (-1)) = d6 := by
    dsimp [d6]
    linear_combination -oblX2 x 5 * e3 + oblX2 x 3 * e5
  have hd6 : det3 (x 5 - x 0) (x 3 - x 0) (x 6 - x 0) = d6 * det24 x := by
    rw [hB_rep, hA_rep, hv6_rep, M4.det3_frame, hd6_alg]
  have hd2_neg : d2 < 0 := mul_neg_of_pos_of_neg hc5 (by linarith)
  have hd6_neg : d6 < 0 := det_same_neg F hB hA hv6 hv2 hd6 hd2 hd2_neg
  have hgap_eq : (1 + omega5 x) * (1 + omega3 x * oblX0 x 3 - oblX6 x 3) -
      (omega3 x * omega5 x - 1) * oblX0 x 3 =
      oblX0 x 3 + (1 + omega3 x * oblX0 x 3 - oblX6 x 3) - omega5 x * (oblX6 x 3 - 1) := by ring
  rw [show 1 + omega3 x * oblX0 x 3 - oblX6 x 3 = oblX2 x 3 by linarith] at hgap_eq
  have hgap : (omega3 x * omega5 x - 1) * oblX0 x 3 < (1 + omega5 x) * oblX2 x 3 := by
    linarith only [h2', hgap_eq]
  have hprod_gap : (omega3 x * omega5 x - 1) * oblX0 x 3 * oblX6 x 5 <
      (1 + omega5 x) * oblX2 x 3 * oblX6 x 5 := mul_lt_mul_of_pos_right hgap hc5
  have hprod_d6 : (1 + omega5 x) * oblX2 x 3 * oblX6 x 5 <
      (1 + omega3 x) * oblX0 x 3 * oblX2 x 5 := by linarith only [hprod_gap, hd6_neg]
  have h_a5_c5 : (omega3 x * omega5 x - 1) * oblX6 x 5 < (1 + omega3 x) * oblX2 x 5 := by
    have : oblX0 x 3 * ((omega3 x * omega5 x - 1) * oblX6 x 5) <
        oblX0 x 3 * ((1 + omega3 x) * oblX2 x 5) := by linarith only [hprod_gap, hprod_d6]
    exact lt_of_mul_lt_mul_left this ha3.le
  have hf_a5_eq : (1 + omega3 x) * (oblX0 x 5 - 1) - (1 + omega5 x) * oblX6 x 5 =
      (omega3 x * omega5 x - 1) * oblX6 x 5 - (1 + omega3 x) * oblX2 x 5 +
      (1 + omega3 x) * (oblX0 x 5 + oblX2 x 5 - 1 - omega5 x * oblX6 x 5) := by ring
  rw [sub_eq_zero.mpr e5, mul_zero, add_zero] at hf_a5_eq
  have hf_a5 : (1 + omega3 x) * (oblX0 x 5 - 1) - (1 + omega5 x) * oblX6 x 5 < 0 := by
    linarith only [h_a5_c5, hf_a5_eq]
  have hf_a3 : (1 + omega3 x) * oblX0 x 3 - (1 + omega5 x) * oblX6 x 3 < 0 := by
    linarith only [hlt3, e3]
  set du := ((1 + omega3 x) * (oblX0 x 5 - 1) - (1 + omega5 x) * oblX6 x 5) *
    ((1 + omega3 x) * oblX0 x 3 - (1 + omega5 x) * oblX6 x 3)
  have hdu_alg : (oblX0 x 5 - 1) * (oblX2 x 3 * (1 + omega3 x) - oblX6 x 3 * (omega3 x * omega5 x - 1)) -
      oblX2 x 5 * ((oblX0 x 3 - 1) * (1 + omega3 x) - oblX6 x 3 * (1 + omega5 x)) +
      oblX6 x 5 * ((oblX0 x 3 - 1) * (omega3 x * omega5 x - 1) - oblX2 x 3 * (1 + omega5 x)) = du := by
    rw [show oblX2 x 3 = 1 + omega3 x * oblX0 x 3 - oblX6 x 3 by linarith,
      show oblX2 x 5 = 1 + omega5 x * oblX6 x 5 - oblX0 x 5 by linarith]
    dsimp [du]; ring
  have hdu : det3 (x 5 - x 0) (x 3 - x 0) (viewM27 x) = du * det24 x := by
    rw [hB_rep, hA_rep]; dsimp [viewM27, capView]; rw [M4.det3_frame, hdu_alg]
  have hdu_pos : 0 < du := mul_pos_of_neg_of_neg hf_a5 hf_a3
  have hN0 : F.N 3 ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hv2; linarith
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.2 hN0
  have hdet24 : det24 x ≠ 0 := T.det_ne
  have e1 := det_perp' (x 5 - x 0) (x 3 - x 0) (viewM27 x) (F.N 3) hB hA
  have e2 := det_perp' (x 5 - x 0) (x 3 - x 0) (x 2 - x 0) (F.N 3) hB hA
  rw [hdu] at e1; rw [hd2] at e2
  have hABN : det3 (x 5 - x 0) (x 3 - x 0) (F.N 3) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e2
    exact (mul_ne_zero (mul_ne_zero hd2_neg.ne hdet24) hNN.ne') e2
  have hprod : det3 (x 5 - x 0) (x 3 - x 0) (F.N 3) *
      (d2 * ⟪F.N 3, viewM27 x⟫ - du * ⟪F.N 3, x 2 - x 0⟫) = 0 := by
    linear_combination -d2 * e1 + du * e2
  have heq : d2 * ⟪F.N 3, viewM27 x⟫ = du * ⟪F.N 3, x 2 - x 0⟫ := by
    linarith only [(mul_eq_zero.mp hprod).resolve_left hABN]
  nlinarith only [hd2_neg, hdu_pos, heq, hv2]

/-! ## (i) Region lemmas -/

/-- **EG1(i), right end.** `M74` is a closed-cell point of the piece-I cell. -/
theorem regionI_M74 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    CellLe F UI DnI (viewM74 x) := by
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have hΔ : 0 ≤ Delta24 x := hC.2.2.2
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact (viewM74_3_pos F h4).le
    · dsimp [viewM74]; rw [inner_capView_4]
      rw [show (1 + omega4 x) - omega4 x * (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring,
        mul_zero]
    · exact (viewM74_6_pos F h4).le
    · dsimp [viewM74]; rw [inner_capView_7]
      rw [show -omega3 x * (1 + omega4 x) + (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring,
        mul_zero]
    · exact (viewM74_8_pos F).le
  · simp only [DnI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · dsimp [viewM74]; rw [inner_capView_0]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · dsimp [viewM74]; rw [inner_capView_1]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · dsimp [viewM74]; rw [inner_capView_2]
      have h21 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      have heq : (1 + omega4 x) + (1 + omega3 x) - omega5 x * (omega3 x * omega4 x - 1) = -Delta24 x := by
        simp only [Delta24]; ring
      rw [heq]; nlinarith
    · dsimp [viewM74]; rw [inner_capView_5]
      have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
      nlinarith

/-- **EG1(i), left end, wall case `b3 ≤ 1`.** `c_0` is a closed-cell point of the piece-I cell. -/
theorem regionI_wall (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb : oblX2 x 3 ≤ 1) :
    CellLe F UI DnI (wallI x) := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hom3 : 0 < omega3 x := hC.1
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have hw := inner_wallI_368 F (t := 3) (by decide)
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have hpos : 0 < oblX0 x 3 * ⟪F.N 3, wallI x⟫ := by nlinarith
      exact (pos_of_mul_pos_right hpos ha3.le).le
    · dsimp [wallI]; rw [inner_capView_4]
      have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      nlinarith
    · have hw := inner_wallI_368 F (t := 6) (by decide)
      rw [F.zero 6 2 (by decide)] at hw
      have h66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
      have hnonneg : 0 ≤ oblX0 x 3 * ⟪F.N 6, wallI x⟫ := by nlinarith
      exact nonneg_of_mul_nonneg_right hnonneg ha3
    · dsimp [wallI]; rw [inner_capView_7]
      rw [show -omega3 x * 1 + 0 + omega3 x = 0 by ring, mul_zero]
    · have hw := inner_wallI_368 F (t := 8) (by decide)
      rw [F.zero 8 6 (by decide)] at hw
      have h82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
      have hpos : 0 < oblX0 x 3 * ⟪F.N 8, wallI x⟫ := by nlinarith
      exact (pos_of_mul_pos_right hpos ha3.le).le
  · simp only [DnI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · dsimp [wallI]; rw [inner_capView_0]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · dsimp [wallI]; rw [inner_capView_1]; rw [zero_mul]
    · dsimp [wallI]; rw [inner_capView_2]
      have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      nlinarith
    · dsimp [wallI]; rw [inner_capView_5]
      have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
      nlinarith

/-- **EG1(i), left end, edge case `1 < b3`.** `u_32 = x 3 - x 2` is a closed-cell point of the piece-I
cell. -/
theorem regionI_edge (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb : 1 < oblX2 x 3)
    (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) : CellLe F UI DnI (x 3 - x 2) := by
  let _ := hC
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 2 (by decide)]
    · exact h4.le
    · rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self]
    · rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self]
    · rw [F.inner_sub, F.zero 8 3 (by decide)]; linarith [F.neg 8 2 (by decide)]
  · simp only [DnI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [F.inner_sub, F.zero 0 2 (by decide), sub_zero]; exact (F.neg 0 3 (by decide)).le
    · have ev := M4.fac_eval F 1 3
      rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev
      rw [F.inner_sub, ev]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact (F.neg 2 3 (by decide)).le
    · rw [F.inner_sub, F.zero 5 2 (by decide), sub_zero]; exact (F.neg 5 3 (by decide)).le

/-- **EG1(i), interior.** At the sum of the two ends every facet of the piece-I cell except `236` is
strict (and `236` is weakly up; it is edge-on). -/
theorem regionI_mid (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    (∀ t ∈ UI, t ≠ 7 → 0 < ⟪F.N t, endIL x + viewM74 x⟫) ∧
      0 ≤ ⟪F.N 7, endIL x + viewM74 x⟫ ∧ ∀ t ∈ DnI, ⟪F.N t, endIL x + viewM74 x⟫ < 0 := by
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  have hL_le : CellLe F UI DnI (endIL x) := by
    unfold endIL
    split_ifs with hb
    · exact regionI_wall F hC hb
    · exact regionI_edge F hC (lt_of_not_ge hb) h4
  have hR_le : CellLe F UI DnI (viewM74 x) := regionI_M74 F hC h4
  refine ⟨fun t ht ht7 => ?_, ?_, fun t ht => ?_⟩
  · rw [inner_add_right]
    have hL0 : 0 ≤ ⟪F.N t, endIL x⟫ := hL_le.1 t ht
    have hR0 : 0 ≤ ⟪F.N t, viewM74 x⟫ := hR_le.1 t ht
    simp only [UI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact add_pos_of_nonneg_of_pos hL0 (viewM74_3_pos F h4)
    · have hL4 : 0 < ⟪F.N 4, endIL x⟫ := by
        unfold endIL
        split_ifs with hb
        · dsimp [wallI]; rw [inner_capView_4]
          have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
          nlinarith
        · exact h4
      exact add_pos_of_pos_of_nonneg hL4 hR0
    · exact add_pos_of_nonneg_of_pos hL0 (viewM74_6_pos F h4)
    · exact absurd rfl ht7
    · exact add_pos_of_nonneg_of_pos hL0 (viewM74_8_pos F)
  · rw [inner_add_right]
    exact add_nonneg (hL_le.1 7 (by decide)) (hR_le.1 7 (by decide))
  · rw [inner_add_right]
    have hL0 : ⟪F.N t, endIL x⟫ ≤ 0 := hL_le.2 t ht
    have hR0 : ⟪F.N t, viewM74 x⟫ ≤ 0 := hR_le.2 t ht
    simp only [DnI, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have hR_0 : ⟪F.N 0, viewM74 x⟫ < 0 := by
        dsimp [viewM74]; rw [inner_capView_0]; have := F.neg 0 6 (by decide); nlinarith
      exact add_lt_of_le_of_neg hL0 hR_0
    · have hR_1 : ⟪F.N 1, viewM74 x⟫ < 0 := by
        dsimp [viewM74]; rw [inner_capView_1]; have := F.neg 1 2 (by decide); nlinarith
      exact add_lt_of_le_of_neg hL0 hR_1
    · have hL_2 : ⟪F.N 2, endIL x⟫ < 0 := by
        unfold endIL
        split_ifs with hb
        · dsimp [wallI]; rw [inner_capView_2]
          have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
          nlinarith
        · rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 3 (by decide)
      exact add_lt_of_neg_of_le hL_2 hR0
    · have hR_5 : ⟪F.N 5, viewM74 x⟫ < 0 := by
        dsimp [viewM74]; rw [inner_capView_5]; have := F.neg 5 0 (by decide); nlinarith
      exact add_lt_of_le_of_neg hL0 hR_5

/-- **EG2(i), left end.** `M27` is a closed-cell point of the piece-III cell. -/
theorem regionIII_M27 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    CellLe F UIII DnIII (viewM27 x) := by
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  have hΔ : 0 ≤ Delta24 x := hC.2.2.2
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · dsimp [viewM27]; rw [inner_capView_2]
      rw [show (1 + omega5 x) + (omega3 x * omega5 x - 1) - omega5 x * (1 + omega3 x) = 0 by ring,
        mul_zero]
    · exact (viewM27_3_pos F h2).le
    · exact (viewM27_6_pos F).le
    · dsimp [viewM27]; rw [inner_capView_7]
      rw [show -omega3 x * (1 + omega5 x) + (omega3 x * omega5 x - 1) + (1 + omega3 x) = 0 by ring,
        mul_zero]
    · exact (viewM27_8_pos F h2).le
  · simp only [DnIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · dsimp [viewM27]; rw [inner_capView_0]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · dsimp [viewM27]; rw [inner_capView_1]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · dsimp [viewM27]; rw [inner_capView_4]
      have h41 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      have heq : (1 + omega5 x) - omega4 x * (omega3 x * omega5 x - 1) + (1 + omega3 x) = -Delta24 x := by
        simp only [Delta24]; ring
      rw [heq]; nlinarith
    · dsimp [viewM27]; rw [inner_capView_5]
      have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
      nlinarith

/-- **EG2(i), right end, wall case `c3 ≤ 1`.** `c_∞` is a closed-cell point of the piece-III cell. -/
theorem regionIII_wall (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hc : oblX6 x 3 ≤ 1) :
    CellLe F UIII DnIII (wallIII x) := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hom3 : 0 < omega3 x := hC.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · dsimp [wallIII]; rw [inner_capView_2]
      have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      nlinarith
    · have hw := inner_wallIII_368 F (t := 3) (by decide)
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have hpos : 0 < oblX0 x 3 * ⟪F.N 3, wallIII x⟫ := by nlinarith
      exact (pos_of_mul_pos_right hpos ha3.le).le
    · have hw := inner_wallIII_368 F (t := 6) (by decide)
      rw [F.zero 6 2 (by decide)] at hw
      have h66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
      have hpos : 0 < oblX0 x 3 * ⟪F.N 6, wallIII x⟫ := by nlinarith
      exact (pos_of_mul_pos_right hpos ha3.le).le
    · dsimp [wallIII]; rw [inner_capView_7]
      rw [show -omega3 x * 1 + omega3 x + 0 = 0 by ring, mul_zero]
    · have hw := inner_wallIII_368 F (t := 8) (by decide)
      rw [F.zero 8 6 (by decide)] at hw
      have h82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
      have hnonneg : 0 ≤ oblX0 x 3 * ⟪F.N 8, wallIII x⟫ := by nlinarith
      exact nonneg_of_mul_nonneg_right hnonneg ha3
  · simp only [DnIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · dsimp [wallIII]; rw [inner_capView_0, zero_mul]
    · dsimp [wallIII]; rw [inner_capView_1]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · dsimp [wallIII]; rw [inner_capView_4]
      have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      nlinarith
    · dsimp [wallIII]; rw [inner_capView_5]
      have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
      nlinarith

/-- **EG2(i), right end, edge case `1 < c3`.** `u_36 = x 3 - x 6` is a closed-cell point of the
piece-III cell. -/
theorem regionIII_edge (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hc : 1 < oblX6 x 3)
    (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) : CellLe F UIII DnIII (x 3 - x 6) := by
  let _ := hC
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact h2.le
    · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 6 (by decide)]
    · rw [F.inner_sub, F.zero 6 3 (by decide)]; linarith [F.neg 6 6 (by decide)]
    · rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self]
    · rw [F.inner_sub, F.zero 8 3 (by decide), F.zero 8 6 (by decide), sub_self]
  · simp only [DnIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have ev := M4.fac_eval F 0 3
      rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev
      rw [F.inner_sub, ev]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · rw [F.inner_sub, F.zero 1 6 (by decide), sub_zero]; exact (F.neg 1 3 (by decide)).le
    · rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; exact (F.neg 4 3 (by decide)).le
    · rw [F.inner_sub, F.zero 5 6 (by decide), sub_zero]; exact (F.neg 5 3 (by decide)).le

/-- **EG2(i), interior.** At the sum of the two ends every facet of the piece-III cell except `236` is
strict (and `236` is weakly up). -/
theorem regionIII_mid (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    (∀ t ∈ UIII, t ≠ 7 → 0 < ⟪F.N t, viewM27 x + endIIIR x⟫) ∧
      0 ≤ ⟪F.N 7, viewM27 x + endIIIR x⟫ ∧ ∀ t ∈ DnIII, ⟪F.N t, viewM27 x + endIIIR x⟫ < 0 := by
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  have hL_le : CellLe F UIII DnIII (viewM27 x) := regionIII_M27 F hC h2
  have hR_le : CellLe F UIII DnIII (endIIIR x) := by
    unfold endIIIR
    split_ifs with hc
    · exact regionIII_wall F hC hc
    · exact regionIII_edge F hC (lt_of_not_ge hc) h2
  refine ⟨fun t ht ht7 => ?_, ?_, fun t ht => ?_⟩
  · rw [inner_add_right]
    have hL0 : 0 ≤ ⟪F.N t, viewM27 x⟫ := hL_le.1 t ht
    have hR0 : 0 ≤ ⟪F.N t, endIIIR x⟫ := hR_le.1 t ht
    simp only [UIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have hR2 : 0 < ⟪F.N 2, endIIIR x⟫ := by
        unfold endIIIR
        split_ifs with hc
        · dsimp [wallIII]; rw [inner_capView_2]
          have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
          nlinarith
        · exact h2
      exact add_pos_of_nonneg_of_pos hL0 hR2
    · exact add_pos_of_pos_of_nonneg (viewM27_3_pos F h2) hR0
    · exact add_pos_of_pos_of_nonneg (viewM27_6_pos F) hR0
    · exact absurd rfl ht7
    · exact add_pos_of_pos_of_nonneg (viewM27_8_pos F h2) hR0
  · rw [inner_add_right]
    exact add_nonneg (hL_le.1 7 (by decide)) (hR_le.1 7 (by decide))
  · rw [inner_add_right]
    have hL0 : ⟪F.N t, viewM27 x⟫ ≤ 0 := hL_le.2 t ht
    have hR0 : ⟪F.N t, endIIIR x⟫ ≤ 0 := hR_le.2 t ht
    simp only [DnIII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have hL_0 : ⟪F.N 0, viewM27 x⟫ < 0 := by
        dsimp [viewM27]; rw [inner_capView_0]; have := F.neg 0 6 (by decide); nlinarith
      exact add_lt_of_neg_of_le hL_0 hR0
    · have hL_1 : ⟪F.N 1, viewM27 x⟫ < 0 := by
        dsimp [viewM27]; rw [inner_capView_1]; have := F.neg 1 2 (by decide); nlinarith
      exact add_lt_of_neg_of_le hL_1 hR0
    · have hR_4 : ⟪F.N 4, endIIIR x⟫ < 0 := by
        unfold endIIIR
        split_ifs with hc
        · dsimp [wallIII]; rw [inner_capView_4]
          have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
          nlinarith
        · rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; exact F.neg 4 3 (by decide)
      exact add_lt_of_le_of_neg hL0 hR_4
    · have hL_5 : ⟪F.N 5, viewM27 x⟫ < 0 := by
        dsimp [viewM27]; rw [inner_capView_5]; have := F.neg 5 0 (by decide); nlinarith
      exact add_lt_of_neg_of_le hL_5 hR0

/-! ## (i) assembled (proved from the region lemmas) -/

theorem n7_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 7, x 2 - x 0⟫ := by
  rw [F.inner_sub, F.zero 7 2 (by decide)]
  have := F.neg 7 0 (by decide)
  linarith

/-- A cell point from a midpoint strict off `236` (tilt toward `+F.N 7` along `x 2 - x 0`). -/
theorem cellAt_of_mid (F : S0xFac 9 s0x_S24 x) {U Dn : Finset (Fin 9)} {u : ℝ³} (hU : ∀ t ∈ U, t ≠ 7 → 0 < ⟪F.N t, u⟫) (h70 : 0 ≤ ⟪F.N 7, u⟫)
    (hD : ∀ t ∈ Dn, ⟪F.N t, u⟫ < 0) : ∃ a, CellAt F U Dn a := by
  refine exists_cellAt_of_lex (u₀ := u) (v := x 2 - x 0) (fun t ht => ?_) (fun t ht => ?_)
  · by_cases h : t = 7
    · subst h
      rcases h70.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, n7_pos F⟩
    · exact Or.inl (hU t ht h)
  · exact Or.inl (by linarith [hD t ht])

theorem regionI_left (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    CellLe F UI DnI (endIL x) := by
  unfold endIL
  split_ifs with hb
  · exact regionI_wall F hC hb
  · exact regionI_edge F hC (lt_of_not_ge hb) h4

theorem regionIII_right (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    CellLe F UIII DnIII (endIIIR x) := by
  unfold endIIIR
  split_ifs with hc
  · exact regionIII_wall F hC hc
  · exact regionIII_edge F hC (lt_of_not_ge hc) h2

/-- **EG1(i).** Both ends of piece I are closed-cell points of the piece-I cell, and the cell is
nonempty. -/
theorem regionI (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    CellLe F UI DnI (endIL x) ∧ CellLe F UI DnI (viewM74 x) ∧ ∃ a, CellAt F UI DnI a := by
  obtain ⟨h1, h2, h3⟩ := regionI_mid F hC h4
  exact ⟨regionI_left F hC h4, regionI_M74 F hC h4,
    cellAt_of_mid F h1 h2 h3⟩

/-- **EG2(i).** Both ends of piece III are closed-cell points of the piece-III cell, and the cell is
nonempty. -/
theorem regionIII (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    CellLe F UIII DnIII (viewM27 x) ∧ CellLe F UIII DnIII (endIIIR x) ∧
      ∃ a, CellAt F UIII DnIII a := by
  obtain ⟨h1, h2', h3⟩ := regionIII_mid F hC h2
  exact ⟨regionIII_M27 F hC h2, regionIII_right F hC h2,
    cellAt_of_mid F h1 h2' h3⟩

/-! ## (ii) The leaves (proved from (i) and `isRupert_of_closedCell_q4`)

`hn` = "not D_A at both ends", `hp` = "not D_B at both ends" (Fable 1.4): for the 4-cycle `c`,
`D_A(g)` is `∀ p ∈ diagPairs, 0 ≤ ⟪x (c p.1) - x (c p.2), g⟫` (`min(z_c0, z_c2) ≥ max(z_c1, z_c3)`),
`D_B(g)` the same with `≤ 0`. -/

/-- **EG1(ii), piece I leaf.** Some diagonal form of `0 5 2 6` negative at an end and some positive at
an end: Rupert. -/
theorem isRupert_pieceI (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫)
    (hn : (∃ p ∈ diagPairs, ⟪x (cI p.1) - x (cI p.2), endIL x⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cI p.1) - x (cI p.2), viewM74 x⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cI p.1) - x (cI p.2), endIL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cI p.1) - x (cI p.2), viewM74 x⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hL, hR, a, ha⟩ := regionI F hC h4
  have hx := Minimality.H24.SAT.inj_of_fac F
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · exact isRupert_of_closedCell_q4 F hx injI cycI ha hL hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injI cycI ha hL hR hn hp
  · exact isRupert_of_closedCell_q4 F hx injI cycI ha hR hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injI cycI ha hR hR hn hp

/-- **EG2(ii), piece III leaf.** Some diagonal form of `0 2 6 4` negative at an end and some positive
at an end: Rupert. -/
theorem isRupert_pieceIII (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫)
    (hn : (∃ p ∈ diagPairs, ⟪x (cIII p.1) - x (cIII p.2), viewM27 x⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cIII p.1) - x (cIII p.2), endIIIR x⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cIII p.1) - x (cIII p.2), viewM27 x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cIII p.1) - x (cIII p.2), endIIIR x⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hL, hR, a, ha⟩ := regionIII F hC h2
  have hx := Minimality.H24.SAT.inj_of_fac F
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · exact isRupert_of_closedCell_q4 F hx injIII cycIII ha hL hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injIII cycIII ha hL hR hn hp
  · exact isRupert_of_closedCell_q4 F hx injIII cycIII ha hR hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injIII cycIII ha hR hR hn hp

end Minimality.T24.EG
