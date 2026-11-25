module

public import Minimality.Type24Pieces236
public import Minimality.FiveRimApex

/-!
# ES: the 5-rim piece II (`0 4 6 2 5`) of circle 236 in the type-24 hidden-cap cone, via Lemma A5

Hydrogen Task ES (2026-11-25; spec nopert229 tools/genleaves/runs/esspec, gate GATE.md there).  Section (i):
region lemmas; section (ii): the leaf, from (i), `Minimality.A5.lexAny_of_a5_row` and elementary convexity along
a segment.  All proved.

Setting (the corner frame at vertex `1`, as `Minimality.T24.EG`, `Type24Pieces236.lean`): `e_a = x 0 - x 1`,
`e_b = x 2 - x 1`, `e_c = x 6 - x 1`; `capView x ca cb cc = ca e_a + cb e_b + cc e_c`; `a3, b3, c3 = oblX0/2/6 x 3`.
Circle 236 in the cone is the pencil `d_s = X3 - ((1 - s) X2 + s X6)`; piece I (`0 5 2 6`, chord-26 sector, `s < s74`),
piece II (`0 4 6 2 5`, `s74 < s < s27`), piece III (`0 2 6 4`, `s > s27`).  Piece II lives in `(max 0 s74, min 1 s27)`.
Ends (shape only, depths linear in the metric):
* left end `M74 = (1 + w4, 1 + w3, w3 w4 - 1)` (viewM74, EG) when `s74 >= 0`, else the edge view `u_32 = x 3 - x 2`
  (`s = 0`, the chord-36 sector lies before it);  `s74 >= 0 <-> a3 - w4 (b3 - 1) + c3 >= 0`;
* right end `M27 = (1 + w5, w3 w5 - 1, 1 + w3)` (viewM27) when `s27 <= 1`, else `u_36 = x 3 - x 6` (`s = 1`);
  `s27 <= 1 <-> a3 + b3 - w5 (c3 - 1) >= 0`.
(The raw `viewM74`, `viewM27` are NOT closed-cell points when `s74 < 0` resp. `s27 > 1`: gate `RAW` lines.)

Cell of piece II (engine lex view at the midpoint of the two ends tilted by `+NV_7`; constant on every gated point):
rim `0 4 6 2 5`, up `0345, 235, 236, 346` (`3 6 7 8`), down `012, 016, 025, 046, 126` (`0 1 2 4 5`).
Facet `236` is edge-on along the circle, so as in EG the circle views are only `CellLe` points and the open cell is
reached by the tilt `x 2 - x 0` (`EG.cellAt_of_mid`).

Existence: piece II exists iff `Delta24 > 0` (A63 TESTS).  The mechanism is the pair of identities
`sign <N_2, M74> = sign <N_4, M27> = - sign Delta24` (EG notes `N_2 . M74 = -Delta`) and `Delta24 = 0 -> M74 || M27`.

Apex data (FACENORM24 FABLE2 TESTS item (d)): lower apex `0` (rim label `0`), the non-edge and the upper apex are
decided by the bracket `B = [x4 - x2, x5 - x2, x6 - x2] / det24` (corner coordinates, mirror invariant):
`B > 0`: non-edge `24`, upper apex `5` (rim label `4`), `ApexPat a = 4, eps = 1`;
`B < 0`: non-edge `56`, upper apex `4` (rim label `1`), `ApexPat a = 1, eps = -1`.
The A5 row is `<x upper, u> < <x 0, u>`.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.ES

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC Minimality.T24.EG
  Minimality.A5

variable {x : Fin 7 → ℝ³}

/-! ## Cell, cycle, ends, apex labelling -/

/-- Up facets of the piece-II cell (rim `0 4 6 2 5`): `0345, 235, 236, 346`. -/
def UII : Finset (Fin 9) := {3, 6, 7, 8}
/-- Down facets of the piece-II cell: `012, 016, 025, 046, 126`. -/
def DnII : Finset (Fin 9) := {0, 1, 2, 4, 5}
/-- Rim cycle of piece II. -/
def cII : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

theorem cycII : S0xCycUD s0x_S24 cII UII DnII := by decide

theorem injII : Function.Injective cII := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- `s74 >= 0` in corner coordinates: `a3 - w4 (b3 - 1) + c3 >= 0`. -/
def LeftM74 (x : Fin 7 → ℝ³) : Prop :=
  0 ≤ oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + oblX6 x 3
/-- `s27 <= 1` in corner coordinates: `a3 + b3 - w5 (c3 - 1) >= 0`. -/
def RightM27 (x : Fin 7 → ℝ³) : Prop :=
  0 ≤ oblX0 x 3 + oblX2 x 3 - omega5 x * (oblX6 x 3 - 1)

open Classical in
/-- Left end of piece II: `M74` if `s74 >= 0`, else the edge view `u_32 = x 3 - x 2`. -/
noncomputable def endIIL (x : Fin 7 → ℝ³) : ℝ³ := if LeftM74 x then viewM74 x else x 3 - x 2
open Classical in
/-- Right end of piece II: `M27` if `s27 <= 1`, else the edge view `u_36 = x 3 - x 6`. -/
noncomputable def endIIR (x : Fin 7 → ℝ³) : ℝ³ := if RightM27 x then viewM27 x else x 3 - x 6
/-- The sum of the two ends (a view strictly inside piece II up to the facet `236`). -/
noncomputable def midII (x : Fin 7 → ℝ³) : ℝ³ := endIIL x + endIIR x

/-- The bracket `[x4 - x2, x5 - x2, x6 - x2]` in corner coordinates (divided by the frame determinant, so it is
invariant under mirror images). -/
noncomputable def brk24 (x : Fin 7 → ℝ³) : ℝ :=
  vol3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) / det24 x

open Classical in
/-- Upper apex vertex of the rim `0 4 6 2 5`: `5` if the bracket is positive, else `4` (lower apex is always `0`). -/
noncomputable def apexV (x : Fin 7 → ℝ³) : Fin 7 := if 0 < brk24 x then 5 else 4
open Classical in
/-- Start label `a` of the apex labelling (`cII a = apexV x`). -/
noncomputable def apexA (x : Fin 7 → ℝ³) : ZMod 5 := if 0 < brk24 x then 4 else 1
open Classical in
/-- Direction `eps` of the apex labelling (`cII (a + eps) = 0`). -/
noncomputable def apexE (x : Fin 7 → ℝ³) : ZMod 5 := if 0 < brk24 x then 1 else -1

/-- Weak strict-convexity companion of `StrictConvex5`: all the determinants have the sign `rho` or vanish. -/
def WeakConvex5 (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) : Prop :=
  ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 ≤ ρ * det3 (p (i + 1) - p i) (p j - p i) u

theorem cII_apexA (x : Fin 7 → ℝ³) : cII (apexA x) = apexV x := by
  unfold apexA apexV; split_ifs <;> decide

theorem cII_apexA_add (x : Fin 7 → ℝ³) : cII (apexA x + apexE x) = 0 := by
  unfold apexA apexE; split_ifs <;> decide

/-! ## Local facet/frame helpers -/

private theorem rep_sub (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
  rw [(M4.type24OfFac F).rep v]; abel

private theorem inner_capView_0 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 0, capView x ca cb cc⟫ = cc * F.f 0 (x 6) := by
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide), sub_self,
    mul_zero, zero_add, sub_zero]

private theorem inner_capView_1 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 1, capView x ca cb cc⟫ = cb * F.f 1 (x 2) := by
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide), sub_self,
    mul_zero, zero_add, add_zero, sub_zero]

private theorem inner_capView_5 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 5, capView x ca cb cc⟫ = ca * F.f 5 (x 0) := by
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide), sub_self,
    mul_zero, add_zero, sub_zero]

private theorem inner_capView_7 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 7, capView x ca cb cc⟫ =
      (-F.f 7 (x 1)) * (-omega3 x * ca + cb + cc) := by
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
  have ht3 : F.f t (x 3) = 0 := by
    fin_cases t <;> simp at ht ⊢ <;> exact F.zero _ 3 (by decide)
  have e3 := M4.eq3 F
  have ev := M4.fac_eval F t 3
  rw [ht3] at ev
  have hwall : ⟪F.N t, wallI x⟫ = (F.f t (x 0) - F.f t (x 1)) + omega3 x * (F.f t (x 6) - F.f t (x 1)) := by
    simp only [wallI, capView, inner_add_right, real_inner_smul_right, F.inner_sub]
    ring
  rw [hwall]
  have hob6 : oblX6 x 3 = 1 + omega3 x * oblX0 x 3 - oblX2 x 3 := by linarith
  rw [hob6] at ev
  fin_cases t <;> simp at ht ev ⊢
  · rw [F.zero 3 0 (by decide)] at ev ⊢; linear_combination -ev
  · rw [F.zero 6 2 (by decide)] at ev ⊢; linear_combination -ev
  · rw [F.zero 8 6 (by decide)] at ev ⊢; linear_combination -ev

private theorem inner_wallIII_368 (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ∈ ({3, 6, 8} : Finset (Fin 9))) :
    oblX0 x 3 * ⟪F.N t, wallIII x⟫ = (oblX6 x 3 - 1) * F.f t (x 2) - oblX6 x 3 * F.f t (x 6) := by
  have ht3 : F.f t (x 3) = 0 := by
    fin_cases t <;> simp at ht ⊢ <;> exact F.zero _ 3 (by decide)
  have e3 := M4.eq3 F
  have ev := M4.fac_eval F t 3
  rw [ht3] at ev
  have hwall : ⟪F.N t, wallIII x⟫ = (F.f t (x 0) - F.f t (x 1)) + omega3 x * (F.f t (x 2) - F.f t (x 1)) := by
    simp only [wallIII, capView, inner_add_right, real_inner_smul_right, F.inner_sub]
    ring
  rw [hwall]
  have hob2 : oblX2 x 3 = 1 + omega3 x * oblX0 x 3 - oblX6 x 3 := by linarith
  rw [hob2] at ev
  fin_cases t <;> simp at ht ev ⊢
  · rw [F.zero 3 0 (by decide)] at ev ⊢; linear_combination -ev
  · rw [F.zero 6 2 (by decide)] at ev ⊢; linear_combination -ev
  · rw [F.zero 8 6 (by decide)] at ev ⊢; linear_combination -ev

private theorem det_ratio_pos (F : S0xFac 9 s0x_S24 x) {N A B u v : ℝ³}
    (hA : ⟪N, A⟫ = 0) (hB : ⟪N, B⟫ = 0) (hv : ⟪N, v⟫ < 0)
    {du dv : ℝ} (hdu : det3 A B u = du * det24 x) (hdv : det3 A B v = dv * det24 x)
    (hdu_neg : du < 0) (hdv_pos : 0 < dv) :
    0 < ⟪N, u⟫ := by
  have hd_ne : det24 x ≠ 0 := by
    have h1 := HC.det3_e026_ne F
    have h2 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det24 x := by
      simp only [det24, vol3, det3_expand]; ring
    rw [← h2]; exact h1
  have hdv_ne : det3 A B v ≠ 0 := by rw [hdv]; exact mul_ne_zero hdv_pos.ne' hd_ne
  have hcross : ∀ w : ℝ³, det3 A B v * ⟪N, w⟫ - det3 A B w * ⟪N, v⟫ =
      (det3 A B v * ⟪N, w⟫ - det3 A B w * ⟪N, v⟫) := fun _ => rfl
  have hlin : det3 A B v * ⟪N, u⟫ = det3 A B u * ⟪N, v⟫ := by
    have hli : LinearIndependent ℝ ![A, B, v] := HC.li_of_det3 A B v hdv_ne
    have hzero : det3 A B v * ⟪N, u⟫ - det3 A B u * ⟪N, v⟫ = 0 := by
      have h3 : det3 A B v • u - det3 A B u • v =
          det3 u B v • A + det3 A u v • B := by
        ext k
        have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
        rcases hk k with rfl | rfl | rfl <;> ring
      have := congrArg (fun z => ⟪N, z⟫) h3
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hA, hB,
        mul_zero, add_zero] at this
      exact this
    linarith
  rw [hdu, hdv] at hlin
  have hmul : (dv * det24 x) ^ 2 * ⟪N, u⟫ = (dv * du) * (det24 x) ^ 2 * ⟪N, v⟫ := by
    calc (dv * det24 x) ^ 2 * ⟪N, u⟫ = (dv * det24 x) * ((dv * det24 x) * ⟪N, u⟫) := by ring
      _ = (dv * det24 x) * ((du * det24 x) * ⟪N, v⟫) := by rw [hlin]
      _ = (dv * du) * (det24 x) ^ 2 * ⟪N, v⟫ := by ring
  have hpos_lhs : 0 < (dv * det24 x) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hdv_pos.ne' hd_ne)
  have hpos_rhs : 0 < (dv * du) * (det24 x) ^ 2 * ⟪N, v⟫ := by
    have h1 : dv * du < 0 := mul_neg_of_pos_of_neg hdv_pos hdu_neg
    have h2 : 0 < (det24 x) ^ 2 := sq_pos_of_ne_zero hd_ne
    nlinarith [mul_neg_of_neg_of_pos h1 h2]
  exact pos_of_mul_pos_right (by rw [hmul]; exact hpos_rhs) hpos_lhs.le

private theorem det_same_neg (F : S0xFac 9 s0x_S24 x) {N A B u v : ℝ³}
    (hA : ⟪N, A⟫ = 0) (hB : ⟪N, B⟫ = 0) (hu : ⟪N, u⟫ < 0) (hv : ⟪N, v⟫ < 0)
    {du dv : ℝ} (hdu : det3 A B u = du * det24 x) (hdv : det3 A B v = dv * det24 x)
    (hdv_neg : dv < 0) :
    du < 0 := by
  have hd_ne : det24 x ≠ 0 := by
    have h1 := HC.det3_e026_ne F
    have h2 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det24 x := by
      simp only [det24, vol3, det3_expand]; ring
    rw [← h2]; exact h1
  have hlin : det3 A B v * ⟪N, u⟫ = det3 A B u * ⟪N, v⟫ := by
    have h3 : det3 A B v • u - det3 A B u • v =
        det3 u B v • A + det3 A u v • B := by
      ext k
      have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
      rcases hk k with rfl | rfl | rfl <;> ring
    have := congrArg (fun z => ⟪N, z⟫) h3
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hA, hB,
      mul_zero, add_zero] at this
    linarith
  rw [hdu, hdv] at hlin
  have h1 : det24 x * (dv * ⟪N, u⟫ - du * ⟪N, v⟫) = 0 := by linarith
  have h2 : dv * ⟪N, u⟫ = du * ⟪N, v⟫ := by
    have := (mul_eq_zero.mp h1).resolve_left hd_ne
    linarith
  have hpos : 0 < dv * ⟪N, u⟫ := mul_pos_of_neg_of_neg hdv_neg hu
  nlinarith

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

private theorem viewM74_6_nonneg (F : S0xFac 9 s0x_S24 x) (h4 : LeftM74 x) :
    0 ≤ ⟪F.N 6, viewM74 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
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
  exact nonneg_of_mul_nonneg_right (by rw [hprod]; exact mul_nonneg h4 hf6.le) ha3

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
  exact det_ratio_pos F hA hB hv hdu hdv (mul_neg_of_pos_of_neg hf2 hf1) (mul_pos ha3 (by linarith))

private theorem viewM74_3_pos (F : S0xFac 9 s0x_S24 x) (h4 : LeftM74 x) :
    0 < ⟪F.N 3, viewM74 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
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
    dsimp [d2]; linear_combination -oblX6 x 4 * e3 + oblX6 x 3 * e4
  have hd2 : det3 (x 3 - x 0) (x 4 - x 0) (x 2 - x 0) = d2 * det24 x := by
    rw [hA_rep, hB_rep, hv2_rep, M4.det3_frame, hd2_alg]
  have hd6_alg : (oblX0 x 3 - 1) * (oblX2 x 4 * 1 - oblX6 x 4 * 0) -
      oblX2 x 3 * ((oblX0 x 4 - 1) * 1 - oblX6 x 4 * (-1)) +
      oblX6 x 3 * ((oblX0 x 4 - 1) * 0 - oblX2 x 4 * (-1)) = d6 := by
    dsimp [d6]; linear_combination -oblX2 x 3 * e4
  have hd6 : det3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) = d6 * det24 x := by
    rw [hA_rep, hB_rep, hv6_rep, M4.det3_frame, hd6_alg]
  have hd6_neg : d6 < 0 := mul_neg_of_pos_of_neg hb4 (by linarith)
  have hd2_neg : d2 < 0 := det_same_neg F hA hB hv2 hv6 hd2 hd6 hd6_neg
  have hgap_eq : (1 + omega4 x) * (1 + omega3 x * oblX0 x 3 - oblX2 x 3) -
      (omega3 x * omega4 x - 1) * oblX0 x 3 =
      oblX0 x 3 - omega4 x * (oblX2 x 3 - 1) + (1 + omega3 x * oblX0 x 3 - oblX2 x 3) := by ring
  rw [show 1 + omega3 x * oblX0 x 3 - oblX2 x 3 = oblX6 x 3 by linarith] at hgap_eq
  have hgap : (omega3 x * omega4 x - 1) * oblX0 x 3 ≤ (1 + omega4 x) * oblX6 x 3 := by
    dsimp [LeftM74] at h4; linarith only [h4, hgap_eq]
  have hprod_gap : (omega3 x * omega4 x - 1) * oblX0 x 3 * oblX2 x 4 ≤
      (1 + omega4 x) * oblX6 x 3 * oblX2 x 4 := mul_le_mul_of_nonneg_right hgap hb4.le
  have hprod_d2 : (1 + omega4 x) * oblX6 x 3 * oblX2 x 4 <
      (1 + omega3 x) * oblX0 x 3 * oblX6 x 4 := by linarith only [hd2_neg]
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
  have hdu : det3 (x 4 - x 0) (x 3 - x 0) (viewM74 x) = (-du) * det24 x := by
    rw [hB_rep, hA_rep]; dsimp [viewM74, capView]; rw [M4.det3_frame]
    have : (oblX0 x 4 - 1) * (oblX2 x 3 * (omega3 x * omega4 x - 1) - oblX6 x 3 * (1 + omega3 x)) -
        oblX2 x 4 * ((oblX0 x 3 - 1) * (omega3 x * omega4 x - 1) - oblX6 x 3 * (1 + omega4 x)) +
        oblX6 x 4 * ((oblX0 x 3 - 1) * (1 + omega3 x) - oblX2 x 3 * (1 + omega4 x)) =
        -((oblX0 x 3 - 1) * (oblX2 x 4 * (omega3 x * omega4 x - 1) - oblX6 x 4 * (1 + omega3 x)) -
          oblX2 x 3 * ((oblX0 x 4 - 1) * (omega3 x * omega4 x - 1) - oblX6 x 4 * (1 + omega4 x)) +
          oblX6 x 3 * ((oblX0 x 4 - 1) * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x))) := by ring
    rw [this, hdu_alg]
  have hd6' : det3 (x 4 - x 0) (x 3 - x 0) (x 6 - x 0) = (-d6) * det24 x := by
    rw [hB_rep, hA_rep, hv6_rep, M4.det3_frame]
    have : (oblX0 x 4 - 1) * (oblX2 x 3 * 1 - oblX6 x 3 * 0) -
        oblX2 x 4 * ((oblX0 x 3 - 1) * 1 - oblX6 x 3 * (-1)) +
        oblX6 x 4 * ((oblX0 x 3 - 1) * 0 - oblX2 x 3 * (-1)) =
        -((oblX0 x 3 - 1) * (oblX2 x 4 * 1 - oblX6 x 4 * 0) -
          oblX2 x 3 * ((oblX0 x 4 - 1) * 1 - oblX6 x 4 * (-1)) +
          oblX6 x 3 * ((oblX0 x 4 - 1) * 0 - oblX2 x 4 * (-1))) := by ring
    rw [this, hd6_alg]
  have hdu_neg : -du < 0 := by linarith [mul_pos_of_neg_of_neg hf_a4 hf_a3]
  have hd6_pos : 0 < -d6 := by linarith [hd6_neg]
  exact det_ratio_pos F hB hA hv6 hdu hd6' hdu_neg hd6_pos

private theorem viewM27_8_nonneg (F : S0xFac 9 s0x_S24 x) (h2 : RightM27 x) :
    0 ≤ ⟪F.N 8, viewM27 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
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
  exact nonneg_of_mul_nonneg_right (by rw [hprod]; exact mul_nonneg h2 hf8.le) ha3

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
    dsimp [dv]; linear_combination oblX0 x 5 * e3
  have hdv : det3 (x 5 - x 2) (x 3 - x 2) (x 6 - x 2) = dv * det24 x := by
    rw [hB_rep, hA_rep, hv_rep, M4.det3_frame, hdv_alg]
  exact det_ratio_pos F hB hA hv hdu hdv (mul_neg_of_pos_of_neg hf2 hf1) (mul_pos ha3 (by linarith))

private theorem viewM27_3_pos (F : S0xFac 9 s0x_S24 x) (h2 : RightM27 x) :
    0 < ⟪F.N 3, viewM27 x⟫ := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
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
    dsimp [d2]; linear_combination -oblX6 x 3 * e5
  have hd2 : det3 (x 5 - x 0) (x 3 - x 0) (x 2 - x 0) = d2 * det24 x := by
    rw [hB_rep, hA_rep, hv2_rep, M4.det3_frame, hd2_alg]
  have hd6_alg : (oblX0 x 5 - 1) * (oblX2 x 3 * 1 - oblX6 x 3 * 0) -
      oblX2 x 5 * ((oblX0 x 3 - 1) * 1 - oblX6 x 3 * (-1)) +
      oblX6 x 5 * ((oblX0 x 3 - 1) * 0 - oblX2 x 3 * (-1)) = d6 := by
    dsimp [d6]; linear_combination -oblX2 x 5 * e3 + oblX2 x 3 * e5
  have hd6 : det3 (x 5 - x 0) (x 3 - x 0) (x 6 - x 0) = d6 * det24 x := by
    rw [hB_rep, hA_rep, hv6_rep, M4.det3_frame, hd6_alg]
  have hd2_neg : d2 < 0 := mul_neg_of_pos_of_neg hc5 (by linarith)
  have hd6_neg : d6 < 0 := det_same_neg F hB hA hv6 hv2 hd6 hd2 hd2_neg
  have hgap_eq : (1 + omega5 x) * (1 + omega3 x * oblX0 x 3 - oblX6 x 3) -
      (omega3 x * omega5 x - 1) * oblX0 x 3 =
      oblX0 x 3 + (1 + omega3 x * oblX0 x 3 - oblX6 x 3) - omega5 x * (oblX6 x 3 - 1) := by ring
  rw [show 1 + omega3 x * oblX0 x 3 - oblX6 x 3 = oblX2 x 3 by linarith] at hgap_eq
  have hgap : (omega3 x * omega5 x - 1) * oblX0 x 3 ≤ (1 + omega5 x) * oblX2 x 3 := by
    dsimp [RightM27] at h2; linarith only [h2, hgap_eq]
  have hprod_gap : (omega3 x * omega5 x - 1) * oblX0 x 3 * oblX6 x 5 ≤
      (1 + omega5 x) * oblX2 x 3 * oblX6 x 5 := mul_le_mul_of_nonneg_right hgap hc5.le
  have hprod_d6 : (1 + omega5 x) * oblX2 x 3 * oblX6 x 5 <
      (1 + omega3 x) * oblX0 x 3 * oblX2 x 5 := by linarith only [hd6_neg]
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
  have hdu_alg : (oblX0 x 3 - 1) * (oblX2 x 5 * (1 + omega3 x) - oblX6 x 5 * (omega3 x * omega5 x - 1)) -
      oblX2 x 3 * ((oblX0 x 5 - 1) * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) +
      oblX6 x 3 * ((oblX0 x 5 - 1) * (omega3 x * omega5 x - 1) - oblX2 x 5 * (1 + omega5 x)) = -du := by
    rw [show oblX2 x 3 = 1 + omega3 x * oblX0 x 3 - oblX6 x 3 by linarith,
      show oblX2 x 5 = 1 + omega5 x * oblX6 x 5 - oblX0 x 5 by linarith]
    dsimp [du]; ring
  have hdu : det3 (x 3 - x 0) (x 5 - x 0) (viewM27 x) = (-du) * det24 x := by
    rw [hA_rep, hB_rep]; dsimp [viewM27, capView]; rw [M4.det3_frame, hdu_alg]
  have hd2' : det3 (x 3 - x 0) (x 5 - x 0) (x 2 - x 0) = (-d2) * det24 x := by
    rw [hA_rep, hB_rep]; rw [hv2_rep, M4.det3_frame]
    have : (oblX0 x 3 - 1) * (oblX2 x 5 * 0 - oblX6 x 5 * 1) -
        oblX2 x 3 * ((oblX0 x 5 - 1) * 0 - oblX6 x 5 * (-1)) +
        oblX6 x 3 * ((oblX0 x 5 - 1) * 1 - oblX2 x 5 * (-1)) =
        -((oblX0 x 5 - 1) * (oblX2 x 3 * 0 - oblX6 x 3 * 1) -
          oblX2 x 5 * ((oblX0 x 3 - 1) * 0 - oblX6 x 3 * (-1)) +
          oblX6 x 5 * ((oblX0 x 3 - 1) * 1 - oblX2 x 3 * (-1))) := by ring
    rw [this, hd2_alg]
  have hdu_neg : -du < 0 := by linarith [mul_pos_of_neg_of_neg hf_a5 hf_a3]
  have hd2_pos : 0 < -d2 := by linarith [hd2_neg]
  exact det_ratio_pos F hA hB hv2 hdu hd2' hdu_neg hd2_pos

/-! ## (i) Region lemmas -/

/-- **ES(i), existence.** On `CbarIn`: `Delta24 > 0` iff `<N_2, M74> < 0` (and `= 0` iff `= 0`). -/
theorem n2_viewM74_sign (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    (0 < Delta24 x ↔ ⟪F.N 2, viewM74 x⟫ < 0) ∧ (Delta24 x = 0 ↔ ⟪F.N 2, viewM74 x⟫ = 0) := by
  let _ := hC
  have h21 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
  have heq : ⟪F.N 2, viewM74 x⟫ = (-F.f 2 (x 1)) * (-Delta24 x) := by
    dsimp [viewM74]; rw [inner_capView_2]
    have h : (1 + omega4 x) + (1 + omega3 x) - omega5 x * (omega3 x * omega4 x - 1) = -Delta24 x := by
      simp only [Delta24]; ring
    rw [h]
  rw [heq]
  constructor
  · constructor
    · intro hD; exact mul_neg_of_pos_of_neg h21 (neg_lt_zero.mpr hD)
    · intro hneg; by_contra hle; push Not at hle; nlinarith [mul_nonneg h21.le (neg_nonneg.mpr hle)]
  · constructor
    · intro h0; simp [h0]
    · intro h0; have := (mul_eq_zero.mp h0).resolve_left h21.ne'; linarith

/-- **ES(i), existence.** On `CbarIn`: `Delta24 > 0` iff `<N_4, M27> < 0` (and `= 0` iff `= 0`). -/
theorem n4_viewM27_sign (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    (0 < Delta24 x ↔ ⟪F.N 4, viewM27 x⟫ < 0) ∧ (Delta24 x = 0 ↔ ⟪F.N 4, viewM27 x⟫ = 0) := by
  let _ := hC
  have h41 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
  have heq : ⟪F.N 4, viewM27 x⟫ = (-F.f 4 (x 1)) * (-Delta24 x) := by
    dsimp [viewM27]; rw [inner_capView_4]
    have h : (1 + omega5 x) - omega4 x * (omega3 x * omega5 x - 1) + (1 + omega3 x) = -Delta24 x := by
      simp only [Delta24]; ring
    rw [h]
  rw [heq]
  constructor
  · constructor
    · intro hD; exact mul_neg_of_pos_of_neg h41 (neg_lt_zero.mpr hD)
    · intro hneg; by_contra hle; push Not at hle; nlinarith [mul_nonneg h41.le (neg_nonneg.mpr hle)]
  · constructor
    · intro h0; simp [h0]
    · intro h0; have := (mul_eq_zero.mp h0).resolve_left h41.ne'; linarith

/-- **ES(i), existence.** On the wall `Delta24 = 0` the two ends coincide: the run of piece II is a point. -/
theorem viewM27_of_delta_zero (hC : CbarIn x) (hΔ : Delta24 x = 0) :
    ∃ c : ℝ, 0 < c ∧ viewM27 x = c • viewM74 x := by
  have hom4 : 0 < 1 + omega4 x := by linarith [hC.2.1]
  have hom5 : 0 < 1 + omega5 x := by linarith [hC.2.2.1]
  refine ⟨(1 + omega5 x) / (1 + omega4 x), div_pos hom5 hom4, ?_⟩
  apply smul_right_injective ℝ³ hom4.ne'
  dsimp only
  rw [smul_smul, mul_div_cancel₀ _ hom4.ne']
  dsimp [viewM27, viewM74, capView]
  have h2 : (1 + omega4 x) * (omega3 x * omega5 x - 1) = (1 + omega5 x) * (1 + omega3 x) := by
    simp only [Delta24] at hΔ; linarith
  have h3 : (1 + omega4 x) * (1 + omega3 x) = (1 + omega5 x) * (omega3 x * omega4 x - 1) := by
    simp only [Delta24] at hΔ; linarith
  rw [smul_add, smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    smul_smul, smul_smul, smul_smul, h2, h3, mul_comm (1 + omega4 x) (1 + omega5 x)]

/-- **ES(i), left end.** The left end of piece II (`M74`, or `u_32` when `s74 < 0`) is a closed-cell point. -/
theorem regionII_left (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) :
    CellLe F UII DnII (endIIL x) := by
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  unfold endIIL
  split_ifs with hL
  · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [UII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact (viewM74_3_pos F hL).le
      · exact viewM74_6_nonneg F hL
      · dsimp [viewM74]; rw [inner_capView_7]
        rw [show -omega3 x * (1 + omega4 x) + (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring,
          mul_zero]
      · exact (viewM74_8_pos F).le
    · simp only [DnII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · dsimp [viewM74]; rw [inner_capView_0]
        have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
        nlinarith
      · dsimp [viewM74]; rw [inner_capView_1]
        have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
        nlinarith
      · exact ((n2_viewM74_sign F hC).1.1 hD).le
      · dsimp [viewM74]; rw [inner_capView_4]
        rw [show (1 + omega4 x) - omega4 x * (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring,
          mul_zero]
      · dsimp [viewM74]; rw [inner_capView_5]
        have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
        nlinarith
  · have T := M4.type24OfFac F
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
    have hb3_gt : 1 < oblX2 x 3 := by
      dsimp [LeftM74] at hL; push Not at hL; nlinarith
    have h4neg : ⟪F.N 4, x 3 - x 2⟫ < 0 := by
      dsimp [LeftM74] at hL; push Not at hL
      rw [h4_equiv F]
      have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      exact mul_neg_of_pos_of_neg hk4 hL
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [UII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 2 (by decide)]
      · rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self]
      · rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self]
      · rw [F.inner_sub, F.zero 8 3 (by decide)]; linarith [F.neg 8 2 (by decide)]
    · simp only [DnII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [F.inner_sub, F.zero 0 2 (by decide), sub_zero]; exact (F.neg 0 3 (by decide)).le
      · have ev := M4.fac_eval F 1 3
        rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev
        rw [F.inner_sub, ev]
        have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
        nlinarith
      · rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact (F.neg 2 3 (by decide)).le
      · exact h4neg.le
      · rw [F.inner_sub, F.zero 5 2 (by decide), sub_zero]; exact (F.neg 5 3 (by decide)).le

/-- **ES(i), right end.** The right end of piece II (`M27`, or `u_36` when `s27 > 1`) is a closed-cell point. -/
theorem regionII_right (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) :
    CellLe F UII DnII (endIIR x) := by
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  unfold endIIR
  split_ifs with hR
  · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [UII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact (viewM27_3_pos F hR).le
      · exact (viewM27_6_pos F).le
      · dsimp [viewM27]; rw [inner_capView_7]
        rw [show -omega3 x * (1 + omega5 x) + (omega3 x * omega5 x - 1) + (1 + omega3 x) = 0 by ring,
          mul_zero]
      · exact viewM27_8_nonneg F hR
    · simp only [DnII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · dsimp [viewM27]; rw [inner_capView_0]
        have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
        nlinarith
      · dsimp [viewM27]; rw [inner_capView_1]
        have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
        nlinarith
      · dsimp [viewM27]; rw [inner_capView_2]
        rw [show (1 + omega5 x) + (omega3 x * omega5 x - 1) - omega5 x * (1 + omega3 x) = 0 by ring,
          mul_zero]
      · exact ((n4_viewM27_sign F hC).1.1 hD).le
      · dsimp [viewM27]; rw [inner_capView_5]
        have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
        nlinarith
  · have T := M4.type24OfFac F
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
    have hc3_gt : 1 < oblX6 x 3 := by
      dsimp [RightM27] at hR; push Not at hR; nlinarith
    have h2neg : ⟪F.N 2, x 3 - x 6⟫ < 0 := by
      dsimp [RightM27] at hR; push Not at hR
      rw [h2_equiv F]
      have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      exact mul_neg_of_pos_of_neg hk2 hR
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [UII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 6 (by decide)]
      · rw [F.inner_sub, F.zero 6 3 (by decide)]; linarith [F.neg 6 6 (by decide)]
      · rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self]
      · rw [F.inner_sub, F.zero 8 3 (by decide), F.zero 8 6 (by decide), sub_self]
    · simp only [DnII, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · have ev := M4.fac_eval F 0 3
        rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev
        rw [F.inner_sub, ev]
        have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
        nlinarith
      · rw [F.inner_sub, F.zero 1 6 (by decide), sub_zero]; exact (F.neg 1 3 (by decide)).le
      · exact h2neg.le
      · rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; exact (F.neg 4 3 (by decide)).le
      · rw [F.inner_sub, F.zero 5 6 (by decide), sub_zero]; exact (F.neg 5 3 (by decide)).le

/-- **ES(i), interior.** At the sum of the two ends every facet of the piece-II cell except `236` is strict
(`236` is weakly up; it is edge-on). -/
theorem regionII_mid (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) :
    (∀ t ∈ UII, t ≠ 7 → 0 < ⟪F.N t, midII x⟫) ∧ 0 ≤ ⟪F.N 7, midII x⟫ ∧
      ∀ t ∈ DnII, ⟪F.N t, midII x⟫ < 0 := by
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have hom35 : 1 < omega3 x * omega5 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have h := hC.2.2.2; simp only [Delta24] at h; linarith)
  have hL := regionII_left F hC hD
  have hR := regionII_right F hC hD
  have hL6 : 0 < ⟪F.N 6, endIIR x⟫ := by
    unfold endIIR; split_ifs
    · exact viewM27_6_pos F
    · rw [F.inner_sub, F.zero 6 3 (by decide)]; linarith [F.neg 6 6 (by decide)]
  have hL8 : 0 < ⟪F.N 8, endIIL x⟫ := by
    unfold endIIL; split_ifs
    · exact viewM74_8_pos F
    · rw [F.inner_sub, F.zero 8 3 (by decide)]; linarith [F.neg 8 2 (by decide)]
  have hL3 : 0 < ⟪F.N 3, endIIL x⟫ := by
    unfold endIIL; split_ifs with hL'
    · exact viewM74_3_pos F hL'
    · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 2 (by decide)]
  have hL0 : ⟪F.N 0, endIIL x⟫ < 0 := by
    unfold endIIL; split_ifs
    · dsimp [viewM74]; rw [inner_capView_0]; nlinarith [F.neg 0 6 (by decide)]
    · rw [F.inner_sub, F.zero 0 2 (by decide), sub_zero]; exact F.neg 0 3 (by decide)
  have hL2 : ⟪F.N 2, endIIL x⟫ < 0 := by
    unfold endIIL; split_ifs
    · exact (n2_viewM74_sign F hC).1.1 hD
    · rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 3 (by decide)
  have hL5 : ⟪F.N 5, endIIL x⟫ < 0 := by
    unfold endIIL; split_ifs
    · dsimp [viewM74]; rw [inner_capView_5]; nlinarith [F.neg 5 0 (by decide)]
    · rw [F.inner_sub, F.zero 5 2 (by decide), sub_zero]; exact F.neg 5 3 (by decide)
  have hR1 : ⟪F.N 1, endIIR x⟫ < 0 := by
    unfold endIIR; split_ifs
    · dsimp [viewM27]; rw [inner_capView_1]; nlinarith [F.neg 1 2 (by decide)]
    · rw [F.inner_sub, F.zero 1 6 (by decide), sub_zero]; exact F.neg 1 3 (by decide)
  have hR4 : ⟪F.N 4, endIIR x⟫ < 0 := by
    unfold endIIR; split_ifs
    · exact (n4_viewM27_sign F hC).1.1 hD
    · rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; exact F.neg 4 3 (by decide)
  refine ⟨fun t ht ht7 => ?_, ?_, fun t ht => ?_⟩
  · dsimp [midII]; rw [inner_add_right]
    simp only [UII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · linarith [hL3, hR.1 3 (by decide)]
    · linarith [hL.1 6 (by decide), hL6]
    · exact absurd rfl ht7
    · linarith [hL8, hR.1 8 (by decide)]
  · dsimp [midII]; rw [inner_add_right]
    linarith [hL.1 7 (by decide), hR.1 7 (by decide)]
  · dsimp [midII]; rw [inner_add_right]
    simp only [DnII, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · linarith [hL0, hR.2 0 (by decide)]
    · linarith [hL.2 1 (by decide), hR1]
    · linarith [hL2, hR.2 2 (by decide)]
    · linarith [hL.2 4 (by decide), hR4]
    · linarith [hL5, hR.2 5 (by decide)]

private theorem det3_ne_zero_of_one_normal {A B u v N : ℝ³}
    (hNA : ⟪N, A⟫ = 0) (hNB : ⟪N, B⟫ = 0) (hNu : ⟪N, u⟫ ≠ 0) (hv : det3 A B v ≠ 0) :
    det3 A B u ≠ 0 := by
  intro h0
  have h3 : det3 A B v • u - det3 A B u • v = det3 u B v • A + det3 A u v • B := by
    ext k
    have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
    rcases hk k with rfl | rfl | rfl <;> ring
  have hdot := congrArg (fun z => ⟪N, z⟫) h3
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hNA, hNB, h0,
    mul_zero, zero_mul, sub_zero, add_zero] at hdot
  exact mul_ne_zero hv hNu hdot

private theorem det3_ne_zero_of_two_normals {A B u v N₁ N₂ : ℝ³}
    (hN1u : ⟪N₁, u⟫ = 0) (hN1A : ⟪N₁, A⟫ = 0) (hN1B : ⟪N₁, B⟫ ≠ 0)
    (hN2u : ⟪N₂, u⟫ = 0) (hN2A : ⟪N₂, A⟫ ≠ 0)
    (hv : det3 A B v ≠ 0) (hu : u ≠ 0) : det3 A B u ≠ 0 := by
  intro h0
  have h3 : det3 A B v • u - det3 A B u • v = det3 u B v • A + det3 A u v • B := by
    ext k
    have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
    rcases hk k with rfl | rfl | rfl <;> ring
  rw [h0, zero_smul, sub_zero] at h3
  have hdot1 := congrArg (fun z => ⟪N₁, z⟫) h3
  simp only [inner_add_right, real_inner_smul_right, hN1u, hN1A, mul_zero, zero_add] at hdot1
  have hAuv : det3 A u v = 0 := (mul_eq_zero.mp hdot1.symm).resolve_right hN1B
  rw [hAuv, zero_smul, add_zero] at h3
  have hdot2 := congrArg (fun z => ⟪N₂, z⟫) h3
  simp only [real_inner_smul_right, hN2u, mul_zero] at hdot2
  have huBv : det3 u B v = 0 := (mul_eq_zero.mp hdot2.symm).resolve_right hN2A
  rw [huBv, zero_smul] at h3
  exact hu ((smul_eq_zero.mp h3).resolve_left hv)

private theorem diagFront_of_signs {y c a b u : ℝ³} {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1)
    (hvol : 0 < ρ * det3 (c - y) (b - a) (y - a))
    (hview : 0 < ρ * det3 (c - y) (b - a) u) : DiagFront y c a b u := by
  unfold DiagFront
  have hsq : ρ ^ 2 = 1 := by rcases hρ with rfl | rfl <;> norm_num
  have hprod : 0 < (ρ * det3 (c - y) (b - a) (y - a)) * (ρ * det3 (c - y) (b - a) u) :=
    mul_pos hvol hview
  calc 0 < (ρ * det3 (c - y) (b - a) (y - a)) * (ρ * det3 (c - y) (b - a) u) := hprod
    _ = ρ ^ 2 * (det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) u) := by ring
    _ = det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) u := by rw [hsq, one_mul]

private theorem diagFront_swap_yc {y c a b u : ℝ³} (h : DiagFront y c a b u) :
    DiagFront c y a b u := by
  unfold DiagFront at *
  have h1 : det3 (y - c) (b - a) (c - a) = -det3 (c - y) (b - a) (y - a) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have h2 : det3 (y - c) (b - a) u = -det3 (c - y) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [h1, h2, neg_mul_neg]; exact h

private theorem diagFront_swap_ab {y c a b u : ℝ³} (h : DiagFront y c a b u) :
    DiagFront y c b a u := by
  unfold DiagFront at *
  have h1 : det3 (c - y) (a - b) (y - b) = -det3 (c - y) (b - a) (y - a) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have h2 : det3 (c - y) (a - b) u = -det3 (c - y) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [h1, h2, neg_mul_neg]; exact h

private theorem det3_quad_decomp (p0 p1 p2 p3 u : ℝ³) :
    det3 (p2 - p0) (p3 - p1) u = det3 (p1 - p0) (p2 - p0) u + det3 (p3 - p2) (p0 - p2) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

private theorem det3_quad_decomp' (p0 p1 p2 p3 u : ℝ³) :
    det3 (p2 - p0) (p1 - p3) u = -(det3 (p1 - p0) (p2 - p0) u + det3 (p3 - p2) (p0 - p2) u) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

set_option maxHeartbeats 800000 in
/-- **ES(i), apex labelling and convexity.**  The rim `x ∘ cII` is strictly convex at `midII x` with a sign `ρ`,
weakly convex (same `ρ`) at the two ends, and has the apex labelling `(apexA, apexE)` (`ApexPat`, an open condition)
at both ends and at the middle.  At the ends the rim is NOT strictly convex in general (at `M74` the facet `046` is
edge-on, so `0 4 6` are collinear on the screen). -/
theorem regionII_apex (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) (hb : brk24 x ≠ 0) :
    ∃ ρ : ℝ, StrictConvex5 (fun i => x (cII i)) (midII x) ρ ∧
      WeakConvex5 (fun i => x (cII i)) (endIIL x) ρ ∧ WeakConvex5 (fun i => x (cII i)) (endIIR x) ρ ∧
      ApexPat (fun i => x (cII i)) (endIIL x) (apexA x) (apexE x) ∧
      ApexPat (fun i => x (cII i)) (midII x) (apexA x) (apexE x) ∧
      ApexPat (fun i => x (cII i)) (endIIR x) (apexA x) (apexE x) := by
  have hx : Function.Injective x := EdgeViewLink.inj_of_fac24 F
  have hL : CellLe F UII DnII (endIIL x) := regionII_left F hC hD
  have hR : CellLe F UII DnII (endIIR x) := regionII_right F hC hD
  obtain ⟨hM1, hM2, hM3⟩ := regionII_mid F hC hD
  have hM : CellLe F UII DnII (midII x) :=
    ⟨fun t ht => by
      by_cases ht7 : t = 7
      · subst ht7; exact hM2
      · exact (hM1 t ht ht7).le,
     fun t ht => (hM3 t ht).le⟩
  obtain ⟨a, ha⟩ := cellAt_of_mid F hM1 hM2 hM3
  choose ea hea eb heb h0a h0b h1a h1b hs using cycII
  let D : h21b_SilDataL 5 x cII (midII x) a := {
    A := fun i => F.N (ea i)
    B := fun i => F.N (eb i)
    fA := fun i => F.f (ea i)
    fB := fun i => F.f (eb i)
    hA := fun i => F.hN (ea i)
    hB := fun i => F.hN (eb i)
    zA0 := fun i => F.zero _ _ (h0a i)
    zA1 := fun i => F.zero _ _ (h1a i)
    zB0 := fun i => F.zero _ _ (h0b i)
    zB1 := fun i => F.zero _ _ (h1b i)
    nA := fun i q => F.le _ q
    nB := fun i q => F.le _ q
    strict := fun i q _ _ => by
      rcases hs i q (by assumption) (by assumption) with h | h
      · exact Or.inl (F.neg _ _ h)
      · exact Or.inr (F.neg _ _ h)
    up := fun i => by
      rcases (hM.1 _ (hea i)).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, ha.1 _ (hea i)⟩
    dn := fun i => by
      rcases (hM.2 _ (heb i)).lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [h]; simp, by linarith [ha.2 _ (heb i)]⟩ }
  choose μ hμ0 hd using fun i => h21b_exists_mu (by decide) hx injII D i
  have hsg := h21b_sign_agree (by decide) hx injII D μ hμ0 hd
  obtain ⟨ρ, hρ_pm, hρμ⟩ : ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∀ i : ZMod 5, 0 < ρ * μ i := by
    rcases hsg with hpos | hneg
    · exact ⟨1, Or.inl rfl, fun i => by rw [one_mul]; exact hpos i⟩
    · exact ⟨-1, Or.inr rfl, fun i => by linarith [hneg i]⟩
  have hweak_of_cell : ∀ u, CellLe F UII DnII u → WeakConvex5 (fun i => x (cII i)) u ρ := by
    intro u hu i j hji hji1
    rw [h21b_det_eq D i (μ i) (hd i) (cII j) u]
    have hA_le : D.fA i (x (cII j)) ≤ 0 := D.nA i _
    have hB_le : D.fB i (x (cII j)) ≤ 0 := D.nB i _
    have huA : 0 ≤ ⟪D.A i, u⟫ := hu.1 _ (hea i)
    have huB : ⟪D.B i, u⟫ ≤ 0 := hu.2 _ (heb i)
    have ht1 : 0 ≤ D.fA i (x (cII j)) * ⟪D.B i, u⟫ := mul_nonneg_of_nonpos_of_nonpos hA_le huB
    have ht2 : 0 ≤ -(D.fB i (x (cII j)) * ⟪D.A i, u⟫) :=
      neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hB_le huA)
    have hsum : 0 ≤ D.fA i (x (cII j)) * ⟪D.B i, u⟫ - D.fB i (x (cII j)) * ⟪D.A i, u⟫ := by
      linarith
    have hmul : 0 ≤ (ρ * μ i) * (D.fA i (x (cII j)) * ⟪D.B i, u⟫ - D.fB i (x (cII j)) * ⟪D.A i, u⟫) :=
      mul_nonneg (hρμ i).le hsum
    linarith
  have hWL : WeakConvex5 (fun i => x (cII i)) (endIIL x) ρ := hweak_of_cell (endIIL x) hL
  have hWR : WeakConvex5 (fun i => x (cII i)) (endIIR x) ρ := hweak_of_cell (endIIR x) hR
  have hSM : StrictConvex5 (fun i => x (cII i)) (midII x) ρ := by
    intro i j hji hji1
    rw [h21b_det_eq D i (μ i) (hd i) (cII j) (midII x)]
    have hcj0 : cII j ≠ cII i := fun h => hji (injII h)
    have hcj1 : cII j ≠ cII (i + 1) := fun h => hji1 (injII h)
    have hstr := D.strict i (cII j) hcj0 hcj1
    have hA_le : D.fA i (x (cII j)) ≤ 0 := D.nA i _
    have hB_le : D.fB i (x (cII j)) ≤ 0 := D.nB i _
    have huA : 0 ≤ ⟪D.A i, midII x⟫ := hM.1 _ (hea i)
    have huB : ⟪D.B i, midII x⟫ < 0 := hM3 _ (heb i)
    have ht1 : 0 ≤ D.fA i (x (cII j)) * ⟪D.B i, midII x⟫ :=
      mul_nonneg_of_nonpos_of_nonpos hA_le huB.le
    have ht2 : 0 ≤ -(D.fB i (x (cII j)) * ⟪D.A i, midII x⟫) :=
      neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hB_le huA)
    have hpos_inner : 0 < D.fA i (x (cII j)) * ⟪D.B i, midII x⟫ -
        D.fB i (x (cII j)) * ⟪D.A i, midII x⟫ := by
      rcases hstr with hA_lt | hB_lt
      · linarith [mul_pos_of_neg_of_neg hA_lt huB]
      · by_cases hea7 : ea i = 7
        · have hA_lt : D.fA i (x (cII j)) < 0 := by
            change F.f (ea i) (x (cII j)) < 0
            rw [hea7]
            have hi2 : i = 2 := by
              have h0 := h0a i; have h1 := h1a i; rw [hea7] at h0 h1
              fin_cases i <;> first | rfl | (exfalso; revert h0 h1; decide)
            subst hi2
            have hnot7 : cII j ∉ s0x_S24 7 := by
              fin_cases j <;> simp at hji hji1 ⊢ <;> first | contradiction | decide
            exact F.neg 7 (cII j) hnot7
          linarith [mul_pos_of_neg_of_neg hA_lt huB]
        · have huA_pos : 0 < ⟪D.A i, midII x⟫ := hM1 _ (hea i) hea7
          linarith [mul_neg_of_neg_of_pos hB_lt huA_pos]
    have hmul : 0 < (ρ * μ i) * (D.fA i (x (cII j)) * ⟪D.B i, midII x⟫ -
        D.fB i (x (cII j)) * ⟪D.A i, midII x⟫) := mul_pos (hρμ i) hpos_inner
    linarith
  have hd_ne : det24 x ≠ 0 := by
    have h1 := HC.det3_e026_ne F
    have h2 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det24 x := by
      simp only [det24, vol3, det3_expand]; ring
    rw [← h2]; exact h1
  have T := M4.type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  -- Sign of ρ * det24 x: negative, via StrictConvex5 at (i=3, j=0) and N_2.
  have hρ_det24 : ρ * det24 x < 0 := by
    have hsc30 := hSM 3 0 (by decide) (by decide)
    change 0 < ρ * det3 (x 5 - x 2) (x 0 - x 2) (midII x) at hsc30
    have h62_neg : ⟪F.N 2, x 6 - x 2⟫ < 0 := by
      rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 6 (by decide)
    have hM2_neg : ⟪F.N 2, midII x⟫ < 0 := hM3 2 (by decide)
    have h62_det : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) = -((1 + omega5 x) * oblX6 x 5) * det24 x := by
      have h52 : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
          oblX6 x 5 • (x 6 - x 1) := by
        rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, rep_sub F 5]; module
      have h02 : x 0 - x 2 = (1 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
        rw [show x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) by abel]; module
      have h62 : x 6 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
        rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]; module
      rw [h52, h02, h62, M4.det3_frame]
      have e5 := M4.eq5 F
      have halg : oblX0 x 5 * ((-1) * 1 - 0 * (-1)) - (oblX2 x 5 - 1) * (1 * 1 - 0 * 0) +
          oblX6 x 5 * (1 * (-1) - (-1) * 0) = -((1 + omega5 x) * oblX6 x 5) := by
        linear_combination -e5
      rw [halg]
    have hpos_c : 0 < (1 + omega5 x) * oblX6 x 5 := mul_pos (by linarith) hc5
    have hsame : 0 < (-((1 + omega5 x) * oblX6 x 5) * det24 x) * det3 (x 5 - x 2) (x 0 - x 2) (midII x) := by
      rw [← h62_det]
      have hdet_rel : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) * ⟪F.N 2, midII x⟫ =
          det3 (x 5 - x 2) (x 0 - x 2) (midII x) * ⟪F.N 2, x 6 - x 2⟫ := by
        have h3 : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) • midII x -
            det3 (x 5 - x 2) (x 0 - x 2) (midII x) • (x 6 - x 2) =
            det3 (midII x) (x 0 - x 2) (x 6 - x 2) • (x 5 - x 2) +
            det3 (x 5 - x 2) (midII x) (x 6 - x 2) • (x 0 - x 2) := by
          ext k
          have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
          simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
          rcases hk k with rfl | rfl | rfl <;> ring
        have hdot := congrArg (fun z => ⟪F.N 2, z⟫) h3
        have hN52 : ⟪F.N 2, x 5 - x 2⟫ = 0 := by
          rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 2 (by decide), sub_self]
        have hN02 : ⟪F.N 2, x 0 - x 2⟫ = 0 := by
          rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 2 (by decide), sub_self]
        simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hN52, hN02,
          mul_zero, add_zero] at hdot
        rw [inner_sub_right]
        linarith
      have hne62 : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) ≠ 0 := by
        rw [h62_det]; exact mul_ne_zero (neg_ne_zero.mpr hpos_c.ne') hd_ne
      have hsq : 0 < (det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2)) ^ 2 := sq_pos_of_ne_zero hne62
      have hmul : (det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) * det3 (x 5 - x 2) (x 0 - x 2) (midII x)) *
          ⟪F.N 2, x 6 - x 2⟫ = (det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2)) ^ 2 * ⟪F.N 2, midII x⟫ := by
        calc _ = det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) *
              (det3 (x 5 - x 2) (x 0 - x 2) (midII x) * ⟪F.N 2, x 6 - x 2⟫) := by ring
          _ = det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) *
              (det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) * ⟪F.N 2, midII x⟫) := by rw [hdet_rel]
          _ = _ := by ring
      have hrhs : (det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2)) ^ 2 * ⟪F.N 2, midII x⟫ < 0 :=
        mul_neg_of_pos_of_neg hsq hM2_neg
      nlinarith
    have hmul_pos : 0 < (ρ * det3 (x 5 - x 2) (x 0 - x 2) (midII x)) *
        (-((1 + omega5 x) * oblX6 x 5) * det24 x * det3 (x 5 - x 2) (x 0 - x 2) (midII x)) :=
      mul_pos hsc30 hsame
    have hsq_mid : 0 ≤ (det3 (x 5 - x 2) (x 0 - x 2) (midII x)) ^ 2 := sq_nonneg _
    have : 0 < -((1 + omega5 x) * oblX6 x 5) * (ρ * det24 x) *
        (det3 (x 5 - x 2) (x 0 - x 2) (midII x)) ^ 2 := by linarith
    have h1 : 0 < -((1 + omega5 x) * oblX6 x 5) * (ρ * det24 x) :=
      pos_of_mul_pos_left this hsq_mid
    by_contra hle; push Not at hle; nlinarith [mul_nonneg hpos_c.le hle]
  -- 4-point volume signs:
  have h40 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, rep_sub F 4]; module
  have h60 : x 6 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
    rw [show x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) by abel]; module
  have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    rw [show x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) by abel]; module
  have hdet_0462 : det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) = -((1 + omega4 x) * oblX2 x 4) * det24 x := by
    rw [h40, h60, h20, M4.det3_frame]
    have e4 := M4.eq4 F
    have halg : (oblX0 x 4 - 1) * (0 * 0 - 1 * 1) - oblX2 x 4 * ((-1) * 0 - 1 * (-1)) +
        oblX6 x 4 * ((-1) * 1 - 0 * (-1)) = -((1 + omega4 x) * oblX2 x 4) := by
      linear_combination -e4
    rw [halg]
  have hvol_0462 : 0 < ρ * det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) := by
    rw [hdet_0462]
    have hpos : 0 < (1 + omega4 x) * oblX2 x 4 := mul_pos (by linarith) hb4
    nlinarith [mul_neg_of_pos_of_neg hpos hρ_det24]
  have hdet_5206 : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) = -((1 + omega5 x) * oblX6 x 5) * det24 x := by
    have h52 : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, rep_sub F 5]; module
    have h02 : x 0 - x 2 = (1 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
      rw [show x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) by abel]; module
    have h62 : x 6 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
      rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]; module
    rw [h52, h02, h62, M4.det3_frame]
    have e5 := M4.eq5 F
    have halg : oblX0 x 5 * ((-1) * 1 - 0 * (-1)) - (oblX2 x 5 - 1) * (1 * 1 - 0 * 0) +
        oblX6 x 5 * (1 * (-1) - (-1) * 0) = -((1 + omega5 x) * oblX6 x 5) := by
      linear_combination -e5
    rw [halg]
  have hvol_5206 : 0 < ρ * det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) := by
    rw [hdet_5206]
    have hpos : 0 < (1 + omega5 x) * oblX6 x 5 := mul_pos (by linarith) hc5
    nlinarith [mul_neg_of_pos_of_neg hpos hρ_det24]
  have hsame_sign_ρ : ∀ {a b : ℝ}, 0 < a * b → 0 < ρ * a → 0 < ρ * b := by
    intro a b hab hpa
    have h1 : 0 < (ρ * a) * (a * b) := mul_pos hpa hab
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have : 0 < a ^ 2 * (ρ * b) := by linarith
    exact pos_of_mul_pos_right this ha2
  have hdet_same_ρ : ∀ {N A B u v : ℝ³},
      ⟪N, A⟫ = 0 → ⟪N, B⟫ = 0 → ⟪N, u⟫ < 0 → ⟪N, v⟫ < 0 →
      det3 A B v ≠ 0 → 0 < ρ * det3 A B v → 0 < ρ * det3 A B u := by
    intro N A B u v hNA hNB hNu hNv hvne hρv
    have h3 : det3 A B v • u - det3 A B u • v = det3 u B v • A + det3 A u v • B := by
      ext k
      have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3_expand]
      rcases hk k with rfl | rfl | rfl <;> ring
    have hdot := congrArg (fun z => ⟪N, z⟫) h3
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hNA, hNB,
      mul_zero, add_zero] at hdot
    have hrel : det3 A B v * ⟪N, u⟫ = det3 A B u * ⟪N, v⟫ := by linarith
    have hmul : (det3 A B v * det3 A B u) * ⟪N, v⟫ = (det3 A B v) ^ 2 * ⟪N, u⟫ := by
      calc (det3 A B v * det3 A B u) * ⟪N, v⟫ = det3 A B v * (det3 A B u * ⟪N, v⟫) := by ring
        _ = det3 A B v * (det3 A B v * ⟪N, u⟫) := by rw [← hrel]
        _ = _ := by ring
    have hsq : 0 < (det3 A B v) ^ 2 := sq_pos_of_ne_zero hvne
    have hneg : (det3 A B v) ^ 2 * ⟪N, u⟫ < 0 := mul_neg_of_pos_of_neg hsq hNu
    have hvu : 0 < det3 A B v * det3 A B u := by
      by_contra hle; push Not at hle; nlinarith [mul_nonneg_of_nonpos_of_nonpos hle hNv.le]
    exact hsame_sign_ρ hvu hρv
  have hne_0462 : det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) ≠ 0 := by
    rw [hdet_0462]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_pos (by linarith) hb4).ne') hd_ne
  have hne_5206 : det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) ≠ 0 := by
    rw [hdet_5206]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_pos (by linarith) hc5).ne') hd_ne
  have hN4_40 : ⟪F.N 4, x 4 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
  have hN4_60 : ⟪F.N 4, x 6 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 4 6 (by decide), F.zero 4 0 (by decide), sub_self]
  have hN4_50 : ⟪F.N 4, x 5 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]; exact F.neg 4 5 (by decide)
  have hN4_20 : ⟪F.N 4, x 2 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]; exact F.neg 4 2 (by decide)
  have hN2_52 : ⟪F.N 2, x 5 - x 2⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 2 (by decide), sub_self]
  have hN2_02 : ⟪F.N 2, x 0 - x 2⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 2 (by decide), sub_self]
  have hN2_42 : ⟪F.N 2, x 4 - x 2⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 4 (by decide)
  have hN2_62 : ⟪F.N 2, x 6 - x 2⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 6 (by decide)
  have hvol_omit2 : 0 < ρ * det3 (x 4 - x 5) (x 6 - x 0) (x 5 - x 0) := by
    rw [show det3 (x 4 - x 5) (x 6 - x 0) (x 5 - x 0) = det3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0) by
      simp only [det3_expand, PiLp.sub_apply]; ring]
    exact hdet_same_ρ hN4_40 hN4_60 hN4_50 hN4_20 hne_0462 hvol_0462
  have hvol_omit5 : 0 < (-ρ) * det3 (x 2 - x 4) (x 6 - x 0) (x 4 - x 0) := by
    rw [show det3 (x 2 - x 4) (x 6 - x 0) (x 4 - x 0) = -det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) by
      simp only [det3_expand, PiLp.sub_apply]; ring]
    linarith [hvol_0462]
  have hvol_omit4 : 0 < ρ * det3 (x 6 - x 5) (x 2 - x 0) (x 5 - x 0) := by
    rw [show det3 (x 6 - x 5) (x 2 - x 0) (x 5 - x 0) = det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) by
      simp only [det3_expand, PiLp.sub_apply]; ring]
    exact hvol_5206
  have hvol_omit6 : 0 < (-ρ) * det3 (x 4 - x 5) (x 0 - x 2) (x 5 - x 2) := by
    rw [show det3 (x 4 - x 5) (x 0 - x 2) (x 5 - x 2) = -det3 (x 5 - x 2) (x 0 - x 2) (x 4 - x 2) by
      simp only [det3_expand, PiLp.sub_apply]; ring]
    have h := hdet_same_ρ hN2_52 hN2_02 hN2_42 hN2_62 hne_5206 hvol_5206
    linarith
  have hbrk_det : det3 (x 6 - x 5) (x 2 - x 4) (x 5 - x 4) = -brk24 x * det24 x := by
    have heq : det3 (x 6 - x 5) (x 2 - x 4) (x 5 - x 4) = -vol3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) := by
      simp only [vol3, det3_expand, PiLp.sub_apply]; ring
    rw [heq, show brk24 x = vol3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) / det24 x from rfl]
    field_simp [hd_ne]
  have hvol_omit0_pos : 0 < brk24 x → 0 < ρ * det3 (x 6 - x 5) (x 2 - x 4) (x 5 - x 4) := by
    intro hbp; rw [hbrk_det]; nlinarith [mul_neg_of_pos_of_neg hbp hρ_det24]
  have hvol_omit0_neg : brk24 x < 0 → 0 < (-ρ) * det3 (x 2 - x 4) (x 6 - x 5) (x 4 - x 5) := by
    intro hbn
    rw [show det3 (x 2 - x 4) (x 6 - x 5) (x 4 - x 5) = det3 (x 6 - x 5) (x 2 - x 4) (x 5 - x 4) by
      simp only [det3_expand, PiLp.sub_apply]; ring]
    rw [hbrk_det]
    nlinarith [mul_pos_of_neg_of_neg hbn hρ_det24]
  -- Helper: from WeakConvex5 + 5 non-vanishing diagonal view determinants -> ApexPat
  have apex_of_weak : ∀ u : ℝ³, WeakConvex5 (fun i => x (cII i)) u ρ →
      det3 (x 4 - x 5) (x 6 - x 0) u ≠ 0 →
      det3 (x 4 - x 5) (x 0 - x 2) u ≠ 0 →
      det3 (x 6 - x 5) (x 2 - x 0) u ≠ 0 →
      det3 (x 2 - x 4) (x 6 - x 0) u ≠ 0 →
      det3 (x 6 - x 5) (x 2 - x 4) u ≠ 0 →
      ApexPat (fun i => x (cII i)) u (apexA x) (apexE x) := by
    intro u hWu h2 h6 h4 h5 h0
    have hρ_ne : ρ ≠ 0 := by rcases hρ_pm with h | h <;> rw [h] <;> norm_num
    have hneg_ρ_ne : -ρ ≠ 0 := neg_ne_zero.mpr hρ_ne
    have hvu_omit2 : 0 < ρ * det3 (x 4 - x 5) (x 6 - x 0) u := by
      have ht1 : 0 ≤ ρ * det3 (x 4 - x 0) (x 6 - x 0) u := hWu 0 2 (by decide) (by decide)
      have ht2 : 0 ≤ ρ * det3 (x 0 - x 5) (x 6 - x 5) u := hWu 4 2 (by decide) (by decide)
      have hsum : det3 (x 4 - x 5) (x 6 - x 0) u =
          det3 (x 4 - x 0) (x 6 - x 0) u + det3 (x 0 - x 5) (x 6 - x 5) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have hge : 0 ≤ ρ * det3 (x 4 - x 5) (x 6 - x 0) u := by rw [hsum]; linarith
      exact lt_of_le_of_ne hge (Ne.symm (mul_ne_zero hρ_ne h2))
    have hvu_omit6 : 0 < (-ρ) * det3 (x 4 - x 5) (x 0 - x 2) u := by
      have ht1 : 0 ≤ ρ * det3 (x 4 - x 0) (x 2 - x 0) u := hWu 0 3 (by decide) (by decide)
      have ht2 : 0 ≤ ρ * det3 (x 5 - x 2) (x 0 - x 2) u := hWu 3 0 (by decide) (by decide)
      have hsum : -det3 (x 4 - x 5) (x 0 - x 2) u =
          det3 (x 4 - x 0) (x 2 - x 0) u + det3 (x 5 - x 2) (x 0 - x 2) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have hge : 0 ≤ (-ρ) * det3 (x 4 - x 5) (x 0 - x 2) u := by
        have : (-ρ) * det3 (x 4 - x 5) (x 0 - x 2) u = ρ * (-det3 (x 4 - x 5) (x 0 - x 2) u) := by ring
        rw [this, hsum]; linarith
      exact lt_of_le_of_ne hge (Ne.symm (mul_ne_zero hneg_ρ_ne h6))
    have hvu_omit4 : 0 < ρ * det3 (x 6 - x 5) (x 2 - x 0) u := by
      have ht1 : 0 ≤ ρ * det3 (x 2 - x 6) (x 0 - x 6) u := hWu 2 0 (by decide) (by decide)
      have ht2 : 0 ≤ ρ * det3 (x 5 - x 2) (x 0 - x 2) u := hWu 3 0 (by decide) (by decide)
      have hsum : det3 (x 6 - x 5) (x 2 - x 0) u =
          det3 (x 2 - x 6) (x 0 - x 6) u + det3 (x 5 - x 2) (x 0 - x 2) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have hge : 0 ≤ ρ * det3 (x 6 - x 5) (x 2 - x 0) u := by rw [hsum]; linarith
      exact lt_of_le_of_ne hge (Ne.symm (mul_ne_zero hρ_ne h4))
    have hvu_omit5 : 0 < (-ρ) * det3 (x 2 - x 4) (x 6 - x 0) u := by
      have ht1 : 0 ≤ ρ * det3 (x 4 - x 0) (x 6 - x 0) u := hWu 0 2 (by decide) (by decide)
      have ht2 : 0 ≤ ρ * det3 (x 2 - x 6) (x 0 - x 6) u := hWu 2 0 (by decide) (by decide)
      have hsum : -det3 (x 2 - x 4) (x 6 - x 0) u =
          det3 (x 4 - x 0) (x 6 - x 0) u + det3 (x 2 - x 6) (x 0 - x 6) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have hge : 0 ≤ (-ρ) * det3 (x 2 - x 4) (x 6 - x 0) u := by
        have : (-ρ) * det3 (x 2 - x 4) (x 6 - x 0) u = ρ * (-det3 (x 2 - x 4) (x 6 - x 0) u) := by ring
        rw [this, hsum]; linarith
      exact lt_of_le_of_ne hge (Ne.symm (mul_ne_zero hneg_ρ_ne h5))
    have hvu_omit0 : 0 < ρ * det3 (x 6 - x 5) (x 2 - x 4) u := by
      have ht1 : 0 ≤ ρ * det3 (x 6 - x 4) (x 2 - x 4) u := hWu 1 3 (by decide) (by decide)
      have ht2 : 0 ≤ ρ * det3 (x 5 - x 2) (x 4 - x 2) u := hWu 3 1 (by decide) (by decide)
      have hsum : det3 (x 6 - x 5) (x 2 - x 4) u =
          det3 (x 6 - x 4) (x 2 - x 4) u + det3 (x 5 - x 2) (x 4 - x 2) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have hge : 0 ≤ ρ * det3 (x 6 - x 5) (x 2 - x 4) u := by rw [hsum]; linarith
      exact lt_of_le_of_ne hge (Ne.symm (mul_ne_zero hρ_ne h0))
    have hneg_ρ_pm : -ρ = 1 ∨ -ρ = -1 := by rcases hρ_pm with h | h <;> rw [h] <;> norm_num
    have hd_omit2 : DiagFront (x 5) (x 4) (x 0) (x 6) u :=
      diagFront_of_signs hρ_pm hvol_omit2 hvu_omit2
    have hd_omit6 : DiagFront (x 5) (x 4) (x 2) (x 0) u :=
      diagFront_of_signs hneg_ρ_pm hvol_omit6 hvu_omit6
    have hd_omit4 : DiagFront (x 5) (x 6) (x 0) (x 2) u :=
      diagFront_of_signs hρ_pm hvol_omit4 hvu_omit4
    have hd_omit5 : DiagFront (x 4) (x 2) (x 0) (x 6) u :=
      diagFront_of_signs hneg_ρ_pm hvol_omit5 hvu_omit5
    dsimp [ApexPat, apexA, apexE]
    by_cases hbp : 0 < brk24 x
    · simp only [hbp, ↓reduceIte]
      refine ⟨Or.inl trivial, ?_, ?_, ?_, ?_, ?_⟩
      · change DiagFront (x 5) (x 4) (x 0) (x 6) u; exact hd_omit2
      · change DiagFront (x 5) (x 4) (x 2) (x 0) u; exact hd_omit6
      · change DiagFront (x 5) (x 6) (x 0) (x 2) u; exact hd_omit4
      · change DiagFront (x 5) (x 6) (x 4) (x 2) u
        exact diagFront_of_signs hρ_pm (hvol_omit0_pos hbp) hvu_omit0
      · change DiagFront (x 4) (x 2) (x 0) (x 6) u; exact hd_omit5
    · have hbn : brk24 x < 0 := lt_of_le_of_ne (not_lt.mp hbp) hb
      simp only [hbp, ↓reduceIte]
      have hvu_omit0' : 0 < (-ρ) * det3 (x 2 - x 4) (x 6 - x 5) u := by
        rw [show det3 (x 2 - x 4) (x 6 - x 5) u = -det3 (x 6 - x 5) (x 2 - x 4) u by
          simp only [det3_expand, PiLp.sub_apply]; ring]
        linarith [hvu_omit0]
      refine ⟨Or.inr trivial, ?_, ?_, ?_, ?_, ?_⟩
      · change DiagFront (x 4) (x 5) (x 0) (x 2) u
        exact diagFront_swap_yc (diagFront_swap_ab hd_omit6)
      · change DiagFront (x 4) (x 5) (x 6) (x 0) u
        exact diagFront_swap_yc (diagFront_swap_ab hd_omit2)
      · change DiagFront (x 4) (x 2) (x 0) (x 6) u; exact hd_omit5
      · change DiagFront (x 4) (x 2) (x 5) (x 6) u
        exact diagFront_of_signs hneg_ρ_pm (hvol_omit0_neg hbn) hvu_omit0'
      · change DiagFront (x 5) (x 6) (x 0) (x 2) u; exact hd_omit4
  -- Helper: if T1 + T2 = det3(c - y)(b - a)u and 0 ≤ ρ*T1, 0 ≤ ρ*T2 and (T1 ≠ 0 ∨ T2 ≠ 0), then det ≠ 0
  have ne_of_sum : ∀ {D T1 T2 : ℝ}, D = T1 + T2 → 0 ≤ ρ * T1 → 0 ≤ ρ * T2 → (T1 ≠ 0 ∨ T2 ≠ 0) → D ≠ 0 := by
    intro D T1 T2 hD_eq h1 h2 hne h0
    have hsum0 : ρ * T1 + ρ * T2 = 0 := by rw [← mul_add, ← hD_eq, h0, mul_zero]
    have hρne : ρ ≠ 0 := by rcases hρ_pm with h | h <;> rw [h] <;> norm_num
    rcases hne with hne1 | hne2
    · exact hne1 ((mul_eq_zero.mp (by linarith : ρ * T1 = 0)).resolve_left hρne)
    · exact hne2 ((mul_eq_zero.mp (by linarith : ρ * T2 = 0)).resolve_left hρne)
  -- Non-vanishing at endIIL x:
  have hapex_L : ApexPat (fun i => x (cII i)) (endIIL x) (apexA x) (apexE x) := by
    have hN2_L : ⟪F.N 2, endIIL x⟫ < 0 := by
      unfold endIIL; split_ifs with hL_if
      · exact (n2_viewM74_sign F hC).1.1 hD
      · rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 3 (by decide)
    have hN3_L : 0 < ⟪F.N 3, endIIL x⟫ := by
      unfold endIIL; split_ifs with hL_if
      · exact viewM74_3_pos F hL_if
      · rw [F.inner_sub, F.zero 3 3 (by decide), zero_sub]; linarith [F.neg 3 2 (by decide)]
    have hL_ne : endIIL x ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN3_L; exact lt_irrefl _ hN3_L
    have hN4_L_ne : ¬ LeftM74 x → ⟪F.N 4, endIIL x⟫ ≠ 0 := by
      intro hnot; simp only [endIIL, hnot, ↓reduceIte, h4_equiv F]
      have hk4 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      dsimp [LeftM74] at hnot; push Not at hnot
      exact (mul_neg_of_pos_of_neg hk4 hnot).ne
    have hne_omit6_L : det3 (x 4 - x 5) (x 0 - x 2) (endIIL x) ≠ 0 := by
      rw [← neg_ne_zero]
      refine ne_of_sum (show -det3 (x 4 - x 5) (x 0 - x 2) (endIIL x) =
          det3 (x 4 - x 0) (x 2 - x 0) (endIIL x) + det3 (x 5 - x 2) (x 0 - x 2) (endIIL x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWL 0 3 (by decide) (by decide)) (hWL 3 0 (by decide) (by decide)) (Or.inr ?_)
      exact det3_ne_zero_of_one_normal hN2_52 hN2_02 hN2_L.ne hne_5206
    have hne_omit4_L : det3 (x 6 - x 5) (x 2 - x 0) (endIIL x) ≠ 0 := by
      refine ne_of_sum (show det3 (x 6 - x 5) (x 2 - x 0) (endIIL x) =
          det3 (x 2 - x 6) (x 0 - x 6) (endIIL x) + det3 (x 5 - x 2) (x 0 - x 2) (endIIL x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWL 2 0 (by decide) (by decide)) (hWL 3 0 (by decide) (by decide)) (Or.inr ?_)
      exact det3_ne_zero_of_one_normal hN2_52 hN2_02 hN2_L.ne hne_5206
    have hne_omit2_L : det3 (x 4 - x 5) (x 6 - x 0) (endIIL x) ≠ 0 := by
      refine ne_of_sum (show det3 (x 4 - x 5) (x 6 - x 0) (endIIL x) =
          det3 (x 4 - x 0) (x 6 - x 0) (endIIL x) + det3 (x 0 - x 5) (x 6 - x 5) (endIIL x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWL 0 2 (by decide) (by decide)) (hWL 4 2 (by decide) (by decide)) ?_
      by_cases hL_if : LeftM74 x
      · right
        have hN4_M74 : ⟪F.N 4, viewM74 x⟫ = 0 := by
          dsimp [viewM74]; rw [inner_capView_4]
          rw [show (1 + omega4 x) - omega4 x * (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring, mul_zero]
        have hN7_M74 : ⟪F.N 7, viewM74 x⟫ = 0 := by
          dsimp [viewM74]; rw [inner_capView_7]
          rw [show -omega3 x * (1 + omega4 x) + (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring, mul_zero]
        have hM74_eq : endIIL x = viewM74 x := by simp only [endIIL, hL_if, ↓reduceIte]
        rw [hM74_eq]
        rw [show det3 (x 0 - x 5) (x 6 - x 5) (viewM74 x) = det3 (x 6 - x 0) (x 5 - x 0) (viewM74 x) by
          simp only [det3_expand, PiLp.sub_apply]; ring]
        exact det3_ne_zero_of_two_normals hN4_M74 hN4_60 hN4_50.ne hN7_M74
          (by rw [F.inner_sub, F.zero 7 6 (by decide), zero_sub]; exact neg_ne_zero.mpr (F.neg 7 0 (by decide)).ne)
          (by rw [show det3 (x 6 - x 0) (x 5 - x 0) (x 2 - x 0) = -det3 (x 5 - x 2) (x 0 - x 2) (x 6 - x 2) by
              simp only [det3_expand, PiLp.sub_apply]; ring]; exact neg_ne_zero.mpr hne_5206)
          (by rw [← hM74_eq]; exact hL_ne)
      · left; exact det3_ne_zero_of_one_normal hN4_40 hN4_60 (hN4_L_ne hL_if) hne_0462
    have hne_omit5_L : det3 (x 2 - x 4) (x 6 - x 0) (endIIL x) ≠ 0 := by
      by_cases hL_if : LeftM74 x
      · have hM74_eq : endIIL x = viewM74 x := by simp only [endIIL, hL_if, ↓reduceIte]
        rw [hM74_eq]
        have h24 : x 2 - x 4 = (-oblX0 x 4) • (x 0 - x 1) + (1 - oblX2 x 4) • (x 2 - x 1) +
            (-oblX6 x 4) • (x 6 - x 1) := by
          rw [show x 2 - x 4 = (x 2 - x 1) - (x 4 - x 1) by abel, rep_sub F 4]; module
        have hdet : det3 (x 2 - x 4) (x 6 - x 0) (viewM74 x) =
            ((1 + omega3 x) * (1 + omega4 x)) * det24 x := by
          rw [h24, h60]; dsimp [viewM74, capView]; rw [M4.det3_frame]
          have e4 := M4.eq4 F
          have halg : (-oblX0 x 4) * (0 * (omega3 x * omega4 x - 1) - 1 * (1 + omega3 x)) -
              (1 - oblX2 x 4) * ((-1) * (omega3 x * omega4 x - 1) - 1 * (1 + omega4 x)) +
              (-oblX6 x 4) * ((-1) * (1 + omega3 x) - 0 * (1 + omega4 x)) =
              (1 + omega3 x) * (1 + omega4 x) := by
            linear_combination (1 + omega3 x) * e4
          rw [halg]
        rw [hdet]
        exact mul_ne_zero (mul_pos (by linarith) (by linarith)).ne' hd_ne
      · rw [← neg_ne_zero]
        refine ne_of_sum (show -det3 (x 2 - x 4) (x 6 - x 0) (endIIL x) =
            det3 (x 4 - x 0) (x 6 - x 0) (endIIL x) + det3 (x 2 - x 6) (x 0 - x 6) (endIIL x) by
            simp only [det3_expand, PiLp.sub_apply]; ring)
          (hWL 0 2 (by decide) (by decide)) (hWL 2 0 (by decide) (by decide)) (Or.inl ?_)
        exact det3_ne_zero_of_one_normal hN4_40 hN4_60 (hN4_L_ne hL_if) hne_0462
    have hne_omit0_L : det3 (x 6 - x 5) (x 2 - x 4) (endIIL x) ≠ 0 := by
      refine ne_of_sum (show det3 (x 6 - x 5) (x 2 - x 4) (endIIL x) =
          det3 (x 6 - x 4) (x 2 - x 4) (endIIL x) + det3 (x 5 - x 2) (x 4 - x 2) (endIIL x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWL 1 3 (by decide) (by decide)) (hWL 3 1 (by decide) (by decide)) (Or.inl ?_)
      by_cases hL_if : LeftM74 x
      · have hN4_M74 : ⟪F.N 4, viewM74 x⟫ = 0 := by
          dsimp [viewM74]; rw [inner_capView_4]
          rw [show (1 + omega4 x) - omega4 x * (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring, mul_zero]
        have hN7_M74 : ⟪F.N 7, viewM74 x⟫ = 0 := by
          dsimp [viewM74]; rw [inner_capView_7]
          rw [show -omega3 x * (1 + omega4 x) + (1 + omega3 x) + (omega3 x * omega4 x - 1) = 0 by ring, mul_zero]
        have hM74_eq : endIIL x = viewM74 x := by simp only [endIIL, hL_if, ↓reduceIte]
        rw [hM74_eq]
        exact det3_ne_zero_of_two_normals hN4_M74
          (by rw [F.inner_sub, F.zero 4 6 (by decide), F.zero 4 4 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 4 4 (by decide), sub_zero]; exact (F.neg 4 2 (by decide)).ne)
          hN7_M74
          (by rw [F.inner_sub, F.zero 7 6 (by decide), zero_sub]; exact neg_ne_zero.mpr (F.neg 7 4 (by decide)).ne)
          (by rw [show det3 (x 6 - x 4) (x 2 - x 4) (x 0 - x 4) = -det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) by
              simp only [det3_expand, PiLp.sub_apply]; ring]; exact neg_ne_zero.mpr hne_0462)
          (by rw [← hM74_eq]; exact hL_ne)
      · have h32_eq : endIIL x = x 3 - x 2 := by simp only [endIIL, hL_if, ↓reduceIte]
        rw [h32_eq]
        rw [show det3 (x 6 - x 4) (x 2 - x 4) (x 3 - x 2) = -det3 (x 6 - x 2) (x 4 - x 2) (x 3 - x 2) by
          simp only [det3_expand, PiLp.sub_apply]; ring, neg_ne_zero]
        exact det3_ne_zero_of_two_normals
          (by rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 7 6 (by decide), F.zero 7 2 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 7 2 (by decide), sub_zero]; exact (F.neg 7 4 (by decide)).ne)
          (by rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 6 2 (by decide), sub_zero]; exact (F.neg 6 6 (by decide)).ne)
          (by rw [show det3 (x 6 - x 2) (x 4 - x 2) (x 0 - x 2) = det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) by
              simp only [det3_expand, PiLp.sub_apply]; ring]; exact hne_0462)
          (by rw [← h32_eq]; exact hL_ne)
    exact apex_of_weak (endIIL x) hWL hne_omit2_L hne_omit6_L hne_omit4_L hne_omit5_L hne_omit0_L
  -- Non-vanishing at endIIR x:
  have hapex_R : ApexPat (fun i => x (cII i)) (endIIR x) (apexA x) (apexE x) := by
    have hN4_R : ⟪F.N 4, endIIR x⟫ < 0 := by
      unfold endIIR; split_ifs with hR_if
      · exact (n4_viewM27_sign F hC).1.1 hD
      · rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]; exact F.neg 4 3 (by decide)
    have hN3_R : 0 < ⟪F.N 3, endIIR x⟫ := by
      unfold endIIR; split_ifs with hR_if
      · exact viewM27_3_pos F hR_if
      · rw [F.inner_sub, F.zero 3 3 (by decide), zero_sub]; linarith [F.neg 3 6 (by decide)]
    have hR_ne : endIIR x ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN3_R; exact lt_irrefl _ hN3_R
    have hN2_R_ne : ¬ RightM27 x → ⟪F.N 2, endIIR x⟫ ≠ 0 := by
      intro hnot; simp only [endIIR, hnot, ↓reduceIte, h2_equiv F]
      have hk2 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      dsimp [RightM27] at hnot; push Not at hnot
      exact (mul_neg_of_pos_of_neg hk2 hnot).ne
    have hne_omit2_R : det3 (x 4 - x 5) (x 6 - x 0) (endIIR x) ≠ 0 := by
      refine ne_of_sum (show det3 (x 4 - x 5) (x 6 - x 0) (endIIR x) =
          det3 (x 4 - x 0) (x 6 - x 0) (endIIR x) + det3 (x 0 - x 5) (x 6 - x 5) (endIIR x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWR 0 2 (by decide) (by decide)) (hWR 4 2 (by decide) (by decide)) (Or.inl ?_)
      exact det3_ne_zero_of_one_normal hN4_40 hN4_60 hN4_R.ne hne_0462
    have hne_omit5_R : det3 (x 2 - x 4) (x 6 - x 0) (endIIR x) ≠ 0 := by
      rw [← neg_ne_zero]
      refine ne_of_sum (show -det3 (x 2 - x 4) (x 6 - x 0) (endIIR x) =
          det3 (x 4 - x 0) (x 6 - x 0) (endIIR x) + det3 (x 2 - x 6) (x 0 - x 6) (endIIR x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWR 0 2 (by decide) (by decide)) (hWR 2 0 (by decide) (by decide)) (Or.inl ?_)
      exact det3_ne_zero_of_one_normal hN4_40 hN4_60 hN4_R.ne hne_0462
    have hne_omit6_R : det3 (x 4 - x 5) (x 0 - x 2) (endIIR x) ≠ 0 := by
      rw [← neg_ne_zero]
      refine ne_of_sum (show -det3 (x 4 - x 5) (x 0 - x 2) (endIIR x) =
          det3 (x 4 - x 0) (x 2 - x 0) (endIIR x) + det3 (x 5 - x 2) (x 0 - x 2) (endIIR x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWR 0 3 (by decide) (by decide)) (hWR 3 0 (by decide) (by decide)) ?_
      by_cases hR_if : RightM27 x
      · left
        have hM27_eq : endIIR x = viewM27 x := by simp only [endIIR, hR_if, ↓reduceIte]
        rw [hM27_eq]
        have hdet : det3 (x 4 - x 0) (x 2 - x 0) (viewM27 x) =
            ((1 + omega3 x) * (oblX0 x 4 + oblX2 x 4 - 1 - omega5 x * oblX6 x 4)) * det24 x := by
          rw [h40, h20]; dsimp [viewM27, capView]; rw [M4.det3_frame]
          have halg : (oblX0 x 4 - 1) * (1 * (1 + omega3 x) - 0 * (omega3 x * omega5 x - 1)) -
              oblX2 x 4 * ((-1) * (1 + omega3 x) - 0 * (1 + omega5 x)) +
              oblX6 x 4 * ((-1) * (omega3 x * omega5 x - 1) - 1 * (1 + omega5 x)) =
              (1 + omega3 x) * (oblX0 x 4 + oblX2 x 4 - 1 - omega5 x * oblX6 x 4) := by ring
          rw [halg]
        have hlt4 : oblX0 x 4 + oblX2 x 4 - 1 - omega5 x * oblX6 x 4 < 0 := by
          linarith [T.lt025 (v := 4) (by decide)]
        rw [hdet]
        exact mul_ne_zero (mul_ne_zero (by linarith) hlt4.ne) hd_ne
      · right
        exact det3_ne_zero_of_one_normal hN2_52 hN2_02 (hN2_R_ne hR_if) hne_5206
    have hne_omit4_R : det3 (x 6 - x 5) (x 2 - x 0) (endIIR x) ≠ 0 := by
      by_cases hR_if : RightM27 x
      · have hM27_eq : endIIR x = viewM27 x := by simp only [endIIR, hR_if, ↓reduceIte]
        rw [hM27_eq]
        have h65 : x 6 - x 5 = (-oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
            (1 - oblX6 x 5) • (x 6 - x 1) := by
          rw [show x 6 - x 5 = (x 6 - x 1) - (x 5 - x 1) by abel, rep_sub F 5]; module
        have hdet : det3 (x 6 - x 5) (x 2 - x 0) (viewM27 x) =
            -((1 + omega3 x) * (1 + omega5 x)) * det24 x := by
          rw [h65, h20]; dsimp [viewM27, capView]; rw [M4.det3_frame]
          have e5 := M4.eq5 F
          have halg : (-oblX0 x 5) * (1 * (1 + omega3 x) - 0 * (omega3 x * omega5 x - 1)) -
              (-oblX2 x 5) * ((-1) * (1 + omega3 x) - 0 * (1 + omega5 x)) +
              (1 - oblX6 x 5) * ((-1) * (omega3 x * omega5 x - 1) - 1 * (1 + omega5 x)) =
              -((1 + omega3 x) * (1 + omega5 x)) := by
            linear_combination -(1 + omega3 x) * e5
          rw [halg]
        rw [hdet]
        exact mul_ne_zero (neg_ne_zero.mpr (mul_pos (by linarith) (by linarith)).ne') hd_ne
      · refine ne_of_sum (show det3 (x 6 - x 5) (x 2 - x 0) (endIIR x) =
            det3 (x 2 - x 6) (x 0 - x 6) (endIIR x) + det3 (x 5 - x 2) (x 0 - x 2) (endIIR x) by
            simp only [det3_expand, PiLp.sub_apply]; ring)
          (hWR 2 0 (by decide) (by decide)) (hWR 3 0 (by decide) (by decide)) (Or.inr ?_)
        exact det3_ne_zero_of_one_normal hN2_52 hN2_02 (hN2_R_ne hR_if) hne_5206
    have hne_omit0_R : det3 (x 6 - x 5) (x 2 - x 4) (endIIR x) ≠ 0 := by
      refine ne_of_sum (show det3 (x 6 - x 5) (x 2 - x 4) (endIIR x) =
          det3 (x 6 - x 4) (x 2 - x 4) (endIIR x) + det3 (x 5 - x 2) (x 4 - x 2) (endIIR x) by
          simp only [det3_expand, PiLp.sub_apply]; ring)
        (hWR 1 3 (by decide) (by decide)) (hWR 3 1 (by decide) (by decide)) ?_
      by_cases hR_if : RightM27 x
      · right
        have hN2_M27 : ⟪F.N 2, viewM27 x⟫ = 0 := by
          dsimp [viewM27]; rw [inner_capView_2]
          rw [show (1 + omega5 x) + (omega3 x * omega5 x - 1) - omega5 x * (1 + omega3 x) = 0 by ring, mul_zero]
        have hN7_M27 : ⟪F.N 7, viewM27 x⟫ = 0 := by
          dsimp [viewM27]; rw [inner_capView_7]
          rw [show -omega3 x * (1 + omega5 x) + (omega3 x * omega5 x - 1) + (1 + omega3 x) = 0 by ring, mul_zero]
        have hM27_eq : endIIR x = viewM27 x := by simp only [endIIR, hR_if, ↓reduceIte]
        rw [hM27_eq]
        exact det3_ne_zero_of_two_normals hN2_M27 hN2_52 hN2_42.ne hN7_M27
          (by rw [F.inner_sub, F.zero 7 2 (by decide), sub_zero]; exact (F.neg 7 5 (by decide)).ne)
          (by rw [show det3 (x 5 - x 2) (x 4 - x 2) (x 0 - x 2) = -det3 (x 5 - x 2) (x 0 - x 2) (x 4 - x 2) by
              simp only [det3_expand, PiLp.sub_apply]; ring]
              have h := hdet_same_ρ hN2_52 hN2_02 hN2_42 hN2_62 hne_5206 hvol_5206
              intro h0; have h0' : det3 (x 5 - x 2) (x 0 - x 2) (x 4 - x 2) = 0 := by linarith
              rw [h0', mul_zero] at h; exact lt_irrefl 0 h)
          (by rw [← hM27_eq]; exact hR_ne)
      · left
        have h36_eq : endIIR x = x 3 - x 6 := by simp only [endIIR, hR_if, ↓reduceIte]
        rw [h36_eq]
        rw [show det3 (x 6 - x 4) (x 2 - x 4) (x 3 - x 6) = -det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) by
          simp only [det3_expand, PiLp.sub_apply]; ring, neg_ne_zero]
        have h26 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
          rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel]; module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by abel, rep_sub F 3]; module
        have h06 : x 0 - x 6 = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
          rw [show x 0 - x 6 = (x 0 - x 1) - (x 6 - x 1) by abel]; module
        have hdet2306 : det3 (x 2 - x 6) (x 3 - x 6) (x 0 - x 6) = ((1 + omega3 x) * oblX0 x 3) * det24 x := by
          rw [h26, h36, h06, M4.det3_frame]
          have e3 := M4.eq3 F
          have halg : 0 * (oblX2 x 3 * (-1) - (oblX6 x 3 - 1) * 0) -
              1 * (oblX0 x 3 * (-1) - (oblX6 x 3 - 1) * 1) +
              (-1) * (oblX0 x 3 * 0 - oblX2 x 3 * 1) = (1 + omega3 x) * oblX0 x 3 := by
            linear_combination e3
          rw [halg]
        have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
        exact det3_ne_zero_of_one_normal
          (by rw [F.inner_sub, F.zero 7 2 (by decide), F.zero 7 6 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self])
          (by rw [F.inner_sub, F.zero 7 6 (by decide), sub_zero]; exact (F.neg 7 4 (by decide)).ne)
          (by rw [hdet2306]; exact mul_ne_zero (mul_pos (by linarith) ha3).ne' hd_ne)
    exact apex_of_weak (endIIR x) hWR hne_omit2_R hne_omit6_R hne_omit4_R hne_omit5_R hne_omit0_R
  have hapex_M : ApexPat (fun i => x (cII i)) (midII x) (apexA x) (apexE x) := by
    have hadd : ∀ {y c a b : ℝ³}, DiagFront y c a b (endIIL x) → DiagFront y c a b (endIIR x) →
        DiagFront y c a b (midII x) := by
      intro y c a b h1 h2
      unfold DiagFront at *
      have hdet : det3 (c - y) (b - a) (midII x) =
          det3 (c - y) (b - a) (endIIL x) + det3 (c - y) (b - a) (endIIR x) := by
        dsimp [midII]; simp only [det3_expand, PiLp.add_apply]; ring
      rw [hdet, mul_add]; exact add_pos h1 h2
    rcases hapex_L with ⟨hε, l1, l2, l3, l4, l5⟩
    rcases hapex_R with ⟨_, r1, r2, r3, r4, r5⟩
    exact ⟨hε, hadd l1 r1, hadd l2 r2, hadd l3 r3, hadd l4 r4, hadd l5 r5⟩
  exact ⟨ρ, hSM, hWL, hWR, hapex_L, hapex_M, hapex_R⟩

/-! ## (i) assembled (proved from the region lemmas) -/

theorem regionII (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) :
    CellLe F UII DnII (endIIL x) ∧ CellLe F UII DnII (endIIR x) ∧ ∃ a, CellAt F UII DnII a := by
  obtain ⟨h1, h2, h3⟩ := regionII_mid F hC hD
  exact ⟨regionII_left F hC hD, regionII_right F hC hD, cellAt_of_mid F h1 h2 h3⟩

/-! ## (ii) The leaf: one strict apex row at an end

Elementary convexity along a segment (proved). -/

private theorem inner_seg (v e m : ℝ³) (t : ℝ) :
    ⟪v, e + t • (m - e)⟫ = (1 - t) * ⟪v, e⟫ + t * ⟪v, m⟫ := by
  simp only [inner_add_right, inner_smul_right, inner_sub_right]; ring

private theorem det3_seg (a b e m : ℝ³) (t : ℝ) :
    det3 a b (e + t • (m - e)) = (1 - t) * det3 a b e + t * det3 a b m := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring

private theorem pos_seg {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < (1 - t) * A + t * B := by
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hA.le, mul_pos ht0 hB]

private theorem diagFront_seg {y c a b e m : ℝ³} {t : ℝ} (he : DiagFront y c a b e) (hm : DiagFront y c a b m)
    (ht0 : 0 < t) (ht1 : t ≤ 1) : DiagFront y c a b (e + t • (m - e)) := by
  unfold DiagFront at *
  rw [det3_seg]
  have := pos_seg he hm ht0 ht1
  linarith [this, show det3 (c - y) (b - a) (y - a) * ((1 - t) * det3 (c - y) (b - a) e + t * det3 (c - y) (b - a) m)
    = (1 - t) * (det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) e) +
      t * (det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) m) by ring]

private theorem apexPat_seg {R : ZMod 5 → ℝ³} {a ε : ZMod 5} {e m : ℝ³} {t : ℝ}
    (he : ApexPat R e a ε) (hm : ApexPat R m a ε) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ApexPat R (e + t • (m - e)) a ε := by
  obtain ⟨hε, e1, e2, e3, e4, e5⟩ := he
  obtain ⟨_, m1, m2, m3, m4, m5⟩ := hm
  exact ⟨hε, diagFront_seg e1 m1 ht0 ht1, diagFront_seg e2 m2 ht0 ht1, diagFront_seg e3 m3 ht0 ht1,
    diagFront_seg e4 m4 ht0 ht1, diagFront_seg e5 m5 ht0 ht1⟩

private theorem exists_t {re rm : ℝ} (hre : re < 0) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (1 - t) * re + t * rm < 0 := by
  by_cases h : rm < 0
  · exact ⟨1, one_pos, le_rfl, by simpa using h⟩
  · push Not at h
    have hd : 0 < rm - re := by linarith
    refine ⟨-re / (2 * (rm - re)), ?_, ?_, ?_⟩
    · exact div_pos (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · have : (1 - -re / (2 * (rm - re))) * re + -re / (2 * (rm - re)) * rm =
          re + (-re / (2 * (rm - re))) * (rm - re) := by ring
      rw [this]
      have h2 : (-re / (2 * (rm - re))) * (rm - re) = -re / 2 := by field_simp
      rw [h2]; linarith

/-- The segment lemma: at a closed-cell end `e` where the rim is weakly convex, has the apex labelling and the
strict row `z r1 < z r2`, and at a closed-cell point `m` where it is strictly convex with the same apex labelling,
there is a closure point of the cell with the strict A5 hypotheses, so `Gen.LexAny`. -/
theorem lexAny_of_segment {F : S0xFac 9 s0x_S24 x} {U Dn : Finset (Fin 9)} {c : ZMod 5 → Fin 7}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn) {a : ℝ³} (ha : CellAt F U Dn a) {e m : ℝ³}
    (he : CellLe F U Dn e) (hm : CellLe F U Dn m) {ρ : ℝ}
    (hwe : WeakConvex5 (fun i => x (c i)) e ρ) (hsm : StrictConvex5 (fun i => x (c i)) m ρ)
    {a₀ ε : ZMod 5} (hpe : ApexPat (fun i => x (c i)) e a₀ ε) (hpm : ApexPat (fun i => x (c i)) m a₀ ε)
    (hlt : ⟪x (c a₀), e⟫ < ⟪x (c (a₀ + ε)), e⟫) : Gen.LexAny F := by
  obtain ⟨t, ht0, ht1, hrow⟩ := exists_t (re := ⟪x (c a₀), e⟫ - ⟪x (c (a₀ + ε)), e⟫)
    (rm := ⟪x (c a₀), m⟫ - ⟪x (c (a₀ + ε)), m⟫) (by linarith)
  have hu : CellLe F U Dn (e + t • (m - e)) := by
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [inner_seg]
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) (he.1 s hs), mul_nonneg ht0.le (hm.1 s hs)]
    · rw [inner_seg]
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 (he.2 s hs)),
        mul_nonneg ht0.le (neg_nonneg.2 (hm.2 s hs))]
  have hcvx : StrictConvex5 (fun i => x (c i)) (e + t • (m - e)) ρ := by
    intro i j hji hji1
    rw [det3_seg]
    have h1 := hwe i j hji hji1
    have h2 := hsm i j hji hji1
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) h1, mul_pos ht0 h2]
  have hlt' : ⟪x (c a₀), e + t • (m - e)⟫ < ⟪x (c (a₀ + ε)), e + t • (m - e)⟫ := by
    rw [inner_seg, inner_seg]; nlinarith [hrow]
  exact lexAny_of_a5_row F hc hcyc ha hu hcvx (apexPat_seg hpe hpm ht0 ht1) hlt'

open Minimality.GenRev Minimality.LexCell in
/-- **ES(ii'), RobUni at a closed-cell end** (the companion leaf, class B of the gate).  If the rim depths at a
closed-cell point `u₀` of the piece-II cell are robustly unimodal (weak form, ties allowed), then `Gen.LexAny F`.
No convexity or apex hypothesis is used (same closed-cell route as `lexAny_of_a5_row`; the A5 row is a way to
get `RobUni` at a nearby point where the end itself is not unimodal). -/
theorem lexAny_of_robUni_end {F : S0xFac 9 s0x_S24 x} {a u₀ : ℝ³} (ha : CellAt F UII DnII a)
    (hu : CellLe F UII DnII u₀) (hR : RobUni (fun i : ZMod 5 => ⟪x (cII i), u₀⟫)) : Gen.LexAny F := by
  refine ⟨5, inferInstance, cII, UII, DnII, u₀, a - u₀, 0, by decide, injII, cycII, ?_, ?_, ?_⟩
  · intro t ht
    rcases (hu.1 t ht).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, Or.inl ?_⟩
      rw [inner_sub_right, ← h]; simpa using ha.1 t ht
  · intro t ht
    rcases (hu.2 t ht).lt_or_eq with h | h
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [h]; simp, Or.inl ?_⟩
      rw [inner_sub_right, h]; have := ha.2 t ht; simp; linarith
  · intro B b c' d' h1 h2 h3 h4
    have hnot := hR B b c' d' h1 h2 h3 h4
    rcases not_and_or.mp hnot with h | h
    · exact Or.inl (Or.inl (sub_pos.mpr (not_le.mp h)))
    · rcases not_and_or.mp h with h | h
      · exact Or.inr (Or.inl (Or.inl (sub_pos.mpr (not_le.mp h))))
      · rcases not_and_or.mp h with h | h
        · exact Or.inr (Or.inr (Or.inl (Or.inl (sub_pos.mpr (not_le.mp h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_pos.mpr (not_le.mp h)))))

/-! ## (ii) The leaf -/

/-- **ES(ii), piece II leaf.**  If the A5 apex row is strictly negative at an end of piece II
(`<x upper, u> < <x 0, u>`, `upper = 5` if the bracket `[2 4 5 6]` is positive, else `4`) then `Gen.LexAny F`. -/
theorem lexAny_pieceII (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) (hb : brk24 x ≠ 0)
    (hrow : ⟪x (apexV x), endIIL x⟫ < ⟪x 0, endIIL x⟫ ∨ ⟪x (apexV x), endIIR x⟫ < ⟪x 0, endIIR x⟫) :
    Gen.LexAny F := by
  obtain ⟨hL, hR, a, ha⟩ := regionII F hC hD
  obtain ⟨hm1, hm2, hm3⟩ := regionII_mid F hC hD
  have hM : CellLe F UII DnII (midII x) := by
    refine ⟨fun t ht => ?_, fun t ht => (hm3 t ht).le⟩
    by_cases h7 : t = 7
    · subst h7; exact hm2
    · exact (hm1 t ht h7).le
  obtain ⟨ρ, hsm, hwL, hwR, apL, apM, apR⟩ := regionII_apex F hC hD hb
  have e1 := cII_apexA x
  have e2 := cII_apexA_add x
  rcases hrow with h | h
  · refine lexAny_of_segment injII cycII ha hL hM hwL hsm apL apM ?_
    rw [e1, e2]; exact h
  · refine lexAny_of_segment injII cycII ha hR hM hwR hsm apR apM ?_
    rw [e1, e2]; exact h

/-- **ES(ii), piece II leaf, Rupert form.** -/
theorem isRupert_pieceII (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) (hb : brk24 x ≠ 0)
    (hrow : ⟪x (apexV x), endIIL x⟫ < ⟪x 0, endIIL x⟫ ∨ ⟪x (apexV x), endIIR x⟫ < ⟪x 0, endIIR x⟫) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (Minimality.H24.SAT.inj_of_fac F) (lexAny_pieceII F hC hD hb hrow)

end Minimality.T24.ES
