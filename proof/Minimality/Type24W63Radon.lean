module

public import Minimality.Type24A2Chain

@[expose] public section

/-!
# Type 24: the single view `w63 = x 3 - x 6` on `{c3 > 1, mu* > 0}` (`SEED63`)

Formalizes the SEED63 region theorem in `Minimality.T24.A20`:
1. `radon02346`, `radon02346_sum`, `radon02346_depth`: the affine Radon dependency of
   `x 0, x 2, x 3, x 4, x 6` with weights `mu0, mu2, mu3, mu4, mu6`.
2. `radon02346_signs`: under `CbarIn x`, the weights have fixed signs `+ - + - +`,
   separating `{0, 3, 6}` from `{2, 4}`.
3. `w63_facings_gt`: under `CbarIn x`, `1 < oblX6 x 3`, and `0 < mustar x`, the facet
   normals at `w63 = x 3 - x 6` have `Up = {2, 3, 6}`, `Dn = {0, 1, 4, 5}`, and `7, 8` on-line.
4. `w63_closes_mustar_pos`: `LexAny F` holds on `{CbarIn x, 1 < c3, 0 < mustar}` under the
   genericity hypothesis `hgen` that the five `w63`-depths `⟪x v, x 3 - x 6⟫` for
   `v ∈ {0, 2, 3, 4, 6}` are pairwise distinct. (Note: `hgen` is needed for a proof using
   `b = w63` + lex tilt `d1` alone; e.g. at `x0=(2,2,0), x1=(1.1,0.3,-0.5), x2=(1,0,0),
   x3=(0,0,1), x4=(0,1,0), x5=(0.1,0.05,1), x6=(0,0,-1)` all facets, `CbarIn`, `c3 > 1`, and
   `mu* > 0` hold, yet `z6 < z0 = z2 = z4 < z3` at `w63` and no lex tilt at `w63` closes any
   of the four rim cycles.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10
  Minimality.T24.A8 Minimality.T24.Q24 Minimality.T24 Minimality.T24.A15

/-- Facing parameter for facet `025` at `w63 = x 3 - x 6`. -/
noncomputable def mustar (x : Fin 7 → ℝ³) : ℝ :=
  (omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3)

/-- Radon weight of `x 3`: `a4 + b4 + c4 - 1` (`= b4 (1 + om4)`). -/
noncomputable def mu3 (x : Fin 7 → ℝ³) : ℝ := oblX0 x 4 + oblX2 x 4 + oblX6 x 4 - 1

/-- Radon weight of `x 4`: `1 - (a3 + b3 + c3)` (`= -a3 (1 + om3)`). -/
noncomputable def mu4 (x : Fin 7 → ℝ³) : ℝ := 1 - (oblX0 x 3 + oblX2 x 3 + oblX6 x 3)

noncomputable def mu0 (x : Fin 7 → ℝ³) : ℝ := -(mu3 x * oblX0 x 3 + mu4 x * oblX0 x 4)
noncomputable def mu2 (x : Fin 7 → ℝ³) : ℝ := -(mu3 x * oblX2 x 3 + mu4 x * oblX2 x 4)
noncomputable def mu6 (x : Fin 7 → ℝ³) : ℝ := -(mu3 x * oblX6 x 3 + mu4 x * oblX6 x 4)

/-- **Radon identity** of `x 0, x 2, x 3, x 4, x 6` (linear form, base point `x 1`). -/
theorem radon02346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    mu0 x • (x 0 - x 1) + mu2 x • (x 2 - x 1) + mu3 x • (x 3 - x 1) + mu4 x • (x 4 - x 1) +
      mu6 x • (x 6 - x 1) = 0 := by
  have T := type24OfFac F
  have h3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
  have h4 : x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by rw [T.rep 4]; abel
  rw [h3, h4]
  dsimp only [mu0, mu2, mu6]
  module

/-- The weights sum to zero, so `radon02346` is an affine dependency. -/
theorem radon02346_sum (x : Fin 7 → ℝ³) : mu0 x + mu2 x + mu3 x + mu4 x + mu6 x = 0 := by
  simp only [mu0, mu2, mu6, mu3, mu4]; ring

theorem radon02346_depth {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) :
    mu0 x * ⟪x 0, u⟫ + mu2 x * ⟪x 2, u⟫ + mu3 x * ⟪x 3, u⟫ + mu4 x * ⟪x 4, u⟫ +
      mu6 x * ⟪x 6, u⟫ = 0 := by
  have h := congrArg (fun v => ⟪v, u⟫) (radon02346 F)
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left, inner_zero_left] at h
  linear_combination h + ⟪x 1, u⟫ * radon02346_sum x

/-- `0 < 1 + omega3 x` from `F : S0xFac 9 s0x_S24 x` alone (via facet `3 = {0, 3, 4, 5}` at `x 3`). -/
theorem one_add_omega3_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < 1 + omega3 x := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have h31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have ev3_3 := fac_eval F 3 3
  rw [F.zero 3 0 (by decide), F.zero 3 3 (by decide)] at ev3_3
  have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp [ha3.ne']
  have hid : oblX0 x 3 * (1 + omega3 x) * F.f 3 (x 1) =
      oblX2 x 3 * F.f 3 (x 2) + oblX6 x 3 * F.f 3 (x 6) := by
    linear_combination ev3_3 + F.f 3 (x 1) * hom3_eq
  have hneg : oblX0 x 3 * (1 + omega3 x) * F.f 3 (x 1) < 0 := by rw [hid]; nlinarith
  have hpos : 0 < oblX0 x 3 * (1 + omega3 x) := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn h31.le]
  exact (mul_pos_iff_of_pos_left ha3).mp hpos

/-- `0 < 1 + omega4 x` from `F : S0xFac 9 s0x_S24 x` alone (via facet `3 = {0, 3, 4, 5}` at `x 4`). -/
theorem one_add_omega4_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < 1 + omega4 x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have h31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have ev3_4 := fac_eval F 3 4
  rw [F.zero 3 0 (by decide), F.zero 3 4 (by decide)] at ev3_4
  have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
    simp only [omega4]; field_simp [hb4.ne']
  have hid : oblX2 x 4 * (1 + omega4 x) * F.f 3 (x 1) =
      oblX2 x 4 * F.f 3 (x 2) + oblX6 x 4 * F.f 3 (x 6) := by
    linear_combination ev3_4 + F.f 3 (x 1) * hom4_eq
  have hneg : oblX2 x 4 * (1 + omega4 x) * F.f 3 (x 1) < 0 := by rw [hid]; nlinarith
  have hpos : 0 < oblX2 x 4 * (1 + omega4 x) := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn h31.le]
  exact (mul_pos_iff_of_pos_left hb4).mp hpos

/-- `0 < 1 + omega5 x` from `F : S0xFac 9 s0x_S24 x` alone (via facet `3 = {0, 3, 4, 5}` at `x 5`). -/
theorem one_add_omega5_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < 1 + omega5 x := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have h31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have ev3_5 := fac_eval F 3 5
  rw [F.zero 3 0 (by decide), F.zero 3 5 (by decide)] at ev3_5
  have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
    simp only [omega5]; field_simp [hc5.ne']
  have hid : oblX6 x 5 * (1 + omega5 x) * F.f 3 (x 1) =
      oblX2 x 5 * F.f 3 (x 2) + oblX6 x 5 * F.f 3 (x 6) := by
    linear_combination ev3_5 + F.f 3 (x 1) * hom5_eq
  have hneg : oblX6 x 5 * (1 + omega5 x) * F.f 3 (x 1) < 0 := by rw [hid]; nlinarith
  have hpos : 0 < oblX6 x 5 * (1 + omega5 x) := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn h31.le]
  exact (mul_pos_iff_of_pos_left hc5).mp hpos

/-- **Radon signs** (region facts only, via facet pairing): `{0, 3, 6}` against `{2, 4}` (`+ - + - +`). -/
theorem radon02346_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < mu0 x ∧ mu2 x < 0 ∧ 0 < mu3 x ∧ mu4 x < 0 ∧ 0 < mu6 x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hmu3 : 0 < mu3 x := by
    have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
      simp only [omega4]; field_simp [hb4.ne']
    have hmu3_eq : mu3 x = oblX2 x 4 * (1 + omega4 x) := by dsimp only [mu3]; linarith
    rw [hmu3_eq]; exact mul_pos hb4 (one_add_omega4_pos F)
  have eval_rad : ∀ t : Fin 9,
      mu0 x * F.f t (x 0) + mu2 x * F.f t (x 2) + mu3 x * F.f t (x 3) +
        mu4 x * F.f t (x 4) + mu6 x * F.f t (x 6) = 0 := by
    intro t
    have h := congrArg (fun u => ⟪F.N t, u⟫) (radon02346 F)
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    rw [← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1), ← F.hN t (x 3) (x 1),
      ← F.hN t (x 4) (x 1), ← F.hN t (x 6) (x 1)] at h
    linear_combination h + F.f t (x 1) * radon02346_sum x
  have hmu2 : mu2 x < 0 := by
    have h4 := eval_rad 4
    rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide), F.zero 4 6 (by decide)] at h4
    have hf42 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
    have hf43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
    nlinarith
  have hmu0 : 0 < mu0 x := by
    have h8 := eval_rad 8
    rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide), F.zero 8 6 (by decide)] at h8
    have hf80 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
    have hf82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
    nlinarith
  have hmu4 : mu4 x < 0 := by
    have h7 := eval_rad 7
    rw [F.zero 7 2 (by decide), F.zero 7 3 (by decide), F.zero 7 6 (by decide)] at h7
    have hf70 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
    have hf74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
    nlinarith
  have hmu6 : 0 < mu6 x := by
    have h3 := eval_rad 3
    rw [F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 4 (by decide)] at h3
    have hf32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
    have hf36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    nlinarith
  exact ⟨hmu0, hmu2, hmu3, hmu4, hmu6⟩

/-- Facet signs at `w63` for `c3 > 1`, `mu* > 0`: `Up = {2, 3, 6}`, `Dn = {0, 1, 4, 5}`,
on-line `{7, 8}`. -/
theorem w63_facings_gt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x) :
    ⟪F.N 0, x 3 - x 6⟫ < 0 ∧ ⟪F.N 1, x 3 - x 6⟫ < 0 ∧ 0 < ⟪F.N 2, x 3 - x 6⟫ ∧
    0 < ⟪F.N 3, x 3 - x 6⟫ ∧ ⟪F.N 4, x 3 - x 6⟫ < 0 ∧ ⟪F.N 5, x 3 - x 6⟫ < 0 ∧
    0 < ⟪F.N 6, x 3 - x 6⟫ ∧ ⟪F.N 7, x 3 - x 6⟫ = 0 ∧ ⟪F.N 8, x 3 - x 6⟫ = 0 := by
  have T := type24OfFac F
  have hw : ∀ t : Fin 9, ⟪F.N t, x 3 - x 6⟫ = F.f t (x 3) - F.f t (x 6) :=
    fun t => (F.hN t (x 3) (x 6)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 0]
    have ev0 := fac_eval F 0 3
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev0
    have h06 : 0 < -F.f 0 (x 6) := by linarith [F.neg 0 6 (by decide)]
    have hc3_neg : 1 - oblX6 x 3 < 0 := sub_neg.mpr hc3
    have hd : F.f 0 (x 3) - F.f 0 (x 6) = (1 - oblX6 x 3) * (-F.f 0 (x 6)) := by
      rw [ev0]; ring
    rw [hd]; exact mul_neg_of_neg_of_pos hc3_neg h06
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
        (-F.f 2 (x 1)) * mustar x := by
      dsimp only [mustar]; rw [ev2_3, hb3]; ring
    rw [hf2_6, hd]
    exact mul_pos (neg_pos.mpr (F.neg 2 1 (by decide))) hmu
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

end Minimality.T24.A20
