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

/-! ### Finite rim lemma on `{0, 2, 3, 4, 6}` -/

private def cyc4_ok4 (a b c d : Fin 5) : Bool :=
  !(Nat.blt a.1 b.1 && Nat.blt a.1 d.1 && Nat.blt c.1 b.1 && Nat.blt c.1 d.1) &&
  !(Nat.blt b.1 a.1 && Nat.blt b.1 c.1 && Nat.blt d.1 a.1 && Nat.blt d.1 c.1)

private def cyc4_ok5 (a b c d e : Fin 5) : Bool :=
  cyc4_ok4 a b c d && cyc4_ok4 a b c e && cyc4_ok4 a b d e && cyc4_ok4 a c d e && cyc4_ok4 b c d e

private theorem cyc4_finite :
    ∀ r0 r1 r2 r3 r4 : Fin 5,
      r0 ≠ r1 → r0 ≠ r2 → r0 ≠ r3 → r0 ≠ r4 →
      r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
      ¬ ((r0.1 < r1.1 ∧ r0.1 < r3.1 ∧ r2.1 < r1.1 ∧ r2.1 < r3.1 ∧ r4.1 < r1.1 ∧ r4.1 < r3.1) ∨
         (r1.1 < r0.1 ∧ r1.1 < r2.1 ∧ r1.1 < r4.1 ∧ r3.1 < r0.1 ∧ r3.1 < r2.1 ∧ r3.1 < r4.1)) →
      cyc4_ok4 r0 r1 r4 r3 = true ∨ cyc4_ok5 r0 r1 r4 r2 r3 = true ∨
      cyc4_ok5 r0 r1 r2 r4 r3 = true ∨ cyc4_ok4 r0 r1 r2 r3 = true := by
  decide

/-! ### Main theorem -/

private def v02346 : Fin 5 → Fin 7 := ![0, 2, 3, 4, 6]

private def c_pp : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
private def c_pm : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 4]
private def c_mp : ZMod 5 → Fin 7 := ![0, 2, 3, 6, 4]
private def c_mm : ZMod 4 → Fin 7 := ![0, 2, 3, 4]

private theorem c_pp_inj : Function.Injective c_pp := by decide
private theorem c_pm_inj : Function.Injective c_pm := by decide
private theorem c_mp_inj : Function.Injective c_mp := by decide
private theorem c_mm_inj : Function.Injective c_mm := by decide

private theorem cyc_pp : S0xCycUD s0x_S24 c_pp {2, 3, 6, 7, 8} {0, 1, 4, 5} := by decide
private theorem cyc_pm : S0xCycUD s0x_S24 c_pm {2, 3, 6, 7} {0, 1, 4, 5, 8} := by decide
private theorem cyc_mp : S0xCycUD s0x_S24 c_mp {2, 3, 6, 8} {0, 1, 4, 5, 7} := by decide
private theorem cyc_mm : S0xCycUD s0x_S24 c_mm {2, 3, 6} {0, 1, 4, 5, 7, 8} := by decide

private theorem lexClause_of_rank {x : Fin 7 → ℝ³} {w d1 : ℝ³} (r : Fin 5 → Fin 5)
    (hinj : ∀ i j : Fin 5, i ≠ j → r i ≠ r j)
    (hmono : ∀ i j : Fin 5, r i < r j → ⟪x (v02346 i), w⟫ < ⟪x (v02346 j), w⟫)
    {va vb vc vd : Fin 7} {a b c d : Fin 5}
    (hva : va = v02346 a) (hvb : vb = v02346 b) (hvc : vc = v02346 c) (hvd : vd = v02346 d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : !(Nat.blt (r a).1 (r c).1 && Nat.blt (r a).1 (r d).1 &&
      Nat.blt (r b).1 (r c).1 && Nat.blt (r b).1 (r d).1) = true) :
    Minimality.GenQuad.LexClause (x va) (x vb) (x vc) (x vd) w d1 0 := by
  subst hva hvb hvc hvd
  apply Minimality.GenQuad.lexClause_of_notM
  rintro ⟨hwac, hwad, hwbc, hwbd⟩
  have h'' : (((r c).1 ≤ (r a).1 ∨ (r d).1 ≤ (r a).1) ∨ (r c).1 ≤ (r b).1) ∨ (r d).1 ≤ (r b).1 := by
    simpa [Nat.blt_eq] using h
  rcases h'' with ((h1 | h2) | h3) | h4
  · have hlt := hmono c a (lt_of_le_of_ne h1 (hinj c a hac.symm))
    linarith
  · have hlt := hmono d a (lt_of_le_of_ne h2 (hinj d a had.symm))
    linarith
  · have hlt := hmono c b (lt_of_le_of_ne h3 (hinj c b hbc.symm))
    linarith
  · have hlt := hmono d b (lt_of_le_of_ne h4 (hinj d b hbd.symm))
    linarith

private theorem tilt_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s7 s8 : ℝ) (hs7 : s7 = 1 ∨ s7 = -1) (hs8 : s8 = 1 ∨ s8 = -1) :
    let d1 : ℝ³ := (-s7) • (x 4 - x 6) + (-s8) • (x 2 - x 6)
    0 < s7 * ⟪F.N 7, d1⟫ ∧ 0 < s8 * ⟪F.N 8, d1⟫ := by
  intro d1
  constructor
  · dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 7 (x 4) (x 6), ← F.hN 7 (x 2) (x 6), F.zero 7 6 (by decide), F.zero 7 2 (by decide),
      sub_zero, sub_self, mul_zero, add_zero]
    have hs7_sq : s7 * s7 = 1 := by rcases hs7 with rfl | rfl <;> norm_num
    have heq : s7 * (-s7 * F.f 7 (x 4)) = -(F.f 7 (x 4)) := by linear_combination -F.f 7 (x 4) * hs7_sq
    rw [heq]
    exact neg_pos.mpr (F.neg 7 4 (by decide))
  · dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 8 (x 4) (x 6), ← F.hN 8 (x 2) (x 6), F.zero 8 6 (by decide), F.zero 8 4 (by decide),
      sub_self, sub_zero, mul_zero, zero_add]
    have hs8_sq : s8 * s8 = 1 := by rcases hs8 with rfl | rfl <;> norm_num
    have heq : s8 * (-s8 * F.f 8 (x 2)) = -(F.f 8 (x 2)) := by linear_combination -F.f 8 (x 2) * hs8_sq
    rw [heq]
    exact neg_pos.mpr (F.neg 8 2 (by decide))

private theorem close_k4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 4 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_four (p := fun i => x (c i)) hA hB)

private theorem close_k5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 5 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA0123 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0123 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0)
    (hA0124 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0124 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0134 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0134 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0234 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA1234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1234 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_five (p := fun i => x (c i))
      hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234)

/-- **SEED63 region theorem**: on `{CbarIn x, 1 < c3, 0 < mustar}` (with distinct `w63`-depths
on `{0, 2, 3, 4, 6}`), the single view `w63 = x 3 - x 6` gives `LexAny F`. -/
theorem w63_closes_mustar_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x)
    (hgen : ∀ i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)), i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Minimality.Gen.LexAny F := by
  classical
  have hfac := w63_facings_gt F hc3 hmu
  have hsgn := radon02346_signs F
  let w : ℝ³ := x 3 - x 6
  obtain ⟨r, hinj, hmono⟩ : ∃ r : Fin 5 → Fin 5,
      (∀ i j : Fin 5, i ≠ j → r i ≠ r j) ∧
      (∀ i j : Fin 5, r i < r j → ⟪x (v02346 i), w⟫ < ⟪x (v02346 j), w⟫) := by
    let r0 : Fin 5 → Fin 5 := fun i =>
      ⟨(Finset.univ.filter fun j : Fin 5 => ⟪x (v02346 j), w⟫ < ⟪x (v02346 i), w⟫).card, by
        have hsub : (Finset.univ.filter fun j : Fin 5 => ⟪x (v02346 j), w⟫ < ⟪x (v02346 i), w⟫) ⊂
            Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
          have hi : i ∈ Finset.univ.filter (fun j : Fin 5 => ⟪x (v02346 j), w⟫ < ⟪x (v02346 i), w⟫) := by
            rw [h]; exact Finset.mem_univ _
          exact lt_irrefl _ (Finset.mem_filter.mp hi).2
        simpa using Finset.card_lt_card hsub⟩
    have hv_mem : ∀ i : Fin 5, v02346 i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)) := by
      intro i; fin_cases i <;> decide
    have hv_inj : Function.Injective v02346 := by decide
    have hmono_rev : ∀ i j : Fin 5, ⟪x (v02346 i), w⟫ < ⟪x (v02346 j), w⟫ → r0 i < r0 j := by
      intro i j hij
      change (Finset.univ.filter fun k : Fin 5 => ⟪x (v02346 k), w⟫ < ⟪x (v02346 i), w⟫).card <
        (Finset.univ.filter fun k : Fin 5 => ⟪x (v02346 k), w⟫ < ⟪x (v02346 j), w⟫).card
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun k hk => ?_, fun heq => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hk hij
      · have hi : i ∈ Finset.univ.filter (fun k : Fin 5 => ⟪x (v02346 k), w⟫ < ⟪x (v02346 j), w⟫) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
        rw [← heq] at hi
        exact lt_irrefl _ (Finset.mem_filter.mp hi).2
    have hinj : ∀ i j : Fin 5, i ≠ j → r0 i ≠ r0 j := by
      intro i j hij
      have hne : ⟪x (v02346 i), w⟫ ≠ ⟪x (v02346 j), w⟫ :=
        hgen (v02346 i) (hv_mem i) (v02346 j) (hv_mem j) (hv_inj.ne hij)
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hmono_rev i j h).ne
      · exact (hmono_rev j i h).ne'
    have hmono : ∀ i j : Fin 5, r0 i < r0 j → ⟪x (v02346 i), w⟫ < ⟪x (v02346 j), w⟫ := by
      intro i j hij
      have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have hwne : ⟪x (v02346 i), w⟫ ≠ ⟪x (v02346 j), w⟫ :=
        hgen (v02346 i) (hv_mem i) (v02346 j) (hv_mem j) (hv_inj.ne hne)
      rcases lt_or_gt_of_ne hwne with h | h
      · exact h
      · exact absurd (lt_trans hij (hmono_rev j i h)) (lt_irrefl _)
    exact ⟨r0, hinj, hmono⟩
  have hnotsep : ¬ (((r 0).1 < (r 1).1 ∧ (r 0).1 < (r 3).1 ∧ (r 2).1 < (r 1).1 ∧
        (r 2).1 < (r 3).1 ∧ (r 4).1 < (r 1).1 ∧ (r 4).1 < (r 3).1) ∨
      ((r 1).1 < (r 0).1 ∧ (r 1).1 < (r 2).1 ∧ (r 1).1 < (r 4).1 ∧
        (r 3).1 < (r 0).1 ∧ (r 3).1 < (r 2).1 ∧ (r 3).1 < (r 4).1)) := by
    have hrad := radon02346_depth F w
    rcases hsgn with ⟨hm0, hm2, hm3, hm4, hm6⟩
    rintro (⟨h01, h03, h21, h23, h41, h43⟩ | ⟨h10, h12, h14, h30, h32, h34⟩)
    · have h02 : ⟪x 0, w⟫ < ⟪x 2, w⟫ := hmono 0 1 h01
      have h04 : ⟪x 0, w⟫ < ⟪x 4, w⟫ := hmono 0 3 h03
      have h32 : ⟪x 3, w⟫ < ⟪x 2, w⟫ := hmono 2 1 h21
      have h34 : ⟪x 3, w⟫ < ⟪x 4, w⟫ := hmono 2 3 h23
      have h62 : ⟪x 6, w⟫ < ⟪x 2, w⟫ := hmono 4 1 h41
      have h64 : ⟪x 6, w⟫ < ⟪x 4, w⟫ := hmono 4 3 h43
      let M := max ⟪x 0, w⟫ (max ⟪x 3, w⟫ ⟪x 6, w⟫)
      let m := min ⟪x 2, w⟫ ⟪x 4, w⟫
      have hMm : M < m := max_lt (lt_min h02 h04) (max_lt (lt_min h32 h34) (lt_min h62 h64))
      have hM0 : ⟪x 0, w⟫ ≤ M := le_max_left _ _
      have hM3 : ⟪x 3, w⟫ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      have hM6 : ⟪x 6, w⟫ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
      have hm2' : m ≤ ⟪x 2, w⟫ := min_le_left _ _
      have hm4' : m ≤ ⟪x 4, w⟫ := min_le_right _ _
      have hsum := radon02346_sum x
      have h1 : mu0 x * ⟪x 0, w⟫ + mu3 x * ⟪x 3, w⟫ + mu6 x * ⟪x 6, w⟫ ≤
          (mu0 x + mu3 x + mu6 x) * M := by nlinarith
      have h2 : (-mu2 x - mu4 x) * m ≤ (-mu2 x) * ⟪x 2, w⟫ + (-mu4 x) * ⟪x 4, w⟫ := by
        nlinarith
      have hM_pos : 0 < (mu0 x + mu3 x + mu6 x) * (m - M) :=
        mul_pos (by linarith) (sub_pos.mpr hMm)
      have hM_eq : (mu0 x + mu3 x + mu6 x) * (m - M) =
          (mu0 x + mu3 x + mu6 x) * m - (mu0 x + mu3 x + mu6 x) * M := by ring
      have hm_eq : (-mu2 x - mu4 x) * m = (mu0 x + mu3 x + mu6 x) * m := by
        linear_combination -m * hsum
      linarith
    · have h20 : ⟪x 2, w⟫ < ⟪x 0, w⟫ := hmono 1 0 h10
      have h40 : ⟪x 4, w⟫ < ⟪x 0, w⟫ := hmono 3 0 h30
      have h23 : ⟪x 2, w⟫ < ⟪x 3, w⟫ := hmono 1 2 h12
      have h43 : ⟪x 4, w⟫ < ⟪x 3, w⟫ := hmono 3 2 h32
      have h26 : ⟪x 2, w⟫ < ⟪x 6, w⟫ := hmono 1 4 h14
      have h46 : ⟪x 4, w⟫ < ⟪x 6, w⟫ := hmono 3 4 h34
      let M := max ⟪x 2, w⟫ ⟪x 4, w⟫
      let m := min ⟪x 0, w⟫ (min ⟪x 3, w⟫ ⟪x 6, w⟫)
      have hMm : M < m := max_lt (lt_min h20 (lt_min h23 h26)) (lt_min h40 (lt_min h43 h46))
      have hM2 : ⟪x 2, w⟫ ≤ M := le_max_left _ _
      have hM4 : ⟪x 4, w⟫ ≤ M := le_max_right _ _
      have hm0' : m ≤ ⟪x 0, w⟫ := min_le_left _ _
      have hm3' : m ≤ ⟪x 3, w⟫ := le_trans (min_le_right _ _) (min_le_left _ _)
      have hm6' : m ≤ ⟪x 6, w⟫ := le_trans (min_le_right _ _) (min_le_right _ _)
      have hsum := radon02346_sum x
      have h1 : (mu0 x + mu3 x + mu6 x) * m ≤
          mu0 x * ⟪x 0, w⟫ + mu3 x * ⟪x 3, w⟫ + mu6 x * ⟪x 6, w⟫ := by nlinarith
      have h2 : (-mu2 x) * ⟪x 2, w⟫ + (-mu4 x) * ⟪x 4, w⟫ ≤ (-mu2 x - mu4 x) * M := by
        nlinarith
      have hM_pos : 0 < (mu0 x + mu3 x + mu6 x) * (m - M) :=
        mul_pos (by linarith) (sub_pos.mpr hMm)
      have hM_eq : (mu0 x + mu3 x + mu6 x) * (m - M) =
          (mu0 x + mu3 x + mu6 x) * m - (mu0 x + mu3 x + mu6 x) * M := by ring
      have hm_eq : (-mu2 x - mu4 x) * M = (mu0 x + mu3 x + mu6 x) * M := by
        linear_combination -M * hsum
      linarith
  rcases cyc4_finite (r 0) (r 1) (r 2) (r 3) (r 4)
      (hinj 0 1 (by decide)) (hinj 0 2 (by decide)) (hinj 0 3 (by decide)) (hinj 0 4 (by decide))
      (hinj 1 2 (by decide)) (hinj 1 3 (by decide)) (hinj 1 4 (by decide))
      (hinj 2 3 (by decide)) (hinj 2 4 (by decide)) (hinj 3 4 (by decide)) hnotsep with
      hpp | hpm | hmp | hmm
  · obtain ⟨hd7, hd8⟩ := tilt_signs F 1 1 (Or.inl rfl) (Or.inl rfl)
    let d1 : ℝ³ := (-1 : ℝ) • (x 4 - x 6) + (-1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < ⟪F.N 7, d1⟫ := by simpa [d1] using hd7
    have hd8' : 0 < ⟪F.N 8, d1⟫ := by simpa [d1] using hd8
    have hU : ∀ t ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    have hD : ∀ t ∈ ({0, 1, 4, 5} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    simp only [cyc4_ok4, Bool.and_eq_true] at hpp
    exact close_k4 F c_pp_inj cyc_pp w d1 hU hD
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpp.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpp.1)
  · obtain ⟨hd7, hd8⟩ := tilt_signs F 1 (-1) (Or.inl rfl) (Or.inr rfl)
    let d1 : ℝ³ := (-1 : ℝ) • (x 4 - x 6) + (1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < ⟪F.N 7, d1⟫ := by simpa [d1] using hd7
    have hd8' : 0 < -⟪F.N 8, d1⟫ := by simpa [d1] using hd8
    have hU : ∀ t ∈ ({2, 3, 6, 7} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
    have hD : ∀ t ∈ ({0, 1, 4, 5, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    simp only [cyc4_ok5, cyc4_ok4, Bool.and_eq_true] at hpm
    exact close_k5 F c_pm_inj cyc_pm w d1 hU hD
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.1.1.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.1.1.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpm.2.1)
  · obtain ⟨hd7, hd8⟩ := tilt_signs F (-1) 1 (Or.inr rfl) (Or.inl rfl)
    let d1 : ℝ³ := (1 : ℝ) • (x 4 - x 6) + (-1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < -⟪F.N 7, d1⟫ := by simpa [d1] using hd7
    have hd8' : 0 < ⟪F.N 8, d1⟫ := by simpa [d1] using hd8
    have hU : ∀ t ∈ ({2, 3, 6, 8} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    have hD : ∀ t ∈ ({0, 1, 4, 5, 7} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
    simp only [cyc4_ok5, cyc4_ok4, Bool.and_eq_true] at hmp
    exact close_k5 F c_mp_inj cyc_mp w d1 hU hD
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.1.1.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.1.1.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.1.2.1)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.2.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmp.2.1)
  · obtain ⟨hd7, hd8⟩ := tilt_signs F (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    let d1 : ℝ³ := (1 : ℝ) • (x 4 - x 6) + (1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < -⟪F.N 7, d1⟫ := by simpa [d1] using hd7
    have hd8' : 0 < -⟪F.N 8, d1⟫ := by simpa [d1] using hd8
    have hU : ∀ t ∈ ({2, 3, 6} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
    have hD : ∀ t ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    simp only [cyc4_ok4, Bool.and_eq_true] at hmm
    exact close_k4 F c_mm_inj cyc_mm w d1 hU hD
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmm.2)
      (lexClause_of_rank r hinj hmono (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hmm.1)

end Minimality.T24.A20
