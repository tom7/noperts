module

public import Minimality.Type24W63Radon
public import Minimality.M4Sym24
public import Minimality.Type24Z0
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

/-!
# Type 24: `E23` mirror, `mustar`/`mu23` coupling, and the `0345` facet cell (`A36`)

Formalizes the A36 referee specs in `Minimality.T24.A20`:
1. `mu23`, `mustar_comp_pi24`, `e23_closes_mu23_pos`: `pi24` transport of `w63_closes_mustar_pos`
   to `E23 = x 3 - x 2` on `{1 < oblX2 x 3, 0 < mu23 x}` with non-tie genericity on `{0,2,3,5,6}`.
2. `mustar_mu23_coupling`, `mustar_eq`, `mu23_eq`, `delta_pos_of_mustar_nonpos`.
3. `facetCell_0345`, `mustar_or_mu23_nonneg`, `mustar_or_mu23_pos`: on `¬ FacetCell24 fs` with
   `be ≤ 1` and `al ≤ 1` (from `par2546_quad`), either `0 ≤ mustar x` or `0 ≤ mu23 x` (strict for
   `be < 1` and `al < 1` under `CbarIn x`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.T24.Sym Minimality.T24.M4 Minimality.T24.A15 Minimality.T24.Z0
  Minimality.T24.Par Minimality.T24 Minimality.LexCell

/-! ### 1. `E23` mirror (`pi24` transport of `w63_closes_mustar_pos`) -/

/-- Mirror of `mustar` under `pi24 = (2 6)(4 5)`: `(omega3 + 1) a3 + (omega4 + 1) (1 - b3)`. -/
noncomputable def mu23 (x : Fin 7 → ℝ³) : ℝ :=
  (omega3 x + 1) * oblX0 x 3 + (omega4 x + 1) * (1 - oblX2 x 3)

theorem mustar_comp_pi24 (x : Fin 7 → ℝ³) : mustar (x ∘ pi24) = mu23 x := by
  simp only [mustar, mu23, omega3_comp_pi24, omega5_comp_pi24, oblX0_comp_pi24,
    oblX6_comp_pi24, pi24_3]

/-- **E23 single-view theorem** (`pi24` mirror of `w63_closes_mustar_pos`): on
`{CbarIn x, 1 < b3, 0 < mu23}` with distinct `E23`-depths on `{0, 2, 3, 5, 6}`,
`E23 = x 3 - x 2` gives `Minimality.Gen.LexAny F`. -/
theorem e23_closes_mu23_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x)
    (hgen : ∀ i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫) :
    Minimality.Gen.LexAny F := by
  have hc3' : 1 < oblX6 (x ∘ pi24) 3 := by simpa [oblX6_comp_pi24, pi24_3] using hb3
  have hmu' : 0 < mustar (x ∘ pi24) := by rwa [mustar_comp_pi24]
  have hgen' : ∀ i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      i ≠ j → ⟪(x ∘ pi24) i, (x ∘ pi24) 3 - (x ∘ pi24) 6⟫ ≠
        ⟪(x ∘ pi24) j, (x ∘ pi24) 3 - (x ∘ pi24) 6⟫ := by
    intro i hi j hj hij
    have hi' : pi24 i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)) := by
      fin_cases i <;> simp at hi ⊢
    have hj' : pi24 j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)) := by
      fin_cases j <;> simp at hj ⊢
    have hij' : pi24 i ≠ pi24 j := fun heq => by
      have hinv : (pi24 (pi24 i)) = (pi24 (pi24 j)) := congrArg pi24 heq
      have hpi : ∀ a : Fin 7, pi24 (pi24 a) = a := by decide
      rw [hpi i, hpi j] at hinv
      exact hij hinv
    have h1 := hgen (pi24 i) hi' (pi24 j) hj' hij'
    dsimp only [Function.comp_apply]
    rw [pi24_3, pi24_6]
    exact h1
  exact lexAny_sym F (w63_closes_mustar_pos (sym24 F) hc3' hmu' hgen')

/-! ### 2. Coupling & algebraic identities -/

/-- Coupling identity: `(om4 + 1) mu* + (om5 + 1) mu23 = (om4 + 1)(om5 + 1) - a3 Delta24`. -/
theorem mustar_mu23_coupling {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (omega4 x + 1) * mustar x + (omega5 x + 1) * mu23 x =
      (omega4 x + 1) * (omega5 x + 1) - oblX0 x 3 * Delta24 x := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp [ha3.ne']
  dsimp only [mustar, mu23, Delta24]
  linear_combination (omega4 x + 1) * (omega5 x + 1) * hom3_eq

private theorem oblX_of_affine {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {al be : ℝ}
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)) :
    oblX0 x 3 = (1 - al - be) + al * oblX0 x 5 + be * oblX0 x 4 ∧
    oblX2 x 3 = al * oblX2 x 5 + be * oblX2 x 4 ∧
    oblX6 x 3 = al * oblX6 x 5 + be * oblX6 x 4 := by
  have hrep3 : x 3 - x 1 = (1 - al - be) • (x 0 - x 1) + al • (x 5 - x 1) + be • (x 4 - x 1) := by
    have e3 : x 3 - x 1 = (x 3 - x 0) + (x 0 - x 1) := by abel
    have e5 : x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) := by abel
    have e4 : x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) := by abel
    rw [e3, hq, e5, e4]; module
  have eval_fac : ∀ t : Fin 9, F.f t (x 3) =
      (1 - al - be) * F.f t (x 0) + al * F.f t (x 5) + be * F.f t (x 4) := by
    intro t
    have h1 := congrArg (fun w => ⟪F.N t, w⟫) hrep3
    simp only [inner_add_right, real_inner_smul_right, ← F.hN] at h1
    linarith
  have h0 : oblX0 x 3 = (1 - al - be) + al * oblX0 x 5 + be * oblX0 x 4 := by
    have e5_3 := fac_eval F 5 3
    have e5_4 := fac_eval F 5 4
    have e5_5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at e5_3 e5_4 e5_5
    have h5 := eval_fac 5
    have h51 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
    have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    have hid : F.f 5 (x 0) * (oblX0 x 3 - ((1 - al - be) + al * oblX0 x 5 + be * oblX0 x 4)) = 0 := by
      linear_combination -e5_3 + al * e5_5 + be * e5_4 + h5 - h51 * 0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h50.ne)
  have h2 : oblX2 x 3 = al * oblX2 x 5 + be * oblX2 x 4 := by
    have e1_3 := fac_eval F 1 3
    have e1_4 := fac_eval F 1 4
    have e1_5 := fac_eval F 1 5
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at e1_3 e1_4 e1_5
    have h1 := eval_fac 1
    rw [F.zero 1 0 (by decide), mul_zero, zero_add] at h1
    have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
    have hid : F.f 1 (x 2) * (oblX2 x 3 - (al * oblX2 x 5 + be * oblX2 x 4)) = 0 := by
      linear_combination -e1_3 + al * e1_5 + be * e1_4 + h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h12.ne)
  have h6 : oblX6 x 3 = al * oblX6 x 5 + be * oblX6 x 4 := by
    have e0_3 := fac_eval F 0 3
    have e0_4 := fac_eval F 0 4
    have e0_5 := fac_eval F 0 5
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at e0_3 e0_4 e0_5
    have h0' := eval_fac 0
    rw [F.zero 0 0 (by decide), mul_zero, zero_add] at h0'
    have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
    have hid : F.f 0 (x 6) * (oblX6 x 3 - (al * oblX6 x 5 + be * oblX6 x 4)) = 0 := by
      linear_combination -e0_3 + al * e0_5 + be * e0_4 + h0'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h06.ne)
  exact ⟨h0, h2, h6⟩

/-- `mustar` in terms of `be` (`s` from `par2546_quad`): `mustar = (1 + om5) + be * <nu025, x4 - x6>`. -/
theorem mustar_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {al be : ℝ}
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)) :
    mustar x = (1 + omega5 x) + be * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp [ha3.ne']
  have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
    simp only [omega5]; field_simp [hc5.ne']
  obtain ⟨h0, h2, h6⟩ := oblX_of_affine F hq
  dsimp only [mustar]
  linear_combination hom3_eq - al * hom5_eq + h0 + h2 - omega5 x * h6

/-- `mu23` in terms of `al` (`t` from `par2546_quad`): `mu23 = (1 + om4) + al * <nu046, x5 - x2>`. -/
theorem mu23_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {al be : ℝ}
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)) :
    mu23 x = (1 + omega4 x) + al * (oblX0 x 5 - omega4 x * oblX2 x 5 + oblX6 x 5 - 1) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp [ha3.ne']
  have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
    simp only [omega4]; field_simp [hb4.ne']
  obtain ⟨h0, h2, h6⟩ := oblX_of_affine F hq
  dsimp only [mu23]
  linear_combination hom3_eq - be * hom4_eq + h0 - omega4 x * h2 + h6

/-- With `mustar ≤ 0`, `0 < Delta24 x` (from `F` alone). -/
theorem delta_pos_of_mustar_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hmu : mustar x ≤ 0) : 0 < Delta24 x := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp [ha3.ne']
  have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
    simp only [omega4]; field_simp [hb4.ne']
  have hf4_2 : F.f 4 (x 2) = (1 + omega4 x) * F.f 4 (x 1) := by
    have ev4_4 := fac_eval F 4 4
    rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide), F.zero 4 6 (by decide)] at ev4_4
    have h_id : oblX2 x 4 * (F.f 4 (x 2) - (1 + omega4 x) * F.f 4 (x 1)) = 0 := by
      linear_combination -ev4_4 - F.f 4 (x 1) * hom4_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h_id).resolve_left hb4.ne')
  have ev4_3 := fac_eval F 4 3
  rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide), hf4_2] at ev4_3
  have hh3_pos : 0 < 1 - oblX0 x 3 - oblX6 x 3 + oblX2 x 3 * omega4 x := by
    have h41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have h43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
    have hid : F.f 4 (x 3) = F.f 4 (x 1) * (1 - oblX0 x 3 - oblX6 x 3 + oblX2 x 3 * omega4 x) := by
      rw [ev4_3]; ring
    rw [hid] at h43
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h41.le hn]
  have hid : oblX0 x 3 * Delta24 x =
      (1 - oblX0 x 3 - oblX6 x 3 + oblX2 x 3 * omega4 x) * (omega5 x + 1) -
        mustar x * (omega4 x + 1) := by
    dsimp only [Delta24, mustar]
    linear_combination omega4 x * (omega5 x + 1) * hom3_eq
  have hom4 : 0 < omega4 x + 1 := by linarith [one_add_omega4_pos F]
  have hom5 : 0 < omega5 x + 1 := by linarith [one_add_omega5_pos F]
  have hprod : 0 < oblX0 x 3 * Delta24 x := by
    rw [hid]
    have h1 : 0 < (1 - oblX0 x 3 - oblX6 x 3 + oblX2 x 3 * omega4 x) * (omega5 x + 1) :=
      mul_pos hh3_pos hom5
    have h2 : 0 ≤ -mustar x * (omega4 x + 1) := mul_nonneg (neg_nonneg.mpr hmu) hom4.le
    linarith
  exact (mul_pos_iff_of_pos_left ha3).mp hprod

/-! ### 3. `0345` facet cell and `mustar_or_mu23_nonneg` -/

private noncomputable def u0546 (x : Fin 7 → ℝ³) : ℝ³ :=
  (omega4 x * omega5 x - 1) • (x 0 - x 1) +
    (omega5 x + 1) • (x 2 - x 1) + (omega4 x + 1) • (x 6 - x 1)

private theorem u0546_fac3_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 3, u0546 x⟫ := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
    simp only [omega4]; field_simp [hb4.ne']
  have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
    simp only [omega5]; field_simp [hc5.ne']
  have hlin3 : ⟪F.N 3, u0546 x⟫ =
      (omega4 x * omega5 x - 1) * (F.f 3 (x 0) - F.f 3 (x 1)) +
      (omega5 x + 1) * (F.f 3 (x 2) - F.f 3 (x 1)) +
      (omega4 x + 1) * (F.f 3 (x 6) - F.f 3 (x 1)) := by
    dsimp only [u0546]
    simp only [inner_add_right, real_inner_smul_right, ← F.hN]
  have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
    have ev2_5 := fac_eval F 2 5
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
    have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
      linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
  have hf4_2 : F.f 4 (x 2) = (1 + omega4 x) * F.f 4 (x 1) := by
    have ev4_4 := fac_eval F 4 4
    rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide), F.zero 4 6 (by decide)] at ev4_4
    have h4_id : oblX2 x 4 * (F.f 4 (x 2) - (1 + omega4 x) * F.f 4 (x 1)) = 0 := by
      linear_combination -ev4_4 - F.f 4 (x 1) * hom4_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4_id).resolve_left hb4.ne')
  have h31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have ev3_4 := fac_eval F 3 4
  have ev3_5 := fac_eval F 3 5
  rw [F.zero 3 0 (by decide), F.zero 3 4 (by decide)] at ev3_4
  rw [F.zero 3 0 (by decide), F.zero 3 5 (by decide)] at ev3_5
  have e3_4 : oblX2 x 4 * (F.f 3 (x 2) - F.f 3 (x 1)) +
      oblX6 x 4 * (F.f 3 (x 6) - F.f 3 (x 1)) =
      (oblX0 x 4 - 1) * F.f 3 (x 1) := by linarith
  have e3_5 : oblX2 x 5 * (F.f 3 (x 2) - F.f 3 (x 1)) +
      oblX6 x 5 * (F.f 3 (x 6) - F.f 3 (x 1)) =
      (oblX0 x 5 - 1) * F.f 3 (x 1) := by linarith
  have hb4om : 0 < oblX2 x 4 * (omega4 x + 1) := by
    have hid : oblX2 x 4 * (omega4 x + 1) * F.f 3 (x 1) =
        oblX2 x 4 * F.f 3 (x 2) + oblX6 x 4 * F.f 3 (x 6) := by
      linear_combination -e3_4 + F.f 3 (x 1) * hom4_eq
    have hneg : oblX2 x 4 * (omega4 x + 1) * F.f 3 (x 1) < 0 := by
      rw [hid]; nlinarith
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn h31.le]
  have hc5om : 0 < oblX6 x 5 * (omega5 x + 1) := by
    have hid : oblX6 x 5 * (omega5 x + 1) * F.f 3 (x 1) =
        oblX2 x 5 * F.f 3 (x 2) + oblX6 x 5 * F.f 3 (x 6) := by
      linear_combination -e3_5 + F.f 3 (x 1) * hom5_eq
    have hneg : oblX6 x 5 * (omega5 x + 1) * F.f 3 (x 1) < 0 := by
      rw [hid]; nlinarith
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn h31.le]
  have h4_025 : 0 < oblX6 x 4 * (omega5 x + 1) - oblX2 x 4 * (omega4 x + 1) := by
    have ev2_4 := fac_eval F 2 4
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_4
    have h21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have h24 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have hid : F.f 2 (x 4) =
        F.f 2 (x 1) * (oblX6 x 4 * (omega5 x + 1) - oblX2 x 4 * (omega4 x + 1)) := by
      linear_combination ev2_4 + F.f 2 (x 1) * hom4_eq
    rw [hid] at h24
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h21.le hn]
  have h5_046 : 0 < oblX2 x 5 * (omega4 x + 1) - oblX6 x 5 * (omega5 x + 1) := by
    have ev4_5 := fac_eval F 4 5
    rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide), hf4_2] at ev4_5
    have h41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have h45 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
    have hid : F.f 4 (x 5) =
        F.f 4 (x 1) * (oblX2 x 5 * (omega4 x + 1) - oblX6 x 5 * (omega5 x + 1)) := by
      linear_combination ev4_5 + F.f 4 (x 1) * hom5_eq
    rw [hid] at h45
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h41.le hn]
  have hdet : oblX2 x 4 * oblX6 x 5 - oblX2 x 5 * oblX6 x 4 < 0 := by
    have hlt1 : oblX2 x 4 * (omega4 x + 1) < oblX6 x 4 * (omega5 x + 1) := sub_pos.mp h4_025
    have hlt2 : oblX6 x 5 * (omega5 x + 1) < oblX2 x 5 * (omega4 x + 1) := sub_pos.mp h5_046
    have hmul : (oblX2 x 4 * (omega4 x + 1)) * (oblX6 x 5 * (omega5 x + 1)) <
        (oblX6 x 4 * (omega5 x + 1)) * (oblX2 x 5 * (omega4 x + 1)) :=
      mul_lt_mul'' hlt1 hlt2 hb4om.le hc5om.le
    have hom_pos : 0 < (omega4 x + 1) * (omega5 x + 1) := by
      have hc4om : 0 < oblX6 x 4 * (omega5 x + 1) := lt_trans hb4om hlt1
      have hp1 : 0 < omega4 x + 1 := (mul_pos_iff_of_pos_left hb4).mp hb4om
      have hp2 : 0 < omega5 x + 1 := (mul_pos_iff_of_pos_left hc4).mp hc4om
      exact mul_pos hp1 hp2
    have hmul' : (oblX2 x 4 * oblX6 x 5 - oblX2 x 5 * oblX6 x 4) *
        ((omega4 x + 1) * (omega5 x + 1)) < 0 := by
      have heq : (oblX2 x 4 * oblX6 x 5 - oblX2 x 5 * oblX6 x 4) *
          ((omega4 x + 1) * (omega5 x + 1)) =
          (oblX2 x 4 * (omega4 x + 1)) * (oblX6 x 5 * (omega5 x + 1)) -
          (oblX6 x 4 * (omega5 x + 1)) * (oblX2 x 5 * (omega4 x + 1)) := by ring
      rw [heq]; exact sub_neg.mpr hmul
    by_contra hn; push Not at hn
    exact absurd hmul' (not_lt.mpr (mul_nonneg hn hom_pos.le))
  have hid3 : (oblX2 x 4 * oblX6 x 5 - oblX2 x 5 * oblX6 x 4) * ⟪F.N 3, u0546 x⟫ =
      F.f 3 (x 1) *
        (oblX6 x 4 * (omega5 x + 1) - oblX2 x 4 * (omega4 x + 1)) *
        (oblX2 x 5 * (omega4 x + 1) - oblX6 x 5 * (omega5 x + 1)) := by
    rw [hlin3, F.zero 3 0 (by decide)]
    clear h32 h36 hb4om hc5om h4_025 h5_046 hdet
    linear_combination (oblX6 x 5 * (omega5 x + 1) - oblX2 x 5 * (omega4 x + 1)) * e3_4 +
      (oblX2 x 4 * (omega4 x + 1) - oblX6 x 4 * (omega5 x + 1)) * e3_5 +
      (-(oblX6 x 5 * (omega5 x + 1) - oblX2 x 5 * (omega4 x + 1)) * F.f 3 (x 1)) * hom4_eq +
      (-(oblX2 x 4 * (omega4 x + 1) - oblX6 x 4 * (omega5 x + 1)) * F.f 3 (x 1)) * hom5_eq
  have hprod_neg : (oblX2 x 4 * oblX6 x 5 - oblX2 x 5 * oblX6 x 4) * ⟪F.N 3, u0546 x⟫ < 0 := by
    rw [hid3]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h31 h4_025) h5_046
  by_contra hn; push Not at hn
  exact absurd hprod_neg (not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos hdet.le hn))

private theorem facetCell_0345_fac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (k4 : oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4) < 0)
    (k5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0) :
    ∃ u : ℝ³, 0 < ⟪F.N 3, u⟫ ∧ ∀ s ∈ nb (3 : Fin 9), ⟪F.N s, u⟫ < 0 := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
    simp only [omega4]; field_simp [hb4.ne']
  have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
    simp only [omega5]; field_simp [hc5.ne']
  let u0 : ℝ³ := u0546 x
  have hlin_u0 : ∀ s : Fin 9, ⟪F.N s, u0⟫ =
      (omega4 x * omega5 x - 1) * (F.f s (x 0) - F.f s (x 1)) +
      (omega5 x + 1) * (F.f s (x 2) - F.f s (x 1)) +
      (omega4 x + 1) * (F.f s (x 6) - F.f s (x 1)) := by
    intro s
    dsimp only [u0, u0546]
    simp only [inner_add_right, real_inner_smul_right, ← F.hN]
  have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
    have ev2_5 := fac_eval F 2 5
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
    have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
      linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
  have hf4_2 : F.f 4 (x 2) = (1 + omega4 x) * F.f 4 (x 1) := by
    have ev4_4 := fac_eval F 4 4
    rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide), F.zero 4 6 (by decide)] at ev4_4
    have h4_id : oblX2 x 4 * (F.f 4 (x 2) - (1 + omega4 x) * F.f 4 (x 1)) = 0 := by
      linear_combination -ev4_4 - F.f 4 (x 1) * hom4_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4_id).resolve_left hb4.ne')
  have hu0_2 : ⟪F.N 2, u0⟫ = 0 := by
    rw [hlin_u0 2, F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6]; ring
  have hu0_4 : ⟪F.N 4, u0⟫ = 0 := by
    rw [hlin_u0 4, F.zero 4 0 (by decide), F.zero 4 6 (by decide), hf4_2]; ring
  have hu0_8 : ⟪F.N 8, u0⟫ < 0 := by
    have ev8_4 := fac_eval F 8 4
    rw [F.zero 8 4 (by decide), F.zero 8 6 (by decide)] at ev8_4
    have h80 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
    have hid : oblX2 x 4 * ⟪F.N 8, u0⟫ =
        -(oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4)) * F.f 8 (x 0) := by
      rw [hlin_u0 8, F.zero 8 6 (by decide)]
      linear_combination -(omega5 x + 1) * ev8_4 +
        (omega5 x * (F.f 8 (x 0) - F.f 8 (x 1)) - F.f 8 (x 1)) * hom4_eq
    have hprod : oblX2 x 4 * ⟪F.N 8, u0⟫ < 0 := by
      rw [hid]
      exact mul_neg_of_pos_of_neg (neg_pos.mpr k4) h80
    by_contra hn; push Not at hn
    exact absurd hprod (not_lt.mpr (mul_nonneg hb4.le hn))
  have hu0_6 : ⟪F.N 6, u0⟫ < 0 := by
    have ev6_5 := fac_eval F 6 5
    rw [F.zero 6 2 (by decide), F.zero 6 5 (by decide)] at ev6_5
    have h60 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
    have hid : oblX6 x 5 * ⟪F.N 6, u0⟫ =
        -(oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) * F.f 6 (x 0) := by
      rw [hlin_u0 6, F.zero 6 2 (by decide)]
      linear_combination -(omega4 x + 1) * ev6_5 +
        (omega4 x * (F.f 6 (x 0) - F.f 6 (x 1)) - F.f 6 (x 1)) * hom5_eq
    have hprod : oblX6 x 5 * ⟪F.N 6, u0⟫ < 0 := by
      rw [hid]
      exact mul_neg_of_pos_of_neg (neg_pos.mpr k5) h60
    by_contra hn; push Not at hn
    exact absurd hprod (not_lt.mpr (mul_nonneg hc5.le hn))
  have hu0_3 : 0 < ⟪F.N 3, u0⟫ := u0546_fac3_pos F
  have h21 : ⟪F.N 2, -(x 0 - x 1)⟫ < 0 := by
    rw [inner_neg_right, ← F.hN 2 (x 0) (x 1), F.zero 2 0 (by decide), zero_sub, neg_neg]
    exact F.neg 2 1 (by decide)
  have h41 : ⟪F.N 4, -(x 0 - x 1)⟫ < 0 := by
    rw [inner_neg_right, ← F.hN 4 (x 0) (x 1), F.zero 4 0 (by decide), zero_sub, neg_neg]
    exact F.neg 4 1 (by decide)
  have hε : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < ⟪F.N 3, u0 + ε • (-(x 0 - x 1))⟫ ∧
      ⟪F.N 2, u0 + ε • (-(x 0 - x 1))⟫ < 0 ∧
      ⟪F.N 4, u0 + ε • (-(x 0 - x 1))⟫ < 0 ∧
      ⟪F.N 6, u0 + ε • (-(x 0 - x 1))⟫ < 0 ∧
      ⟪F.N 8, u0 + ε • (-(x 0 - x 1))⟫ < 0 := by
    filter_upwards [
      eventually_pos_affine (A := ⟪F.N 3, u0⟫) (B := ⟪F.N 3, -(x 0 - x 1)⟫) (Or.inl hu0_3),
      eventually_pos_affine (A := -⟪F.N 2, u0⟫) (B := -⟪F.N 2, -(x 0 - x 1)⟫)
        (Or.inr ⟨neg_eq_zero.mpr hu0_2, neg_pos.mpr h21⟩),
      eventually_pos_affine (A := -⟪F.N 4, u0⟫) (B := -⟪F.N 4, -(x 0 - x 1)⟫)
        (Or.inr ⟨neg_eq_zero.mpr hu0_4, neg_pos.mpr h41⟩),
      eventually_pos_affine (A := -⟪F.N 6, u0⟫) (B := -⟪F.N 6, -(x 0 - x 1)⟫)
        (Or.inl (neg_pos.mpr hu0_6)),
      eventually_pos_affine (A := -⟪F.N 8, u0⟫) (B := -⟪F.N 8, -(x 0 - x 1)⟫)
        (Or.inl (neg_pos.mpr hu0_8))] with ε h3 h2 h4 h6 h8
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [inner_add_right, real_inner_smul_right] using h3
    · have : 0 < -(⟪F.N 2, u0⟫ + ε * ⟪F.N 2, -(x 0 - x 1)⟫) := by linarith
      simpa [inner_add_right, real_inner_smul_right] using neg_pos.mp this
    · have : 0 < -(⟪F.N 4, u0⟫ + ε * ⟪F.N 4, -(x 0 - x 1)⟫) := by linarith
      simpa [inner_add_right, real_inner_smul_right] using neg_pos.mp this
    · have : 0 < -(⟪F.N 6, u0⟫ + ε * ⟪F.N 6, -(x 0 - x 1)⟫) := by linarith
      simpa [inner_add_right, real_inner_smul_right] using neg_pos.mp this
    · have : 0 < -(⟪F.N 8, u0⟫ + ε * ⟪F.N 8, -(x 0 - x 1)⟫) := by linarith
      simpa [inner_add_right, real_inner_smul_right] using neg_pos.mp this
  obtain ⟨ε, h3, h2, h4, h6, h8⟩ := hε.exists
  refine ⟨u0 + ε • (-(x 0 - x 1)), h3, fun s hs => ?_⟩
  fin_cases s <;> simp [nb] at hs
  · exact h2
  · exact h4
  · exact h6
  · exact h8

/-- **Facet cell at `0345`** (`t = 3`): if `k4 < 0` (`<nu025, x4 - x6> < 0`) and
`k5 < 0` (`<nu046, x5 - x2> < 0`), then `u0546 - ε e_a` realizes `FacetCell24 fs`.
Uses `S0xFac` / region facts only (`CbarIn` is not needed). -/
theorem facetCell_0345 {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (k4 : oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4) < 0)
    (k5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0) :
    FacetCell24 fs := by
  let F := mkFac24 fs h
  have hN : ∀ s v, (fs s).linear v = ⟪F.N s, v⟫ := by
    intro s v
    have h1 := F.hN s v 0
    have h2 : (fs s).linear v = fs s v - fs s 0 := by simpa using (fs s).linear_apply_vsub v 0
    rw [h2]; simpa [F, mkFac24] using h1
  obtain ⟨u, hu3, hus⟩ := facetCell_0345_fac F k4 k5
  refine ⟨3, u, ?_, fun s hs => ?_⟩
  · rw [hN]; exact hu3
  · rw [hN]; exact hus s hs

/-- On `¬ FacetCell24 fs` with `0 ≤ al, 0 ≤ be, be ≤ 1, al ≤ 1` (from `par2546_quad`),
`0 ≤ mustar x ∨ 0 ≤ mu23 x`. -/
theorem mustar_or_mu23_nonneg {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hz : ¬ FacetCell24 fs) {al be : ℝ}
    (halp : 0 ≤ al) (hbep : 0 ≤ be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be ≤ 1) (hal : al ≤ 1) :
    0 ≤ mustar x ∨ 0 ≤ mu23 x := by
  let F := mkFac24 fs h
  have hom4 := one_add_omega4_pos F
  have hom5 := one_add_omega5_pos F
  by_contra hnot
  push Not at hnot
  have hk4 : oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4) < 0 := by
    have hme := mustar_eq F hq
    have hid : be * (oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4)) =
        mustar x - (1 - be) * (1 + omega5 x) := by rw [hme]; ring
    have hneg : be * (oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4)) < 0 := by
      rw [hid]
      have : 0 ≤ (1 - be) * (1 + omega5 x) := mul_nonneg (sub_nonneg.mpr hbe) hom5.le
      linarith [hnot.1]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg hbep hn))
  have hk5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0 := by
    have hme := mu23_eq F hq
    have hid : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) =
        mu23 x - (1 - al) * (1 + omega4 x) := by rw [hme]; ring
    have hneg : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) < 0 := by
      rw [hid]
      have : 0 ≤ (1 - al) * (1 + omega4 x) := mul_nonneg (sub_nonneg.mpr hal) hom4.le
      linarith [hnot.2]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg halp hn))
  exact hz (facetCell_0345 fs h hk4 hk5)

/-- Strict version on `¬ FacetCell24 fs` with `0 ≤ al, 0 ≤ be, be < 1, al < 1`:
`0 < mustar x ∨ 0 < mu23 x`. -/
theorem mustar_or_mu23_pos {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hz : ¬ FacetCell24 fs) {al be : ℝ}
    (halp : 0 ≤ al) (hbep : 0 ≤ be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be < 1) (hal : al < 1) :
    0 < mustar x ∨ 0 < mu23 x := by
  let F := mkFac24 fs h
  have hom4 := one_add_omega4_pos F
  have hom5 := one_add_omega5_pos F
  by_contra hnot
  push Not at hnot
  have hk4 : oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4) < 0 := by
    have hme := mustar_eq F hq
    have hid : be * (oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4)) =
        mustar x - (1 - be) * (1 + omega5 x) := by rw [hme]; ring
    have hneg : be * (oblX0 x 4 + oblX2 x 4 + omega5 x * (1 - oblX6 x 4)) < 0 := by
      rw [hid]
      have : 0 < (1 - be) * (1 + omega5 x) := mul_pos (sub_pos.mpr hbe) hom5
      linarith [hnot.1]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg hbep hn))
  have hk5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0 := by
    have hme := mu23_eq F hq
    have hid : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) =
        mu23 x - (1 - al) * (1 + omega4 x) := by rw [hme]; ring
    have hneg : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) < 0 := by
      rw [hid]
      have : 0 < (1 - al) * (1 + omega4 x) := mul_pos (sub_pos.mpr hal) hom4
      linarith [hnot.2]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg halp hn))
  exact hz (facetCell_0345 fs h hk4 hk5)

/-! ### 4. The walls `mustar = 0` and `mu23 = 0` (`Task DI`) -/

/-- Facet signs at `w63 = x 3 - x 6` on the wall `{1 < oblX6 x 3, mustar x = 0}`:
`Up = {3, 6}`, `Dn = {0, 1, 4, 5}`, and on-line `{2, 7, 8}` (`025 = 0`, `236 = 0`, `346 = 0`). -/
theorem w63_facings_wall {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : mustar x = 0) :
    ⟪F.N 0, x 3 - x 6⟫ < 0 ∧ ⟪F.N 1, x 3 - x 6⟫ < 0 ∧ ⟪F.N 2, x 3 - x 6⟫ = 0 ∧
    0 < ⟪F.N 3, x 3 - x 6⟫ ∧ ⟪F.N 4, x 3 - x 6⟫ < 0 ∧ ⟪F.N 5, x 3 - x 6⟫ < 0 ∧
    0 < ⟪F.N 6, x 3 - x 6⟫ ∧ ⟪F.N 7, x 3 - x 6⟫ = 0 ∧ ⟪F.N 8, x 3 - x 6⟫ = 0 := by
  have T := type24OfFac F
  have hw : ∀ t : Fin 9, ⟪F.N t, x 3 - x 6⟫ = F.f t (x 3) - F.f t (x 6) :=
    fun t => (F.hN t (x 3) (x 6)).symm
  have ev_x : ∀ t : Fin 9, ∀ v : Fin 7, F.f t (x v) =
      (1 - oblX0 x v - oblX2 x v - oblX6 x v) * F.f t (x 1) +
        oblX0 x v * F.f t (x 0) + oblX2 x v * F.f t (x 2) + oblX6 x v * F.f t (x 6) := by
    intro t v
    have hrep : x v - x 1 =
        oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
      rw [T.rep v]; abel
    have h0 := congrArg (fun u => ⟪F.N t, u⟫) hrep
    simp only [inner_add_right, real_inner_smul_right] at h0
    rw [← F.hN t (x v) (x 1), ← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1),
      ← F.hN t (x 6) (x 1)] at h0
    linear_combination h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 0]
    have ev0 := ev_x 0 3
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
      have ev2_5 := ev_x 2 5
      rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
      have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
      have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
        simp only [omega5]; field_simp
      have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
        linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
    have ev2_3 := ev_x 2 3
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_3
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hom3_eq : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
      simp only [omega3]; field_simp [ha3.ne']
    have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [hom3_eq]
    have hd : F.f 2 (x 3) - (1 + omega5 x) * F.f 2 (x 1) =
        (-F.f 2 (x 1)) * mustar x := by
      dsimp only [mustar]; rw [ev2_3, hb3]; ring
    rw [hf2_6, hd, hmu, mul_zero]
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

/-- **Radon circuit `R_0345`**: `{0, 3}` and `{4, 5}` cannot be strictly separated by any
linear functional `⟪·, w⟫`. -/
theorem radon0345_depth {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³) :
    ¬ ((⟪x 0, w⟫ < ⟪x 4, w⟫ ∧ ⟪x 0, w⟫ < ⟪x 5, w⟫ ∧
        ⟪x 3, w⟫ < ⟪x 4, w⟫ ∧ ⟪x 3, w⟫ < ⟪x 5, w⟫) ∨
       (⟪x 4, w⟫ < ⟪x 0, w⟫ ∧ ⟪x 5, w⟫ < ⟪x 0, w⟫ ∧
        ⟪x 4, w⟫ < ⟪x 3, w⟫ ∧ ⟪x 5, w⟫ < ⟪x 3, w⟫)) := by
  rcases par2546_quad F with ⟨al, be, hal, hbe, hab, hq⟩
  have hid : (al + be - 1) * ⟪x 0, w⟫ + ⟪x 3, w⟫ = al * ⟪x 5, w⟫ + be * ⟪x 4, w⟫ := by
    have h := congrArg (fun v => ⟪v, w⟫) hq
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith
  have h1 : 0 < al + be - 1 := sub_pos.mpr hab
  rintro (⟨h04, h05, h34, h35⟩ | ⟨h40, h50, h43, h53⟩)
  · have hL : (al + be - 1) * ⟪x 0, w⟫ + ⟪x 3, w⟫ <
        (al + be - 1) * min ⟪x 4, w⟫ ⟪x 5, w⟫ + min ⟪x 4, w⟫ ⟪x 5, w⟫ := by
      have hm0 : ⟪x 0, w⟫ < min ⟪x 4, w⟫ ⟪x 5, w⟫ := lt_min h04 h05
      have hm3 : ⟪x 3, w⟫ < min ⟪x 4, w⟫ ⟪x 5, w⟫ := lt_min h34 h35
      nlinarith
    have hR : (al + be) * min ⟪x 4, w⟫ ⟪x 5, w⟫ ≤ al * ⟪x 5, w⟫ + be * ⟪x 4, w⟫ := by
      have hm4 : min ⟪x 4, w⟫ ⟪x 5, w⟫ ≤ ⟪x 4, w⟫ := min_le_left _ _
      have hm5 : min ⟪x 4, w⟫ ⟪x 5, w⟫ ≤ ⟪x 5, w⟫ := min_le_right _ _
      nlinarith
    linarith
  · have hL : (al + be) * max ⟪x 4, w⟫ ⟪x 5, w⟫ < (al + be - 1) * ⟪x 0, w⟫ + ⟪x 3, w⟫ := by
      have hm0 : max ⟪x 4, w⟫ ⟪x 5, w⟫ < ⟪x 0, w⟫ := max_lt h40 h50
      have hm3 : max ⟪x 4, w⟫ ⟪x 5, w⟫ < ⟪x 3, w⟫ := max_lt h43 h53
      nlinarith
    have hR : al * ⟪x 5, w⟫ + be * ⟪x 4, w⟫ ≤ (al + be) * max ⟪x 4, w⟫ ⟪x 5, w⟫ := by
      have hm4 : ⟪x 4, w⟫ ≤ max ⟪x 4, w⟫ ⟪x 5, w⟫ := le_max_left _ _
      have hm5 : ⟪x 5, w⟫ ≤ max ⟪x 4, w⟫ ⟪x 5, w⟫ := le_max_right _ _
      nlinarith
    linarith

noncomputable def d3_24 (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 3 + oblX2 x 3 + oblX6 x 3 - 1

noncomputable def d5_24 (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1

noncomputable def nu0 (x : Fin 7 → ℝ³) : ℝ :=
  d3_24 x * oblX0 x 5 - d5_24 x * oblX0 x 3

noncomputable def nu2 (x : Fin 7 → ℝ³) : ℝ :=
  d3_24 x * oblX2 x 5 - d5_24 x * oblX2 x 3

noncomputable def nu3 (x : Fin 7 → ℝ³) : ℝ := d5_24 x

noncomputable def nu5 (x : Fin 7 → ℝ³) : ℝ := -d3_24 x

noncomputable def nu6 (x : Fin 7 → ℝ³) : ℝ :=
  d3_24 x * oblX6 x 5 - d5_24 x * oblX6 x 3

/-- Affine Radon dependency of `{0, 2, 3, 5, 6}` relative to `x 1`. -/
theorem radon02356 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    nu0 x • (x 0 - x 1) + nu2 x • (x 2 - x 1) + nu3 x • (x 3 - x 1) +
      nu5 x • (x 5 - x 1) + nu6 x • (x 6 - x 1) = 0 := by
  have T := type24OfFac F
  have h3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
  have h5 : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  rw [h3, h5]
  dsimp only [nu0, nu2, nu3, nu5, nu6, d3_24, d5_24]
  module

theorem radon02356_sum (x : Fin 7 → ℝ³) :
    nu0 x + nu2 x + nu3 x + nu5 x + nu6 x = 0 := by
  dsimp only [nu0, nu2, nu3, nu5, nu6, d3_24, d5_24]
  ring

theorem radon02356_depth {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³) :
    nu0 x * ⟪x 0, w⟫ + nu2 x * ⟪x 2, w⟫ + nu3 x * ⟪x 3, w⟫ +
      nu5 x * ⟪x 5, w⟫ + nu6 x * ⟪x 6, w⟫ = 0 := by
  have h := congrArg (fun v => ⟪v, w⟫) (radon02356 F)
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left] at h
  linear_combination h + ⟪x 1, w⟫ * radon02356_sum x

/-- The Radon weights of `{0, 2, 3, 5, 6}` have signs `+ + + - -` from `F` alone. -/
theorem radon02356_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < nu0 x ∧ 0 < nu2 x ∧ 0 < nu3 x ∧ nu5 x < 0 ∧ nu6 x < 0 := by
  have T := type24OfFac F
  have hmu4 : mu4 x < 0 := (radon02346_signs F).2.2.2.1
  have hd3 : 0 < d3_24 x := by
    dsimp only [d3_24]; dsimp only [mu4] at hmu4; linarith
  have hnu5 : nu5 x < 0 := by dsimp only [nu5]; linarith
  have hd5 : 0 < d5_24 x := by
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have hom5 : 0 < 1 + omega5 x := one_add_omega5_pos F
    have hid : d5_24 x = oblX6 x 5 * (1 + omega5 x) := by
      dsimp only [d5_24, omega5]; field_simp [hc5.ne']; ring
    rw [hid]; exact mul_pos hc5 hom5
  have hnu3 : 0 < nu3 x := hd5
  have eval_rad : ∀ t : Fin 9,
      nu0 x * F.f t (x 0) + nu2 x * F.f t (x 2) + nu3 x * F.f t (x 3) +
        nu5 x * F.f t (x 5) + nu6 x * F.f t (x 6) = 0 := by
    intro t
    have h := congrArg (fun u => ⟪F.N t, u⟫) (radon02356 F)
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    rw [← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1), ← F.hN t (x 3) (x 1),
      ← F.hN t (x 5) (x 1), ← F.hN t (x 6) (x 1)] at h
    linear_combination h + F.f t (x 1) * radon02356_sum x
  have hnu6 : nu6 x < 0 := by
    have h2 := eval_rad 2
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at h2
    have hf23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
    have hf26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
    nlinarith
  have hnu0 : 0 < nu0 x := by
    have h7 := eval_rad 7
    rw [F.zero 7 2 (by decide), F.zero 7 3 (by decide), F.zero 7 6 (by decide)] at h7
    have hf70 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
    have hf75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    nlinarith
  have hnu2 : 0 < nu2 x := by
    have h3 := eval_rad 3
    rw [F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 5 (by decide)] at h3
    have hf32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
    have hf36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    nlinarith
  exact ⟨hnu0, hnu2, hnu3, hnu5, hnu6⟩

private theorem close_k4_w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
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

private theorem close_k5_w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
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

private theorem close_k6_w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 6 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA0123 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0123 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0)
    (hA0124 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0124 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0125 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0125 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0134 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0134 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0135 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0135 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0145 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0145 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0234 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA0235 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0235 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 5)) w d1 0)
    (hA0245 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0245 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 2)) (x (c 5)) w d1 0)
    (hA0345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0345 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0)
    (hA1234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1234 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA1235 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1235 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 5)) w d1 0)
    (hA1245 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 1)) (x (c 4)) w d1 0)
    (hB1245 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 2)) (x (c 5)) w d1 0)
    (hA1345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 1)) (x (c 4)) w d1 0)
    (hB1345 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0)
    (hA2345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 2)) (x (c 4)) w d1 0)
    (hB2345 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_six (p := fun i => x (c i))
      hA0123 hB0123 hA0124 hB0124 hA0125 hB0125 hA0134 hB0134 hA0135 hB0135
      hA0145 hB0145 hA0234 hB0234 hA0235 hB0235 hA0245 hB0245 hA0345 hB0345
      hA1234 hB1234 hA1235 hB1235 hA1245 hB1245 hA1345 hB1345 hA2345 hB2345)

/-- Universal tilt realizing `(+1, -1, -1)` on `(F.N 2, F.N 7, F.N 8)`. -/
private noncomputable def tilt_pmm {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (-F.f 2 (x 6)) • (x 4 - x 6) + (|F.f 2 (x 4) - F.f 2 (x 6)| + 1) • (x 2 - x 6)

/-- Universal tilt realizing `(+1, +1, -1)` on `(F.N 2, F.N 7, F.N 8)`. -/
private noncomputable def tilt_ppm {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (-F.f 2 (x 6)) • (-(x 4 - x 6)) + (|F.f 2 (x 4) - F.f 2 (x 6)| + 1) • (x 2 - x 6)

private theorem tilt_pmm_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 2, tilt_pmm F⟫ ∧ ⟪F.N 7, tilt_pmm F⟫ < 0 ∧ ⟪F.N 8, tilt_pmm F⟫ < 0 := by
  dsimp only [tilt_pmm]
  simp only [inner_add_right, real_inner_smul_right]
  rw [← F.hN 2 (x 4) (x 6), ← F.hN 2 (x 2) (x 6),
    ← F.hN 7 (x 4) (x 6), ← F.hN 7 (x 2) (x 6),
    ← F.hN 8 (x 4) (x 6), ← F.hN 8 (x 2) (x 6),
    F.zero 2 2 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide),
    F.zero 8 4 (by decide), F.zero 8 6 (by decide)]
  have hf26 : 0 < -F.f 2 (x 6) := neg_pos.mpr (F.neg 2 6 (by decide))
  have hf74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have hf82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
  have habs : 0 ≤ F.f 2 (x 4) - F.f 2 (x 6) + |F.f 2 (x 4) - F.f 2 (x 6)| := by
    linarith [neg_abs_le (F.f 2 (x 4) - F.f 2 (x 6))]
  refine ⟨?_, ?_, ?_⟩
  · have hid : (-F.f 2 (x 6)) * (F.f 2 (x 4) - F.f 2 (x 6)) +
        (|F.f 2 (x 4) - F.f 2 (x 6)| + 1) * (0 - F.f 2 (x 6)) =
        (-F.f 2 (x 6)) * (F.f 2 (x 4) - F.f 2 (x 6) + |F.f 2 (x 4) - F.f 2 (x 6)| + 1) := by ring
    rw [hid]
    exact mul_pos hf26 (by linarith)
  · simp only [sub_zero, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg hf26 hf74
  · simp only [sub_self, mul_zero, zero_add, sub_zero]
    exact mul_neg_of_pos_of_neg (by linarith [abs_nonneg (F.f 2 (x 4) - F.f 2 (x 6))]) hf82

private theorem tilt_ppm_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 2, tilt_ppm F⟫ ∧ 0 < ⟪F.N 7, tilt_ppm F⟫ ∧ ⟪F.N 8, tilt_ppm F⟫ < 0 := by
  dsimp only [tilt_ppm]
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right]
  rw [← F.hN 2 (x 4) (x 6), ← F.hN 2 (x 2) (x 6),
    ← F.hN 7 (x 4) (x 6), ← F.hN 7 (x 2) (x 6),
    ← F.hN 8 (x 4) (x 6), ← F.hN 8 (x 2) (x 6),
    F.zero 2 2 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide),
    F.zero 8 4 (by decide), F.zero 8 6 (by decide)]
  have hf26 : 0 < -F.f 2 (x 6) := neg_pos.mpr (F.neg 2 6 (by decide))
  have hf74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have hf82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
  have habs : 0 ≤ -(F.f 2 (x 4) - F.f 2 (x 6)) + |F.f 2 (x 4) - F.f 2 (x 6)| := by
    linarith [le_abs_self (F.f 2 (x 4) - F.f 2 (x 6))]
  refine ⟨?_, ?_, ?_⟩
  · have hid : (-F.f 2 (x 6)) * -(F.f 2 (x 4) - F.f 2 (x 6)) +
        (|F.f 2 (x 4) - F.f 2 (x 6)| + 1) * (0 - F.f 2 (x 6)) =
        (-F.f 2 (x 6)) * (-(F.f 2 (x 4) - F.f 2 (x 6)) + |F.f 2 (x 4) - F.f 2 (x 6)| + 1) := by ring
    rw [hid]
    exact mul_pos hf26 (by linarith)
  · simp only [sub_zero, mul_zero, add_zero]
    exact mul_pos hf26 (neg_pos.mpr hf74)
  · simp only [sub_self, neg_zero, mul_zero, zero_add, sub_zero]
    exact mul_neg_of_pos_of_neg (by linarith [abs_nonneg (F.f 2 (x 4) - F.f 2 (x 6))]) hf82

private def c_w0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
private def c_w02634 : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 4]
private def c_w04625 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
private def c_w046325 : ZMod 6 → Fin 7 := ![0, 4, 6, 3, 2, 5]

private theorem c_w0234_inj : Function.Injective c_w0234 := by decide
private theorem c_w02634_inj : Function.Injective c_w02634 := by decide
private theorem c_w04625_inj : Function.Injective c_w04625 := by decide
private theorem c_w046325_inj : Function.Injective c_w046325 := by decide

private theorem cyc_w0234 : S0xCycUD s0x_S24 c_w0234 {2, 3, 6} {0, 1, 4, 5, 7, 8} := by decide
private theorem cyc_w02634 : S0xCycUD s0x_S24 c_w02634 {2, 3, 6, 7} {0, 1, 4, 5, 8} := by decide
private theorem cyc_w04625 : S0xCycUD s0x_S24 c_w04625 {3, 6, 7, 8} {0, 1, 2, 4, 5} := by decide
private theorem cyc_w046325 : S0xCycUD s0x_S24 c_w046325 {3, 6, 8} {0, 1, 2, 4, 5, 7} := by decide

private def all6 (f : Fin 6 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5

private theorem forall_of_all6 {f : Fin 6 → Bool} (h : all6 f = true) (i : Fin 6) :
    f i = true := by
  fin_cases i <;> simp_all [all6]

private def quadOk (a b c d : Fin 6) : Bool :=
  (min a.val c.val < max b.val d.val) && (min b.val d.val < max a.val c.val)

private def cyc4Ok (a b c d : Fin 6) : Bool := quadOk a b c d

private def cyc5Ok (a b c d e : Fin 6) : Bool :=
  quadOk a b c d && quadOk a b c e && quadOk a b d e && quadOk a c d e && quadOk b c d e

private def cyc6Ok (a b c d e f : Fin 6) : Bool :=
  quadOk a b c d && quadOk a b c e && quadOk a b c f &&
  quadOk a b d e && quadOk a b d f && quadOk a b e f &&
  quadOk a c d e && quadOk a c d f && quadOk a c e f &&
  quadOk a d e f &&
  quadOk b c d e && quadOk b c d f && quadOk b c e f &&
  quadOk b d e f &&
  quadOk c d e f

private def sep23 (a1 a2 b1 b2 b3 : Fin 6) : Bool :=
  (a1.val < b1.val && a1.val < b2.val && a1.val < b3.val &&
   a2.val < b1.val && a2.val < b2.val && a2.val < b3.val) ||
  (b1.val < a1.val && b1.val < a2.val &&
   b2.val < a1.val && b2.val < a2.val &&
   b3.val < a1.val && b3.val < a2.val)

private def sep22 (a1 a2 b1 b2 : Fin 6) : Bool :=
  (a1.val < b1.val && a1.val < b2.val && a2.val < b1.val && a2.val < b2.val) ||
  (b1.val < a1.val && b1.val < a2.val && b2.val < a1.val && b2.val < a2.val)

private def wallOrderOk (r0 r1 r2 r3 r4 r5 : Fin 6) : Bool :=
  let inj : Bool :=
    r0 != r1 && r0 != r2 && r0 != r3 && r0 != r4 && r0 != r5 &&
    r1 != r2 && r1 != r3 && r1 != r4 && r1 != r5 &&
    r2 != r3 && r2 != r4 && r2 != r5 &&
    r3 != r4 && r3 != r5 &&
    r4 != r5
  let cond : Bool :=
    inj && (r5.val < r2.val) &&
    !(sep23 r1 r3 r0 r2 r5) &&
    !(sep22 r0 r2 r3 r4) &&
    !(sep23 r4 r5 r0 r1 r2)
  !cond || (cyc4Ok r0 r1 r2 r3 || cyc5Ok r0 r1 r5 r2 r3 ||
    cyc5Ok r0 r3 r5 r1 r4 || cyc6Ok r0 r3 r5 r2 r1 r4)

private def wallCheck1 (r0 r1 r2 r3 r4 : Fin 6) : Bool :=
  all6 fun r5 =>
    if r0 == r5 || r1 == r5 || r2 == r5 || r3 == r5 || r4 == r5 || !(r5.val < r2.val) then true
    else wallOrderOk r0 r1 r2 r3 r4 r5

private def wallCheck2 (r0 r1 r2 r3 : Fin 6) : Bool :=
  all6 fun r4 =>
    if r0 == r4 || r1 == r4 || r2 == r4 || r3 == r4 then true
    else wallCheck1 r0 r1 r2 r3 r4

private def wallCheck3 (r0 r1 r2 : Fin 6) : Bool :=
  all6 fun r3 =>
    if r0 == r3 || r1 == r3 || r2 == r3 then true
    else wallCheck2 r0 r1 r2 r3

private def wallCheck4 (r0 r1 : Fin 6) : Bool :=
  all6 fun r2 =>
    if r0 == r2 || r1 == r2 then true
    else wallCheck3 r0 r1 r2

private def wallCheck5 (r0 : Fin 6) : Bool :=
  all6 fun r1 =>
    if r0 == r1 then true
    else wallCheck4 r0 r1

private def wallCheckAll : Bool := all6 wallCheck5

private theorem wallCheckAll_eq_true : wallCheckAll = true := by decide

private theorem wallOrderOk_of_inj {r : Fin 6 → Fin 6}
    (hinj : ∀ i j : Fin 6, i ≠ j → r i ≠ r j) (h52 : (r 5).val < (r 2).val) :
    wallOrderOk (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) = true := by
  have h5 := forall_of_all6 wallCheckAll_eq_true (r 0)
  have h4 := forall_of_all6 h5 (r 1)
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [beq_iff_eq, hinj 0 1 (by decide)]))] at h4
  have h3 := forall_of_all6 h4 (r 2)
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [beq_iff_eq, hinj 0 2 (by decide), hinj 1 2 (by decide)]))] at h3
  have h2 := forall_of_all6 h3 (r 3)
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [beq_iff_eq, hinj 0 3 (by decide), hinj 1 3 (by decide),
    hinj 2 3 (by decide)]))] at h2
  have h1 := forall_of_all6 h2 (r 4)
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [beq_iff_eq, hinj 0 4 (by decide), hinj 1 4 (by decide),
    hinj 2 4 (by decide), hinj 3 4 (by decide)]))] at h1
  have h0 := forall_of_all6 h1 (r 5)
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [beq_iff_eq, hinj 0 5 (by decide), hinj 1 5 (by decide),
    hinj 2 5 (by decide), hinj 3 5 (by decide), hinj 4 5 (by decide), h52]))] at h0
  exact h0

private def v023456 : Fin 6 → Fin 7 := ![0, 2, 3, 4, 5, 6]

private theorem radon32_no_sep {a0 a1 a2 b0 b1 p0 p1 p2 q0 q1 : ℝ}
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb0 : b0 < 0) (hb1 : b1 < 0)
    (hsum : a0 + a1 + a2 + b0 + b1 = 0)
    (hdot : a0 * p0 + a1 * p1 + a2 * p2 + b0 * q0 + b1 * q1 = 0) :
    ¬ ((q0 < p0 ∧ q0 < p1 ∧ q0 < p2 ∧ q1 < p0 ∧ q1 < p1 ∧ q1 < p2) ∨
       (p0 < q0 ∧ p1 < q0 ∧ p2 < q0 ∧ p0 < q1 ∧ p1 < q1 ∧ p2 < q1)) := by
  rintro (⟨h00, h01, h02, h10, h11, h12⟩ | ⟨h00, h10, h20, h01, h11, h21⟩)
  · let M : ℝ := min p0 (min p1 p2)
    have hM0 : M ≤ p0 := min_le_left _ _
    have hM1 : M ≤ p1 := (min_le_right _ _).trans (min_le_left _ _)
    have hM2 : M ≤ p2 := (min_le_right _ _).trans (min_le_right _ _)
    have hq0 : q0 < M := lt_min h00 (lt_min h01 h02)
    have hq1 : q1 < M := lt_min h10 (lt_min h11 h12)
    have hp0 : a0 * M ≤ a0 * p0 := mul_le_mul_of_nonneg_left hM0 ha0.le
    have hp1 : a1 * M ≤ a1 * p1 := mul_le_mul_of_nonneg_left hM1 ha1.le
    have hp2 : a2 * M ≤ a2 * p2 := mul_le_mul_of_nonneg_left hM2 ha2.le
    have hbq0 : b0 * M < b0 * q0 := mul_lt_mul_of_neg_left hq0 hb0
    have hbq1 : b1 * M < b1 * q1 := mul_lt_mul_of_neg_left hq1 hb1
    have hm0 : a0 * M + a1 * M + a2 * M + b0 * M + b1 * M = 0 := by
      linear_combination M * hsum
    linarith
  · let M : ℝ := max p0 (max p1 p2)
    have hM0 : p0 ≤ M := le_max_left _ _
    have hM1 : p1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hM2 : p2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have hq0 : M < q0 := max_lt h00 (max_lt h10 h20)
    have hq1 : M < q1 := max_lt h01 (max_lt h11 h21)
    have hp0 : a0 * p0 ≤ a0 * M := mul_le_mul_of_nonneg_left hM0 ha0.le
    have hp1 : a1 * p1 ≤ a1 * M := mul_le_mul_of_nonneg_left hM1 ha1.le
    have hp2 : a2 * p2 ≤ a2 * M := mul_le_mul_of_nonneg_left hM2 ha2.le
    have hbq0 : b0 * q0 < b0 * M := mul_lt_mul_of_neg_left hq0 hb0
    have hbq1 : b1 * q1 < b1 * M := mul_lt_mul_of_neg_left hq1 hb1
    have hm0 : a0 * M + a1 * M + a2 * M + b0 * M + b1 * M = 0 := by
      linear_combination M * hsum
    linarith

/-- **Wall `w63` theorem**: on `{1 < oblX6 x 3, mustar x = 0}` with distinct
`w63`-depths on `{0, 2, 3, 4, 5, 6}`, `w63 = x 3 - x 6` gives `Minimality.Gen.LexAny F`. -/
theorem w63_closes_wall {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : mustar x = 0)
    (hgen : ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Minimality.Gen.LexAny F := by
  let w : ℝ³ := x 3 - x 6
  have hfac := w63_facings_wall F hc3 hmu
  have hsgn2346 := radon02346_signs F
  have hsgn2356 := radon02356_signs F
  have hv_mem : ∀ i : Fin 6, v023456 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
    intro i; fin_cases i <;> decide
  have hv_inj : Function.Injective v023456 := by decide
  obtain ⟨r, hinj, hmono⟩ : ∃ r : Fin 6 → Fin 6,
      (∀ i j : Fin 6, i ≠ j → r i ≠ r j) ∧
      (∀ i j : Fin 6, (r i).val < (r j).val → ⟪x (v023456 i), w⟫ < ⟪x (v023456 j), w⟫) := by
    let r0 : Fin 6 → Fin 6 := fun i =>
      ⟨(Finset.univ.filter fun k : Fin 6 => ⟪x (v023456 k), w⟫ < ⟪x (v023456 i), w⟫).card, by
        have hlt : (Finset.univ.filter fun k : Fin 6 =>
            ⟪x (v023456 k), w⟫ < ⟪x (v023456 i), w⟫).card < (Finset.univ : Finset (Fin 6)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun heq => by
            have hi : i ∈ Finset.univ.filter (fun k : Fin 6 =>
                ⟪x (v023456 k), w⟫ < ⟪x (v023456 i), w⟫) := by rw [heq]; exact Finset.mem_univ _
            exact lt_irrefl _ (Finset.mem_filter.mp hi).2⟩)
        simpa using hlt⟩
    have hmono_rev : ∀ i j : Fin 6, ⟪x (v023456 i), w⟫ < ⟪x (v023456 j), w⟫ → (r0 i).val < (r0 j).val := by
      intro i j hij
      change (Finset.univ.filter fun k : Fin 6 => ⟪x (v023456 k), w⟫ < ⟪x (v023456 i), w⟫).card <
        (Finset.univ.filter fun k : Fin 6 => ⟪x (v023456 k), w⟫ < ⟪x (v023456 j), w⟫).card
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun k hk => ?_, fun heq => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hk hij
      · have hi : i ∈ Finset.univ.filter (fun k : Fin 6 => ⟪x (v023456 k), w⟫ < ⟪x (v023456 j), w⟫) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
        rw [← heq] at hi
        exact lt_irrefl _ (Finset.mem_filter.mp hi).2
    have hinj : ∀ i j : Fin 6, i ≠ j → r0 i ≠ r0 j := by
      intro i j hij
      have hne : ⟪x (v023456 i), w⟫ ≠ ⟪x (v023456 j), w⟫ :=
        hgen (v023456 i) (hv_mem i) (v023456 j) (hv_mem j) (hv_inj.ne hij)
      rcases lt_or_gt_of_ne hne with h | h
      · exact Fin.val_ne_iff.mp (hmono_rev i j h).ne
      · exact Fin.val_ne_iff.mp (hmono_rev j i h).ne'
    have hmono : ∀ i j : Fin 6, (r0 i).val < (r0 j).val → ⟪x (v023456 i), w⟫ < ⟪x (v023456 j), w⟫ := by
      intro i j hij
      have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have hwne : ⟪x (v023456 i), w⟫ ≠ ⟪x (v023456 j), w⟫ :=
        hgen (v023456 i) (hv_mem i) (v023456 j) (hv_mem j) (hv_inj.ne hne)
      rcases lt_or_gt_of_ne hwne with h | h
      · exact h
      · exact absurd (lt_trans hij (hmono_rev j i h)) (lt_irrefl _)
    exact ⟨r0, hinj, hmono⟩
  have h52 : (r 5).val < (r 2).val := by
    have hw52 : ⟪x (v023456 5), w⟫ < ⟪x (v023456 2), w⟫ := by
      change ⟪x 6, x 3 - x 6⟫ < ⟪x 3, x 3 - x 6⟫
      have hne : w ≠ 0 := fun h => by
        have hf : ⟪F.N 3, w⟫ = 0 := by rw [h, inner_zero_right]
        linarith [hfac.2.2.2.1]
      have hnorm : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hne
      have hsub : ⟪x 3 - x 6, w⟫ = ⟪x 3, w⟫ - ⟪x 6, w⟫ := inner_sub_left (x 3) (x 6) w
      change ⟪x 6, w⟫ < ⟪x 3, w⟫
      linarith
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact hinj 2 5 (by decide) (Fin.ext heq)
    · exact absurd (lt_trans hw52 (hmono 2 5 hlt)) (lt_irrefl _)
  have hnot_02346 : sep23 (r 1) (r 3) (r 0) (r 2) (r 5) = false := by
    by_contra hsep
    have hsep' : sep23 (r 1) (r 3) (r 0) (r 2) (r 5) = true := Bool.eq_true_of_not_eq_false hsep
    dsimp only [sep23] at hsep'
    have hrad := radon02346_depth F w
    rcases hsgn2346 with ⟨hm0, hm2, hm3, hm4, hm6⟩
    apply radon32_no_sep hm0 hm3 hm6 hm2 hm4 (p0 := ⟪x 0, w⟫) (p1 := ⟪x 3, w⟫)
      (p2 := ⟪x 6, w⟫) (q0 := ⟪x 2, w⟫) (q1 := ⟪x 4, w⟫)
      (by linarith [radon02346_sum x]) (by linarith)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsep'
    rcases hsep' with ⟨⟨⟨⟨⟨h10, h12⟩, h15⟩, h30⟩, h32⟩, h35⟩ |
        ⟨⟨⟨⟨⟨h01, h03⟩, h21⟩, h23⟩, h51⟩, h53⟩
    · exact Or.inl ⟨hmono 1 0 h10, hmono 1 2 h12, hmono 1 5 h15,
        hmono 3 0 h30, hmono 3 2 h32, hmono 3 5 h35⟩
    · exact Or.inr ⟨hmono 0 1 h01, hmono 2 1 h21, hmono 5 1 h51,
        hmono 0 3 h03, hmono 2 3 h23, hmono 5 3 h53⟩
  have hnot_0345 : sep22 (r 0) (r 2) (r 3) (r 4) = false := by
    by_contra hsep
    have hsep' : sep22 (r 0) (r 2) (r 3) (r 4) = true := Bool.eq_true_of_not_eq_false hsep
    dsimp only [sep22] at hsep'
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsep'
    apply radon0345_depth F w
    rcases hsep' with ⟨⟨⟨h03, h04⟩, h23⟩, h24⟩ | ⟨⟨⟨h30, h32⟩, h40⟩, h42⟩
    · exact Or.inl ⟨hmono 0 3 h03, hmono 0 4 h04, hmono 2 3 h23, hmono 2 4 h24⟩
    · exact Or.inr ⟨hmono 3 0 h30, hmono 4 0 h40, hmono 3 2 h32, hmono 4 2 h42⟩
  have hnot_02356 : sep23 (r 4) (r 5) (r 0) (r 1) (r 2) = false := by
    by_contra hsep
    have hsep' : sep23 (r 4) (r 5) (r 0) (r 1) (r 2) = true := Bool.eq_true_of_not_eq_false hsep
    dsimp only [sep23] at hsep'
    have hrad := radon02356_depth F w
    rcases hsgn2356 with ⟨hn0, hn2, hn3, hn5, hn6⟩
    apply radon32_no_sep hn0 hn2 hn3 hn5 hn6 (p0 := ⟪x 0, w⟫) (p1 := ⟪x 2, w⟫)
      (p2 := ⟪x 3, w⟫) (q0 := ⟪x 5, w⟫) (q1 := ⟪x 6, w⟫)
      (radon02356_sum x) hrad
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsep'
    rcases hsep' with ⟨⟨⟨⟨⟨h40, h41⟩, h42⟩, h50⟩, h51⟩, h52⟩ |
        ⟨⟨⟨⟨⟨h04, h05⟩, h14⟩, h15⟩, h24⟩, h25⟩
    · exact Or.inl ⟨hmono 4 0 h40, hmono 4 1 h41, hmono 4 2 h42,
        hmono 5 0 h50, hmono 5 1 h51, hmono 5 2 h52⟩
    · exact Or.inr ⟨hmono 0 4 h04, hmono 1 4 h14, hmono 2 4 h24,
        hmono 0 5 h05, hmono 1 5 h15, hmono 2 5 h25⟩
  have hok := wallOrderOk_of_inj hinj h52
  have hinj_b : (r 0 != r 1 && r 0 != r 2 && r 0 != r 3 && r 0 != r 4 && r 0 != r 5 &&
      r 1 != r 2 && r 1 != r 3 && r 1 != r 4 && r 1 != r 5 &&
      r 2 != r 3 && r 2 != r 4 && r 2 != r 5 &&
      r 3 != r 4 && r 3 != r 5 && r 4 != r 5) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinj 0 1 (by decide), hinj 0 2 (by decide)⟩, hinj 0 3 (by decide)⟩,
      hinj 0 4 (by decide)⟩, hinj 0 5 (by decide)⟩, hinj 1 2 (by decide)⟩,
      hinj 1 3 (by decide)⟩, hinj 1 4 (by decide)⟩, hinj 1 5 (by decide)⟩,
      hinj 2 3 (by decide)⟩, hinj 2 4 (by decide)⟩, hinj 2 5 (by decide)⟩,
      hinj 3 4 (by decide)⟩, hinj 3 5 (by decide)⟩, hinj 4 5 (by decide)⟩
  have hdisj : (cyc4Ok (r 0) (r 1) (r 2) (r 3) || cyc5Ok (r 0) (r 1) (r 5) (r 2) (r 3) ||
      cyc5Ok (r 0) (r 3) (r 5) (r 1) (r 4) || cyc6Ok (r 0) (r 3) (r 5) (r 2) (r 1) (r 4)) = true := by
    dsimp only [wallOrderOk] at hok
    have h52_b : decide ((r 5).val < (r 2).val) = true := decide_eq_true h52
    rw [hinj_b, h52_b, hnot_02346, hnot_0345, hnot_02356] at hok
    simpa using hok
  have mk_lc : ∀ {i1 i2 j1 j2 : Fin 6} {d1 : ℝ³},
      quadOk (r i1) (r j1) (r i2) (r j2) = true →
      Minimality.GenQuad.LexClause (x (v023456 j1)) (x (v023456 j2))
        (x (v023456 i1)) (x (v023456 i2)) w d1 0 := by
    intro i1 i2 j1 j2 d1 hq
    dsimp only [quadOk] at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    apply Minimality.GenQuad.lexClause_of_notM
    rintro ⟨h11, h12, h21, h22⟩
    rcases min_lt_iff.mp hq.1 with h1 | h2
    · rcases lt_max_iff.mp h1 with h | h
      · linarith [hmono _ _ h]
      · linarith [hmono _ _ h]
    · rcases lt_max_iff.mp h2 with h | h
      · linarith [hmono _ _ h]
      · linarith [hmono _ _ h]
  have mk_lc2 : ∀ {i1 i2 j1 j2 : Fin 6} {d1 : ℝ³},
      quadOk (r i1) (r j1) (r i2) (r j2) = true →
      Minimality.GenQuad.LexClause (x (v023456 i1)) (x (v023456 i2))
        (x (v023456 j1)) (x (v023456 j2)) w d1 0 := by
    intro i1 i2 j1 j2 d1 hq
    dsimp only [quadOk] at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    apply Minimality.GenQuad.lexClause_of_notM
    rintro ⟨h11, h12, h21, h22⟩
    rcases min_lt_iff.mp hq.2 with h1 | h2
    · rcases lt_max_iff.mp h1 with h | h
      · linarith [hmono _ _ h]
      · linarith [hmono _ _ h]
    · rcases lt_max_iff.mp h2 with h | h
      · linarith [hmono _ _ h]
      · linarith [hmono _ _ h]
  have hpmm := tilt_pmm_signs F
  have hppm := tilt_ppm_signs F
  simp only [Bool.or_eq_true] at hdisj
  rcases hdisj with ((hc4 | hc5a) | hc5b) | hc6
  · have hU : ∀ t ∈ ({2, 3, 6} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, tilt_pmm F⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inr ⟨hfac.2.2.1, Or.inl hpmm.1⟩
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
    have hD : ∀ t ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, tilt_pmm F⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.2.2.2.2.2.1), Or.inl (neg_pos.mpr hpmm.2.1)⟩
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.2.2.2.2.2.2), Or.inl (neg_pos.mpr hpmm.2.2)⟩
    dsimp only [cyc4Ok] at hc4
    exact close_k4_w F c_w0234_inj cyc_w0234 w (tilt_pmm F) hU hD
      (by simpa [c_w0234, v023456] using mk_lc (d1 := tilt_pmm F) hc4)
      (by simpa [c_w0234, v023456] using mk_lc2 (d1 := tilt_pmm F) hc4)
  · have hU : ∀ t ∈ ({2, 3, 6, 7} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, tilt_ppm F⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inr ⟨hfac.2.2.1, Or.inl hppm.1⟩
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl hppm.2.1⟩
    have hD : ∀ t ∈ ({0, 1, 4, 5, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, tilt_ppm F⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.2.2.2.2.2.2), Or.inl (neg_pos.mpr hppm.2.2)⟩
    dsimp only [cyc5Ok] at hc5a
    simp only [Bool.and_eq_true] at hc5a
    rcases hc5a with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact close_k5_w F c_w02634_inj cyc_w02634 w (tilt_ppm F) hU hD
      (by simpa [c_w02634, v023456] using mk_lc (d1 := tilt_ppm F) h1)
      (by simpa [c_w02634, v023456] using mk_lc2 (d1 := tilt_ppm F) h1)
      (by simpa [c_w02634, v023456] using mk_lc (d1 := tilt_ppm F) h2)
      (by simpa [c_w02634, v023456] using mk_lc2 (d1 := tilt_ppm F) h2)
      (by simpa [c_w02634, v023456] using mk_lc (d1 := tilt_ppm F) h3)
      (by simpa [c_w02634, v023456] using mk_lc2 (d1 := tilt_ppm F) h3)
      (by simpa [c_w02634, v023456] using mk_lc (d1 := tilt_ppm F) h4)
      (by simpa [c_w02634, v023456] using mk_lc2 (d1 := tilt_ppm F) h4)
      (by simpa [c_w02634, v023456] using mk_lc (d1 := tilt_ppm F) h5)
      (by simpa [c_w02634, v023456] using mk_lc2 (d1 := tilt_ppm F) h5)
  · have hU : ∀ t ∈ ({3, 6, 7, 8} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, -tilt_pmm F⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl (by rw [inner_neg_right]; exact neg_pos.mpr hpmm.2.1)⟩
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl (by rw [inner_neg_right]; exact neg_pos.mpr hpmm.2.2)⟩
    have hD : ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, -tilt_pmm F⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.1),
          Or.inl (by rw [inner_neg_right, neg_neg]; exact hpmm.1)⟩
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    dsimp only [cyc5Ok] at hc5b
    simp only [Bool.and_eq_true] at hc5b
    rcases hc5b with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact close_k5_w F c_w04625_inj cyc_w04625 w (-tilt_pmm F) hU hD
      (by simpa [c_w04625, v023456] using mk_lc (d1 := -tilt_pmm F) h1)
      (by simpa [c_w04625, v023456] using mk_lc2 (d1 := -tilt_pmm F) h1)
      (by simpa [c_w04625, v023456] using mk_lc (d1 := -tilt_pmm F) h2)
      (by simpa [c_w04625, v023456] using mk_lc2 (d1 := -tilt_pmm F) h2)
      (by simpa [c_w04625, v023456] using mk_lc (d1 := -tilt_pmm F) h3)
      (by simpa [c_w04625, v023456] using mk_lc2 (d1 := -tilt_pmm F) h3)
      (by simpa [c_w04625, v023456] using mk_lc (d1 := -tilt_pmm F) h4)
      (by simpa [c_w04625, v023456] using mk_lc2 (d1 := -tilt_pmm F) h4)
      (by simpa [c_w04625, v023456] using mk_lc (d1 := -tilt_pmm F) h5)
      (by simpa [c_w04625, v023456] using mk_lc2 (d1 := -tilt_pmm F) h5)
  · have hU : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, w⟫ ⟪F.N t, -tilt_ppm F⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl (by rw [inner_neg_right]; exact neg_pos.mpr hppm.2.2)⟩
    have hD : ∀ t ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, -tilt_ppm F⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht; fin_cases t <;> simp at ht
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.1),
          Or.inl (by rw [inner_neg_right, neg_neg]; exact hppm.1)⟩
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr (by dsimp only; exact hfac.2.2.2.2.2.2.2.1),
          Or.inl (by rw [inner_neg_right, neg_neg]; exact hppm.2.1)⟩
    dsimp only [cyc6Ok] at hc6
    simp only [Bool.and_eq_true] at hc6
    rcases hc6 with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨q0123, q0124⟩, q0125⟩, q0134⟩, q0135⟩, q0145⟩,
      q0234⟩, q0235⟩, q0245⟩, q0345⟩, q1234⟩, q1235⟩, q1245⟩, q1345⟩, q2345⟩
    exact close_k6_w F c_w046325_inj cyc_w046325 w (-tilt_ppm F) hU hD
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0123)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0123)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0124)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0124)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0125)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0125)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0134)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0134)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0135)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0135)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0145)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0145)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0234)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0234)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0235)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0235)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0245)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0245)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q0345)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q0345)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q1234)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q1234)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q1235)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q1235)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q1245)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q1245)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q1345)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q1345)
      (by simpa [c_w046325, v023456] using mk_lc (d1 := -tilt_ppm F) q2345)
      (by simpa [c_w046325, v023456] using mk_lc2 (d1 := -tilt_ppm F) q2345)

/-- **Wall `E23` theorem** (`pi24` mirror of `w63_closes_wall`): on
`{1 < oblX2 x 3, mu23 x = 0}` with distinct `E23`-depths on `{0, 2, 3, 4, 5, 6}`,
`E23 = x 3 - x 2` gives `Minimality.Gen.LexAny F`. -/
theorem e23_closes_wall {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : mu23 x = 0)
    (hgen : ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫) :
    Minimality.Gen.LexAny F := by
  have hc3' : 1 < oblX6 (x ∘ pi24) 3 := by simpa [oblX6_comp_pi24, pi24_3] using hb3
  have hmu' : mustar (x ∘ pi24) = 0 := by rwa [mustar_comp_pi24]
  have hgen' : ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪(x ∘ pi24) i, (x ∘ pi24) 3 - (x ∘ pi24) 6⟫ ≠
        ⟪(x ∘ pi24) j, (x ∘ pi24) 3 - (x ∘ pi24) 6⟫ := by
    intro i hi j hj hij
    have hi' : pi24 i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
      fin_cases i <;> simp at hi ⊢
    have hj' : pi24 j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
      fin_cases j <;> simp at hj ⊢
    have hij' : pi24 i ≠ pi24 j := fun heq => by
      have hinv : pi24 (pi24 i) = pi24 (pi24 j) := congrArg pi24 heq
      have hpi : ∀ a : Fin 7, pi24 (pi24 a) = a := by decide
      rw [hpi i, hpi j] at hinv
      exact hij hinv
    have h1 := hgen (pi24 i) hi' (pi24 j) hj' hij'
    dsimp only [Function.comp_apply]
    rw [pi24_3, pi24_6]
    exact h1
  exact lexAny_sym F (w63_closes_wall (sym24 F) hc3' hmu' hgen')

end Minimality.T24.A20
