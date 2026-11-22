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
  Minimality.T24.Par Minimality.T24

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
theorem e23_closes_mu23_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x)
    (hgen : ∀ i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫) :
    Minimality.Gen.LexAny F := by
  have hC' : CbarIn (x ∘ pi24) := (cbarIn_comp_pi24 x).2 hC
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
  exact lexAny_sym F (w63_closes_mustar_pos (sym24 F) hC' hc3' hmu' hgen')

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

/-- On `CbarIn` with `mustar ≤ 0`, `0 < Delta24 x`. -/
theorem delta_pos_of_mustar_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
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
  have hom4 : 0 < omega4 x + 1 := by linarith [hC.2.1]
  have hom5 : 0 < omega5 x + 1 := by linarith [hC.2.2.1]
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

private theorem one_add_omega4_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
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

private theorem one_add_omega5_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
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

/-- On `¬ FacetCell24 fs` with `0 < al, 0 < be, be ≤ 1, al ≤ 1` (from `par2546_quad`),
`0 ≤ mustar x ∨ 0 ≤ mu23 x`. -/
theorem mustar_or_mu23_nonneg {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hz : ¬ FacetCell24 fs) {al be : ℝ}
    (halp : 0 < al) (hbep : 0 < be)
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
    exact absurd hneg (not_lt.mpr (mul_nonneg hbep.le hn))
  have hk5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0 := by
    have hme := mu23_eq F hq
    have hid : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) =
        mu23 x - (1 - al) * (1 + omega4 x) := by rw [hme]; ring
    have hneg : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) < 0 := by
      rw [hid]
      have : 0 ≤ (1 - al) * (1 + omega4 x) := mul_nonneg (sub_nonneg.mpr hal) hom4.le
      linarith [hnot.2]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg halp.le hn))
  exact hz (facetCell_0345 fs h hk4 hk5)

/-- Strict version on `¬ FacetCell24 fs` with `0 < al, 0 < be, be < 1, al < 1`:
`0 < mustar x ∨ 0 < mu23 x`. -/
theorem mustar_or_mu23_pos {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hz : ¬ FacetCell24 fs) {al be : ℝ}
    (halp : 0 < al) (hbep : 0 < be)
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
    exact absurd hneg (not_lt.mpr (mul_nonneg hbep.le hn))
  have hk5 : oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5) < 0 := by
    have hme := mu23_eq F hq
    have hid : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) =
        mu23 x - (1 - al) * (1 + omega4 x) := by rw [hme]; ring
    have hneg : al * (oblX0 x 5 + oblX6 x 5 + omega4 x * (1 - oblX2 x 5)) < 0 := by
      rw [hid]
      have : 0 < (1 - al) * (1 + omega4 x) := mul_pos (sub_pos.mpr hal) hom4
      linarith [hnot.2]
    by_contra hn; push Not at hn
    exact absurd hneg (not_lt.mpr (mul_nonneg halp.le hn))
  exact hz (facetCell_0345 fs h hk4 hk5)

end Minimality.T24.A20
