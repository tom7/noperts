module

public import Minimality.R012
public import Minimality.Q45Leaf
public import Minimality.CornerU
public import Minimality.DiagCross
public import Minimality.FaceChordFac


@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012
variable {x : Fin 7 → ℝ³}

/-- f346 root vector on 012 ∩ 346, division-free: a positive multiple of Carbon's u08. -/
noncomputable def u08 (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (F.f 0 (x 4) - F.f 0 (x 6)) • (x 3 - x 6) + (F.f 0 (x 6) - F.f 0 (x 3)) • (x 4 - x 6)

private theorem exists_coords (a b c u : ℝ³) (h : det3 a b c ≠ 0) :
    ∃ p q r : ℝ, u = p • a + q • b + r • c := by
  have hv : vol3 a b c ≠ 0 := by
    have : vol3 a b c = det3 a b c := by simp only [det3_expand, vol3]; ring
    rwa [this]
  refine ⟨vol3 u b c / vol3 a b c, vol3 a u c / vol3 a b c, vol3 a b u / vol3 a b c, ?_⟩
  have e : ∀ t : ℝ, vol3 a b c * (t / vol3 a b c) = t := fun t => by field_simp
  refine smul_right_injective _ hv ?_
  simp only
  rw [vol3_smul_cramer, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e, e, e]

private theorem pair3 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (p q r : ℝ) :
    ⟪F.N t, p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)⟫ =
      p * (F.f t (x 0) - F.f t (x 1)) + q * (F.f t (x 2) - F.f t (x 1)) +
        r * (F.f t (x 6) - F.f t (x 1)) := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]

theorem inner_comb36 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (α β : ℝ) :
    ⟪F.N t, α • (x 3 - x 6) + β • (x 4 - x 6)⟫ =
      α * (F.f t (x 3) - F.f t (x 6)) + β * (F.f t (x 4) - F.f t (x 6)) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]

theorem inner_u08 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u08 F⟫ = (F.f 0 (x 4) - F.f 0 (x 6)) * (F.f t (x 3) - F.f t (x 6)) +
      (F.f 0 (x 6) - F.f 0 (x 3)) * (F.f t (x 4) - F.f t (x 6)) := inner_comb36 F t _ _

theorem inner_N0_u08 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 0, u08 F⟫ = 0 := by
  rw [inner_u08]; ring

theorem inner_N8_u08 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 8, u08 F⟫ = 0 := by
  rw [inner_u08, F.zero 8 3 (by decide), F.zero 8 4 (by decide), F.zero 8 6 (by decide)]; ring

theorem inner_N4_u08 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 4, u08 F⟫ = (F.f 0 (x 4) - F.f 0 (x 6)) * F.f 4 (x 3) := by
  rw [inner_u08, F.zero 4 4 (by decide), F.zero 4 6 (by decide)]; ring

theorem inner_N7_u08 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 7, u08 F⟫ = (F.f 0 (x 6) - F.f 0 (x 3)) * F.f 7 (x 4) := by
  rw [inner_u08, F.zero 7 3 (by decide), F.zero 7 6 (by decide)]; ring

theorem inner_N3_u08 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 3, u08 F⟫ = (F.f 0 (x 4) - F.f 0 (x 3)) * (- F.f 3 (x 6)) := by
  rw [inner_u08, F.zero 3 3 (by decide), F.zero 3 4 (by decide)]; ring

theorem inner_N5_u08 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, u08 F⟫ = (F.f 0 (x 4) - F.f 0 (x 6)) * F.f 5 (x 3) +
      (F.f 0 (x 6) - F.f 0 (x 3)) * F.f 5 (x 4) := by
  rw [inner_u08, F.zero 5 6 (by decide)]; ring

theorem inner_N1_u08 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 1, u08 F⟫ = (F.f 0 (x 4) - F.f 0 (x 6)) * F.f 1 (x 3) +
      (F.f 0 (x 6) - F.f 0 (x 3)) * F.f 1 (x 4) := by
  rw [inner_u08, F.zero 1 6 (by decide)]; ring

private theorem view_inner (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v d : ℝ³) (ε : ℝ) :
    ⟪F.N t, v + ε • d⟫ = ⟪F.N t, v⟫ + ε * ⟪F.N t, d⟫ := by
  rw [inner_add_right, real_inner_smul_right]

theorem inner_d (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, x 2 - x 1⟫ = F.f t (x 2) - F.f t (x 1) := F.inner_sub t 2 1

lemma cross_smul_N (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (a b : ℝ³) (ha : ⟪F.N t, a⟫ = 0)
    (hb : ⟪F.N t, b⟫ = 0) (hN : F.N t ≠ 0) : ∃ κ : ℝ, cross a b = κ • F.N t := by
  by_cases hab : cross a b = 0
  · exact ⟨0, by simp [hab]⟩
  · have hcl := cross_eq_zero_of_perp2 ha hb (inner_cross_left a b) (inner_cross_right a b) hab
    exact ⟨_, eq_smul_of_cross_eq_zero hN hcl⟩

lemma N_ne_zero (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (i : Fin 7) (hi : i ∉ s0x_S24 t)
    (j : Fin 7) (hj : j ∈ s0x_S24 t) : F.N t ≠ 0 := by
  intro h0
  have := F.inner_sub t i j
  rw [h0, inner_zero_left, F.zero t j hj] at this
  have := F.neg t i hi
  linarith

lemma inner_eq3 (p q : ℝ³) : ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- Ω * D034 > 0 where D034 = det3 (0-6) (3-6) (4-6). -/
theorem omega_mul_D034_pos (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6) := by
  have hD := omega_mul_det3_0246_pos_unconditional F
  have hN4 : F.N 4 ≠ 0 := N_ne_zero F 4 3 (by decide) 0 (by decide)
  obtain ⟨k4, hk4⟩ := cross_smul_N F 4 (x 0 - x 6) (x 4 - x 6)
    (by rw [F.inner_sub, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 6 (by decide)]; ring) hN4
  have e : ∀ y : ℝ³, det3 (x 0 - x 6) (y - x 6) (x 4 - x 6) = - ⟪cross (x 0 - x 6) (x 4 - x 6), y - x 6⟫ := by
    intro y
    simp only [det3_expand, inner_eq3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]; ring
  have h2 := e (x 2)
  have h3 := e (x 3)
  rw [hk4, real_inner_smul_left, F.inner_sub 4 2 6, F.zero 4 6 (by decide)] at h2
  rw [hk4, real_inner_smul_left, F.inner_sub 4 3 6, F.zero 4 6 (by decide)] at h3
  have f2 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  have f3 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have key : det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6) * F.f 4 (x 2) =
      det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6) * F.f 4 (x 3) := by
    rw [h2, h3]; ring
  have h1 : (Ω * det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6)) * F.f 4 (x 2) =
      (Ω * det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6)) * F.f 4 (x 3) := by
    linear_combination Ω * key
  have h2 := mul_neg_of_pos_of_neg hD f3
  by_contra hn; push Not at hn
  have := mul_nonneg_of_nonpos_of_nonpos hn f2.le
  linarith

/-- Ω * κ(0,4,3,2) < 0. -/
theorem omega_mul_kappa0432_neg (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4) < 0 := by
  have hD := omega_mul_D034_pos F
  have hN3 : F.N 3 ≠ 0 := N_ne_zero F 3 6 (by decide) 0 (by decide)
  obtain ⟨k3, hk3⟩ := cross_smul_N F 3 (x 3 - x 0) (x 0 - x 4)
    (by rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 0 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 3 0 (by decide), F.zero 3 4 (by decide)]; ring) hN3
  have eκ : det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4) = - ⟪cross (x 3 - x 0) (x 0 - x 4), x 2 - x 4⟫ := by
    simp only [det3_expand, inner_eq3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]; ring
  have eD : det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6) = ⟪cross (x 3 - x 0) (x 0 - x 4), x 6 - x 0⟫ := by
    simp only [det3_expand, inner_eq3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]; ring
  rw [hk3, real_inner_smul_left, F.inner_sub 3 2 4, F.zero 3 4 (by decide)] at eκ
  rw [hk3, real_inner_smul_left, F.inner_sub 3 6 0, F.zero 3 0 (by decide)] at eD
  have f2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have f6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have key : det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4) * F.f 3 (x 6) =
      - det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6) * F.f 3 (x 2) := by
    rw [eκ, eD]; ring
  have h1 : (Ω * det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4)) * F.f 3 (x 6) =
      -(Ω * det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6)) * F.f 3 (x 2) := by
    linear_combination Ω * key
  have h2 : 0 < -(Ω * det3 (x 0 - x 6) (x 3 - x 6) (x 4 - x 6)) * F.f 3 (x 2) := by
    have := mul_neg_of_pos_of_neg hD f2
    linarith
  by_contra hn; push Not at hn
  have := mul_nonpos_of_nonneg_of_nonpos hn f6.le
  linarith


lemma quad_eq_r : ∀ i : ZMod 4, x (quad (0 : Fin 7) 4 3 2 i) = quad (x 0) (x 4) (x 3) (x 2) i := by
  intro i; fin_cases i <;> rfl

lemma ext_vertices (q : Fin 7) (hqS : q ∉ s0x_S24 0) (hqr : ∀ j : ZMod 4, q ≠ quad (0 : Fin 7) 4 3 2 j) :
    q = 5 ∨ q = 6 := by
  revert q; decide

lemma mid_vertices (q : Fin 7) (hqS : q ∈ s0x_S24 0) (hqr : ∀ j : ZMod 4, q ≠ quad (0 : Fin 7) 4 3 2 j) :
    q = 1 := by
  revert q; decide

private lemma far_cand (m : ZMod 4) (hm : m ≠ 2) (hmS : quad (0 : Fin 7) 4 3 2 m ∉ s0x_S24 0) : m = 1 := by
  revert m; decide

private lemma far_cand' (m : ZMod 4) (hm : m ≠ 1) (hmS : quad (0 : Fin 7) 4 3 2 m ∉ s0x_S24 0) : m = 2 := by
  revert m; decide

theorem coords_view (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h0 : ⟪F.N 0, u⟫ = 0)
    (h5 : ⟪F.N 5, u⟫ < 0) (h1 : ⟪F.N 1, u⟫ < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ u = A • (x 0 - x 1) + B • (x 2 - x 1) := by
  obtain ⟨p, q, r, hu⟩ := exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) u (omega_ne_zero F)
  rw [hu, pair3] at h0 h5 h1
  have f0 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f5 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have f1 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at h0
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at h5
  rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at h1
  have hr : r = 0 := by
    have : r * F.f 0 (x 6) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h f0.ne
  have hp : 0 < p := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f5.le]
  have hq : 0 < q := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f1.le]
  exact ⟨p, q, hp, hq, by rw [hu, hr, zero_smul, add_zero]⟩

theorem quadRim0432 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (hN2 : 0 < ⟪F.N 2, u⟫)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN3 : 0 < ⟪F.N 3, u⟫) (hN8 : ⟪F.N 8, u⟫ < 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN6 : 0 < ⟪F.N 6, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (quad (x 0) (x 4) (x 3) (x 2) j - quad (x 0) (x 4) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (x 5 - quad (x 0) (x 4) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (x 6 - quad (x 0) (x 4) (x 3) (x 2) i) u) := by
  have hne_04 := cross_ne_zero_of_facet_sign F 4 0 4 (by decide) (by decide) hN4.ne 0 (by decide) (by decide)
  have hne_43 := cross_ne_zero_of_facet_sign F 8 4 3 (by decide) (by decide) hN8.ne 4 (by decide) (by decide)
  have hne_32 := cross_ne_zero_of_facet_sign F 7 3 2 (by decide) (by decide) hN7.ne 8 (by decide) (by decide)
  have hne_20 := cross_ne_zero_of_facet_sign F 2 2 0 (by decide) (by decide) hN2.ne' 5 (by decide) (by decide)
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F 4 3 0 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN4, hN3⟩ hne_04
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_ridge F 8 3 4 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN8, hN3⟩ hne_43
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F 7 6 3 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN7, hN6⟩ hne_32
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_edgeOn F 0 2 0 (by decide) (by decide) u hN0 hne_20
  have c01 : det3 (x 4 - x 0) (x 3 - x 0) u = det3 (x 3 - x 4) (x 0 - x 4) u :=
    RimFromSigns.det3_cycle_triangle (x 0) (x 4) (x 3) u
  have c12 : det3 (x 3 - x 4) (x 2 - x 4) u = det3 (x 2 - x 3) (x 4 - x 3) u :=
    RimFromSigns.det3_cycle_triangle (x 4) (x 3) (x 2) u
  have c23 : det3 (x 2 - x 3) (x 0 - x 3) u = det3 (x 0 - x 2) (x 3 - x 2) u :=
    RimFromSigns.det3_cycle_triangle (x 3) (x 2) (x 0) u
  have h0_3 : 0 < σ₀ * det3 (x 4 - x 0) (x 3 - x 0) u := hσ₀ 3 (by decide)
  have h1_0 : 0 < σ₁ * det3 (x 3 - x 4) (x 0 - x 4) u := hσ₁ 0 (by decide)
  have h1_0' : 0 < σ₁ * det3 (x 4 - x 0) (x 3 - x 0) u := by rw [c01]; exact h1_0
  have hσ01 : 0 < σ₀ * σ₁ := sign_prod h0_3 h1_0'
  have h1_2 : 0 < σ₁ * det3 (x 3 - x 4) (x 2 - x 4) u := hσ₁ 2 (by decide)
  have h2_4 : 0 < σ₂ * det3 (x 2 - x 3) (x 4 - x 3) u := hσ₂ 4 (by decide)
  have h2_4' : 0 < σ₂ * det3 (x 3 - x 4) (x 2 - x 4) u := by rw [c12]; exact h2_4
  have hσ12 : 0 < σ₁ * σ₂ := sign_prod h1_2 h2_4'
  have h2_0 : 0 < σ₂ * det3 (x 2 - x 3) (x 0 - x 3) u := hσ₂ 0 (by decide)
  have h3_3 : 0 < σ₃ * det3 (x 0 - x 2) (x 3 - x 2) u := hσ₃ 3 (by decide)
  have h3_3' : 0 < σ₃ * det3 (x 2 - x 3) (x 0 - x 3) u := by rw [c23]; exact h3_3
  have hσ23 : 0 < σ₂ * σ₃ := sign_prod h2_0 h3_3'
  have hσ02 : 0 < σ₀ * σ₂ := sign_transfer hσ01 hσ12
  have hσ03 : 0 < σ₀ * σ₃ := sign_transfer hσ02 hσ23
  refine ⟨σ₀, hσ₀_ne, ?_, ?_, ?_⟩
  · intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_3
    · exact hσ₀ 2 (by decide)
    · exact sign_transfer hσ01 (hσ₁ 0 (by decide))
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ01 h1_2
    · exact sign_transfer hσ02 h2_0
    · exact sign_transfer hσ02 h2_4
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ03 (hσ₃ 4 (by decide))
    · exact sign_transfer hσ03 h3_3
    · exact False.elim (hj1 rfl)
  · intro i
    fin_cases i
    · exact hσ₀ 5 (by decide)
    · exact sign_transfer hσ01 (hσ₁ 5 (by decide))
    · exact sign_transfer hσ02 (hσ₂ 5 (by decide))
    · exact sign_transfer hσ03 (hσ₃ 5 (by decide))
  · intro i
    fin_cases i
    · exact hσ₀ 6 (by decide)
    · exact sign_transfer hσ01 (hσ₁ 6 (by decide))
    · exact sign_transfer hσ02 (hσ₂ 6 (by decide))
    · exact sign_transfer hσ03 (hσ₃ 6 (by decide))

private theorem rim_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (hN5 : ⟪F.N 5, u⟫ < 0) (hN1 : ⟪F.N 1, u⟫ < 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN3 : 0 < ⟪F.N 3, u⟫) (hN8 : ⟪F.N 8, u⟫ < 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN6 : 0 < ⟪F.N 6, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (quad (x 0) (x 4) (x 3) (x 2) j - quad (x 0) (x 4) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (x 5 - quad (x 0) (x 4) (x 3) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 4) (x 3) (x 2) (i + 1) - quad (x 0) (x 4) (x 3) (x 2) i)
          (x 6 - quad (x 0) (x 4) (x 3) (x 2) i) u) ∧
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x 1 = x 2 + s • (x 0 - x 2) + δ • u := by
  obtain ⟨A, B, hA, hB, hu⟩ := coords_view F hN0 hN5 hN1
  have hN2 : 0 < ⟪F.N 2, u⟫ := by
    have hu' : u = A • (x 0 - x 1) + B • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
      rw [hu, zero_smul, add_zero]
    rw [hu', pair3, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    have := F.neg 2 1 (by decide)
    nlinarith
  obtain ⟨ρ, hρ, hcyc, hin5, hin6⟩ := quadRim0432 F hN0 hN2 hN4 hN3 hN8 hN7 hN6
  have hΩ := omega_ne_zero F
  refine ⟨ρ, hρ, ?_, hcyc, hin5, hin6, A / (A + B), -1 / (A + B), by positivity, ?_, ?_, ?_⟩
  · have h3 : 0 < ρ * det3 (x 0 - x 2) (x 6 - x 2) u := hin6 3
    have e : det3 (x 0 - x 2) (x 6 - x 2) u =
        -(A + B) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      rw [hu]
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [e] at h3
    by_contra hn; push Not at hn
    have : (A + B) * (ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) ≥ 0 :=
      mul_nonneg (by linarith) hn
    nlinarith
  · rw [div_lt_one (by linarith)]; linarith
  · exact div_ne_zero (by norm_num) (by linarith)
  · rw [hu]
    have hAB : A + B ≠ 0 := by linarith
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring


/-- Generic leaf on rim `(0,4,3,2)` of facet 012 at the views `b + ε c`, `ε → 0+`
(`b`, `c` in the plane of 012, `N8 b = 0`, `N8 c < 0`, strict facet signs at `b`). -/
theorem leaf0432 (F : S0xFac 9 s0x_S24 x) (b c : ℝ³)
    (hb0 : ⟪F.N 0, b⟫ = 0) (hc0 : ⟪F.N 0, c⟫ = 0)
    (hb1 : ⟪F.N 1, b⟫ < 0) (hb5 : ⟪F.N 5, b⟫ < 0) (hb4 : ⟪F.N 4, b⟫ < 0)
    (hb3 : 0 < ⟪F.N 3, b⟫) (hb7 : ⟪F.N 7, b⟫ < 0) (hb6 : 0 < ⟪F.N 6, b⟫)
    (hb8 : ⟪F.N 8, b⟫ = 0) (hc8 : ⟪F.N 8, c⟫ < 0)
    (hbase : min ⟪x 0, b⟫ ⟪x 3, b⟫ < max ⟪x 4, b⟫ ⟪x 2, b⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, b⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, c⟫ ≠ 0)
    (w : ZMod 4) (hw : w = 1 ∨ w = 2)
    (hfar : ∀ m : ZMod 4, m ≠ w → quad (0 : Fin 7) 4 3 2 m ∉ s0x_S24 0 →
      F.f 0 (x (quad (0 : Fin 7) 4 3 2 w)) < F.f 0 (x (quad (0 : Fin 7) 4 3 2 m)))
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x (quad (0 : Fin 7) 4 3 2 w) - x 2)⟫ ≠ 0 ∨
      ⟪x (quad (0 : Fin 7) 4 3 2 w) - x 2, x 0 - x 2⟫ < 0 ∨
      ⟪x (quad (0 : Fin 7) 4 3 2 w) - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  set p : ZMod 4 → ℝ³ := quad (x 0) (x 4) (x 3) (x 2) with hp
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩdef
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evn : ∀ N : ℝ³, ⟪N, b⟫ < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪N, b + ε • c⟫ < 0 := by
    intro N hN
    have := eventually_pos_affine (A := -⟪N, b⟫) (B := -⟪N, c⟫) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [inner_add_right, real_inner_smul_right]; linarith
  have evp : ∀ N : ℝ³, 0 < ⟪N, b⟫ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪N, b + ε • c⟫ := by
    intro N hN
    have := eventually_pos_affine (A := ⟪N, b⟫) (B := ⟪N, c⟫) (Or.inl hN)
    filter_upwards [this] with ε hε
    rw [inner_add_right, real_inner_smul_right]; exact hε
  have e1 := evn _ hb1
  have e5 := evn _ hb5
  have e4 := evn _ hb4
  have e7 := evn _ hb7
  have e3 := evp _ hb3
  have e6 := evp _ hb6
  have x0 : ∀ ε : ℝ, ⟪F.N 0, b + ε • c⟫ = 0 := by
    intro ε; rw [view_inner, hb0, hc0]; ring
  have x8 : ∀ ε : ℝ, 0 < ε → ⟪F.N 8, b + ε • c⟫ < 0 := by
    intro ε hε
    rw [view_inner, hb8]; nlinarith
  have hk : 0 < (-Ω) * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) := by
    have h := omega_mul_kappa0432_neg F
    change 0 < (-Ω) * det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4)
    linarith
  have hcyc_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < (-Ω) * triD p (b + ε • c) i := by
    filter_upwards [e1, e5, e4, e7, e3, e6, ev0] with ε h1 h5 h4 h7 h3 h6 hε
    obtain ⟨ρ, hρ, hρΩ, hcyc, -, -, -⟩ := rim_data F (x0 ε) h5 h1 h4 h3 (x8 ε hε) h7 h6
    intro i
    have hne1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hne2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    have h := hcyc i (i + 2) hne1 hne2
    have hT : 0 < (-(ρ * Ω)) * (ρ * triD p (b + ε • c) i) := mul_pos (by linarith) h
    have e : (-(ρ * Ω)) * (ρ * triD p (b + ε • c) i) =
        ρ ^ 2 * ((-Ω) * triD p (b + ε • c) i) := by ring
    rw [e] at hT
    exact pos_of_mul_pos_right hT (sq_nonneg ρ)
  have hU := cornerU_mirror p b c (-Ω) hcyc_ev hk hbase hgen
  obtain ⟨ε, h1, h5, h4, h7, h3, h6, hε, hinjU⟩ :=
    (e1.and (e5.and (e4.and (e7.and (e3.and (e6.and (ev0.and hU))))))).exists
  have hε' : 0 < ε := hε
  set u := b + ε • c with hu
  obtain ⟨ρ, hρ, hρΩ, hcyc, hin5, hin6, s, δ, hs0, hs1, hδ, hmid⟩ :=
    rim_data F (x0 ε) h5 h1 h4 h3 (x8 ε hε') h7 h6
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) hinjU.2
  set r : ZMod 4 → Fin 7 := quad (0 : Fin 7) 4 3 2 with hr
  have hrx : ∀ i, x (r i) = p i := quad_eq_r
  refine ⟨u, 4, inferInstance, r, 3, w, ρ, x0 ε, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quad (0 : Fin 7) 4 3 2 3 ∈ s0x_S24 0; decide
  · show quad (0 : Fin 7) 4 3 2 (3 + 1) ∈ s0x_S24 0; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    rcases ext_vertices q hqS hqr with rfl | rfl
    · exact hin5 i
    · exact hin6 i
  · intro q hqS hqr
    have hq1 := mid_vertices q hqS hqr
    subst hq1
    refine ⟨s, δ, hs0, hs1, hδ, ?_⟩
    change x 1 = x 2 + s • (x 0 - x 2) + δ • u
    exact hmid
  · simp_rw [hrx]; exact hinjU.1
  · simp_rw [hrx]; exact Or.inl h_uni
  · rcases hw with rfl | rfl <;> (show _ ∉ s0x_S24 0; decide)
  · exact hfar
  · exact hoff

/-- **q012_f346_pos_A, 4-rim (0,4,3,2) case.**  Case conditions: `c4 < 1 < c3` (frame-free:
`f0 x3 < f0 x6 < f0 x4`), `⟪N6, u08⟫ > 0`, the depth condition at the base view `u08`,
`f8 x2 < f8 x1` (`⟪N8, x2 - x1⟫ < 0`; census: automatic in this case, not proved), tie genericity,
`hoff`.  View `u08 + ε (x 2 - x 1)`.  `⟪N3, u08⟫ > 0` is automatic (derived). -/
theorem q012_f346_pos_A_4 (F : S0xFac 9 s0x_S24 x)
    (hc3 : F.f 0 (x 3) < F.f 0 (x 6)) (hc4 : F.f 0 (x 6) < F.f 0 (x 4))
    (hN6 : 0 < ⟪F.N 6, u08 F⟫)
    (hN8 : F.f 8 (x 2) < F.f 8 (x 1))
    (hbase : min ⟪x 0, u08 F⟫ ⟪x 3, u08 F⟫ < max ⟪x 4, u08 F⟫ ⟪x 2, u08 F⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, u08 F⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, x 2 - x 1⟫ ≠ 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨
      ⟪x 3 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 3 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  have hPpos : 0 < F.f 0 (x 4) - F.f 0 (x 6) := by linarith
  have hQpos : 0 < F.f 0 (x 6) - F.f 0 (x 3) := by linarith
  refine leaf0432 F (u08 F) (x 2 - x 1) (inner_N0_u08 F) ?_ ?_ ?_ ?_ ?_ ?_ hN6
    (inner_N8_u08 F) ?_ hbase hgen 2 (Or.inr rfl) ?_ hoff
  · rw [inner_d, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]; ring
  · rw [inner_N1_u08]
    have a := mul_neg_of_pos_of_neg hPpos (F.neg 1 3 (by decide))
    have b := mul_neg_of_pos_of_neg hQpos (F.neg 1 4 (by decide))
    linarith
  · rw [inner_N5_u08]
    have a := mul_neg_of_pos_of_neg hPpos (F.neg 5 3 (by decide))
    have b := mul_neg_of_pos_of_neg hQpos (F.neg 5 4 (by decide))
    linarith
  · rw [inner_N4_u08]; exact mul_neg_of_pos_of_neg hPpos (F.neg 4 3 (by decide))
  · rw [inner_N3_u08]
    exact mul_pos (by linarith) (by linarith [F.neg 3 6 (by decide)])
  · rw [inner_N7_u08]; exact mul_neg_of_pos_of_neg hQpos (F.neg 7 4 (by decide))
  · rw [inner_d]; linarith
  · intro m hm hmS
    have := far_cand m hm hmS
    subst this
    show F.f 0 (x 3) < F.f 0 (x 4)
    linarith

/-- **q012_f346_B, 4-rim (0,4,3,2) case.**  Case conditions: `c3 < 1 < c4`
(`f0 x4 < f0 x6 < f0 x3`), `⟪N6, -u08⟫ > 0`, the depth condition at `-u08`
(`min(z0, z3) < max(z4, z2)`, i.e. not `{0,3}`-high), `f8 x1 < f8 x2` (`⟪N8, x2 - x1⟫ > 0`;
census: automatic here), genericity, `hoff` at vertex 4.  View `-u08 + ε (x 1 - x 2)`.
`⟪N3, -u08⟫ > 0` and `hfar` (w = 4) are automatic. -/
theorem q012_f346_B_4 (F : S0xFac 9 s0x_S24 x)
    (hc4 : F.f 0 (x 4) < F.f 0 (x 6)) (hc3 : F.f 0 (x 6) < F.f 0 (x 3))
    (hN6 : 0 < ⟪F.N 6, -u08 F⟫)
    (hN8 : F.f 8 (x 1) < F.f 8 (x 2))
    (hbase : min ⟪x 0, -u08 F⟫ ⟪x 3, -u08 F⟫ < max ⟪x 4, -u08 F⟫ ⟪x 2, -u08 F⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, -u08 F⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, x 1 - x 2⟫ ≠ 0)
    (hoff : ⟪F.N 0, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨
      ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  have hPneg : F.f 0 (x 4) - F.f 0 (x 6) < 0 := by linarith
  have hQneg : F.f 0 (x 6) - F.f 0 (x 3) < 0 := by linarith
  have inn : ∀ t : Fin 9, ⟪F.N t, -u08 F⟫ = - ⟪F.N t, u08 F⟫ := fun t => inner_neg_right _ _
  refine leaf0432 F (-u08 F) (x 1 - x 2) (by rw [inn, inner_N0_u08]; ring) ?_ ?_ ?_ ?_ ?_ ?_ hN6
    (by rw [inn, inner_N8_u08]; ring) ?_ hbase hgen 1 (Or.inl rfl) ?_ hoff
  · rw [F.inner_sub, F.zero 0 1 (by decide), F.zero 0 2 (by decide)]; ring
  · rw [inn, inner_N1_u08]
    have a := mul_pos_of_neg_of_neg hPneg (F.neg 1 3 (by decide))
    have b := mul_pos_of_neg_of_neg hQneg (F.neg 1 4 (by decide))
    linarith
  · rw [inn, inner_N5_u08]
    have a := mul_pos_of_neg_of_neg hPneg (F.neg 5 3 (by decide))
    have b := mul_pos_of_neg_of_neg hQneg (F.neg 5 4 (by decide))
    linarith
  · rw [inn, inner_N4_u08]; have := mul_pos_of_neg_of_neg hPneg (F.neg 4 3 (by decide)); linarith
  · rw [inn, inner_N3_u08]
    have : (F.f 0 (x 4) - F.f 0 (x 3)) * (- F.f 3 (x 6)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith [F.neg 3 6 (by decide)])
    linarith
  · rw [inn, inner_N7_u08]; have := mul_pos_of_neg_of_neg hQneg (F.neg 7 4 (by decide)); linarith
  · rw [F.inner_sub]; linarith
  · intro m hm hmS
    have := far_cand' m hm hmS
    subst this
    show F.f 0 (x 4) < F.f 0 (x 3)
    linarith

end Minimality.T24.R012

