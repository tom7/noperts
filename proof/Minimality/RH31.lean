module

public import Minimality.R012F
public import Minimality.Q45Tie
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.H31
variable {x : Fin 7 → ℝ³}

/-- `u31 = f1(x4) e5 - f1(x5) e4`, a positive multiple of Carbon's `b5 e4 - b4 e5` (the line 0345 cap 016). -/
noncomputable def u31 (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  F.f 1 (x 4) • (x 5 - x 0) - F.f 1 (x 5) • (x 4 - x 0)

theorem inner_u31 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u31 F⟫ = F.f 1 (x 4) * (F.f t (x 5) - F.f t (x 0)) - F.f 1 (x 5) * (F.f t (x 4) - F.f t (x 0)) := by
  unfold u31
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]

private theorem pair3' (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (p q r : ℝ) :
    ⟪F.N t, p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)⟫ =
      p * (F.f t (x 0) - F.f t (x 1)) + q * (F.f t (x 2) - F.f t (x 1)) +
        r * (F.f t (x 6) - F.f t (x 1)) := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]

/-- Orientation: `ρ κ < 0` for the 4-rim `(0,1,2,5)`, `κ = det3 (x2-x0) (x5-x1) (x0-x1)`. -/
theorem rho_kappa (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (hN0 : ⟪F.N 0, u⟫ < 0)
    (h : 0 < ρ * det3 (x 2 - x 1) (x 0 - x 1) u) :
    ρ * det3 (x 2 - x 0) (x 5 - x 1) (x 0 - x 1) < 0 := by
  have hΩ := omega_ne_zero F
  obtain ⟨a, b, c, hu⟩ := Q45.exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) u hΩ
  obtain ⟨p, q, r, h5⟩ := Q45.exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 5 - x 1) hΩ
  have f6 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f5 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
  have z0 := F.zero 0 0 (by decide); have z1 := F.zero 0 1 (by decide); have z2 := F.zero 0 2 (by decide)
  have hc : 0 < c := by
    have e : ⟪F.N 0, u⟫ = c * F.f 0 (x 6) := by
      rw [hu, pair3', z0, z1, z2]; ring
    rw [e] at hN0
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f6.le]
  have hr : 0 < r := by
    have e : F.f 0 (x 5) = r * F.f 0 (x 6) := by
      have := F.inner_sub 0 5 1
      rw [h5, pair3', z0, z1, z2] at this
      linarith
    rw [e] at f5
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f6.le]
  have h5' : x 5 = x 1 + (p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)) := by
    rw [← h5]; abel
  have eκ : det3 (x 2 - x 0) (x 5 - x 1) (x 0 - x 1) = r * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    rw [h5']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have eu : det3 (x 2 - x 1) (x 0 - x 1) u = -c * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    rw [hu]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [eu] at h
  rw [eκ]
  have : ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hc.le hn]
  nlinarith [mul_pos hr hr]

theorem sigma_range (x0 x1 x2 x5 xq u : ℝ³) (ρ σ δ : ℝ) (hq : xq = x0 + σ • (x5 - x0) + δ • u)
    (h1 : 0 < ρ * det3 (x1 - x0) (x5 - x0) u) (h2 : 0 < ρ * det3 (x5 - x2) (x0 - x2) u)
    (t1 : 0 < ρ * det3 (x1 - x0) (xq - x0) u) (t2 : 0 < ρ * det3 (x5 - x2) (xq - x2) u) :
    0 < σ ∧ σ < 1 := by
  have e1 : ρ * det3 (x1 - x0) (xq - x0) u = σ * (ρ * det3 (x1 - x0) (x5 - x0) u) := by
    subst hq
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have e2 : ρ * det3 (x5 - x2) (xq - x2) u = (1 - σ) * (ρ * det3 (x5 - x2) (x0 - x2) u) := by
    subst hq
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [e1] at t1; rw [e2] at t2
  constructor
  · exact pos_of_mul_pos_left t1 h1.le
  · have := pos_of_mul_pos_left t2 h2.le
    linarith

lemma ext_vertices (q : Fin 7) (hqS : q ∉ s0x_S24 3) (hqr : ∀ j : ZMod 4, q ≠ quad (0 : Fin 7) 1 2 5 j) :
    q = 6 := by
  revert q; decide

lemma mid_vertices (q : Fin 7) (hqS : q ∈ s0x_S24 3) (hqr : ∀ j : ZMod 4, q ≠ quad (0 : Fin 7) 1 2 5 j) :
    q = 3 ∨ q = 4 := by
  revert q; decide

lemma quad_eq_r : ∀ i : ZMod 4, x (quad (0 : Fin 7) 1 2 5 i) = quad (x 0) (x 1) (x 2) (x 5) i := by
  intro i; fin_cases i <;> rfl

/-- The 4-rim `(0,1,2,5)` on the circle of 0345 at a view with `N3 u = 0`,
`N0, N2 < 0 < N1, N5, N6`. -/
theorem quadRim0125 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0) (hN0 : ⟪F.N 0, u⟫ < 0) (hN1 : 0 < ⟪F.N 1, u⟫)
    (hN2 : ⟪F.N 2, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) (hN6 : 0 < ⟪F.N 6, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ρ * det3 (x 2 - x 0) (x 5 - x 1) (x 0 - x 1) < 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 0) (x 1) (x 2) (x 5) (i + 1) - quad (x 0) (x 1) (x 2) (x 5) i)
          (quad (x 0) (x 1) (x 2) (x 5) j - quad (x 0) (x 1) (x 2) (x 5) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 1) (x 2) (x 5) (i + 1) - quad (x 0) (x 1) (x 2) (x 5) i)
          (x 6 - quad (x 0) (x 1) (x 2) (x 5) i) u) ∧
      (∀ y : Fin 7, y ∉ s0x_S24 0 → y ∉ s0x_S24 2 →
        0 < ρ * det3 (x 1 - x 0) (x y - x 0) u ∧ 0 < ρ * det3 (x 5 - x 2) (x y - x 2) u) := by
  have hne_01 := cross_ne_zero_of_facet_sign F 0 0 1 (by decide) (by decide) hN0.ne 2 (by decide) (by decide)
  have hne_12 := cross_ne_zero_of_facet_sign F 0 1 2 (by decide) (by decide) hN0.ne 1 (by decide) (by decide)
  have hne_25 := cross_ne_zero_of_facet_sign F 2 2 5 (by decide) (by decide) hN2.ne 5 (by decide) (by decide)
  have hne_50 := cross_ne_zero_of_facet_sign F 2 5 0 (by decide) (by decide) hN2.ne 6 (by decide) (by decide)
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F 0 1 0 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN1⟩ hne_01
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_ridge F 0 5 1 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN5⟩ hne_12
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F 2 6 2 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN2, hN6⟩ hne_25
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_edgeOn F 3 5 0 (by decide) (by decide) u hN3 hne_50
  have c01 : det3 (x 1 - x 0) (x 2 - x 0) u = det3 (x 2 - x 1) (x 0 - x 1) u :=
    RimFromSigns.det3_cycle_triangle (x 0) (x 1) (x 2) u
  have c12 : det3 (x 2 - x 1) (x 5 - x 1) u = det3 (x 5 - x 2) (x 1 - x 2) u :=
    RimFromSigns.det3_cycle_triangle (x 1) (x 2) (x 5) u
  have c23 : det3 (x 5 - x 2) (x 0 - x 2) u = det3 (x 0 - x 5) (x 2 - x 5) u :=
    RimFromSigns.det3_cycle_triangle (x 2) (x 5) (x 0) u
  have h0_2 : 0 < σ₀ * det3 (x 1 - x 0) (x 2 - x 0) u := hσ₀ 2 (by decide)
  have h1_0 : 0 < σ₁ * det3 (x 2 - x 1) (x 0 - x 1) u := hσ₁ 0 (by decide)
  have h1_0' : 0 < σ₁ * det3 (x 1 - x 0) (x 2 - x 0) u := by rw [c01]; exact h1_0
  have hσ01 : 0 < σ₀ * σ₁ := sign_prod h0_2 h1_0'
  have h1_5 : 0 < σ₁ * det3 (x 2 - x 1) (x 5 - x 1) u := hσ₁ 5 (by decide)
  have h2_1 : 0 < σ₂ * det3 (x 5 - x 2) (x 1 - x 2) u := hσ₂ 1 (by decide)
  have h2_1' : 0 < σ₂ * det3 (x 2 - x 1) (x 5 - x 1) u := by rw [c12]; exact h2_1
  have hσ12 : 0 < σ₁ * σ₂ := sign_prod h1_5 h2_1'
  have h2_0 : 0 < σ₂ * det3 (x 5 - x 2) (x 0 - x 2) u := hσ₂ 0 (by decide)
  have h3_2 : 0 < σ₃ * det3 (x 0 - x 5) (x 2 - x 5) u := hσ₃ 2 (by decide)
  have h3_2' : 0 < σ₃ * det3 (x 5 - x 2) (x 0 - x 2) u := by rw [c23]; exact h3_2
  have hσ23 : 0 < σ₂ * σ₃ := sign_prod h2_0 h3_2'
  have hσ02 : 0 < σ₀ * σ₂ := sign_transfer hσ01 hσ12
  have hσ03 : 0 < σ₀ * σ₃ := sign_transfer hσ02 hσ23
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < σ₀ * det3 (quad (x 0) (x 1) (x 2) (x 5) (i + 1) - quad (x 0) (x 1) (x 2) (x 5) i)
          (quad (x 0) (x 1) (x 2) (x 5) j - quad (x 0) (x 1) (x 2) (x 5) i) u := by
    intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_2
    · exact hσ₀ 5 (by decide)
    · exact sign_transfer hσ01 (hσ₁ 0 (by decide))
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ01 h1_5
    · exact sign_transfer hσ02 h2_0
    · exact sign_transfer hσ02 (hσ₂ 1 (by decide))
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ03 (hσ₃ 1 (by decide))
    · exact sign_transfer hσ03 h3_2
    · exact False.elim (hj1 rfl)
  refine ⟨σ₀, hσ₀_ne, ?_, hcyc, ?_, ?_⟩
  · refine rho_kappa F hN0 ?_
    have := hcyc 1 0 (by decide) (by decide)
    exact this
  · intro i
    fin_cases i
    · exact hσ₀ 6 (by decide)
    · exact sign_transfer hσ01 (hσ₁ 6 (by decide))
    · exact sign_transfer hσ02 (hσ₂ 6 (by decide))
    · exact sign_transfer hσ03 (hσ₃ 6 (by decide))
  · intro y hy0 hy2
    exact ⟨hσ₀ y (Or.inl hy0), sign_transfer hσ02 (hσ₂ y (Or.inl hy2))⟩


private theorem ev_neg (N b d : ℝ³) (h : ⟪N, b⟫ < 0) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪N, b + ε • d⟫ < 0 := by
  have := eventually_pos_affine (A := -⟪N, b⟫) (B := -⟪N, d⟫) (Or.inl (by linarith))
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

private theorem ev_pos (N b d : ℝ³) (h : 0 < ⟪N, b⟫) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪N, b + ε • d⟫ := by
  have := eventually_pos_affine (A := ⟪N, b⟫) (B := ⟪N, d⟫) (Or.inl h)
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; exact hε

theorem u_eq (F : S0xFac 9 s0x_S24 x) (ε : ℝ) :
    u31 F + ε • (x 0 - x 5) = (F.f 1 (x 4) - ε) • (x 5 - x 0) + (-F.f 1 (x 5)) • (x 4 - x 0) := by
  unfold u31; module

/-- **H31 hinge leaf** (facet 0345, view `u31 - ε e5`, rim `(0,1,2,5)`, chord `5 -> 0`, middles 3, 4,
vertex 6 inside). Case conditions are the four facet signs at `u31` and the depth condition. -/
theorem q45_h31 (F : S0xFac 9 s0x_S24 x)
    (hN0 : ⟪F.N 0, u31 F⟫ < 0) (hN2 : ⟪F.N 2, u31 F⟫ < 0)
    (hN5 : 0 < ⟪F.N 5, u31 F⟫) (hN6 : 0 < ⟪F.N 6, u31 F⟫)
    (hbase : min ⟪x 1, u31 F⟫ ⟪x 5, u31 F⟫ < max ⟪x 0, u31 F⟫ ⟪x 2, u31 F⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 1) (x 2) (x 5) i - quad (x 0) (x 1) (x 2) (x 5) j, u31 F⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 1) (x 2) (x 5) i - quad (x 0) (x 1) (x 2) (x 5) j, x 0 - x 5⟫ ≠ 0)
    (w : ZMod 4) (hw : w = 1 ∨ w = 2)
    (hfar : ∀ m : ZMod 4, m ≠ w → quad (0 : Fin 7) 1 2 5 m ∉ s0x_S24 3 →
      F.f 3 (x (quad (0 : Fin 7) 1 2 5 w)) < F.f 3 (x (quad (0 : Fin 7) 1 2 5 m)))
    (hoff : ⟪F.N 3, cross (x 0 - x 5) (x (quad (0 : Fin 7) 1 2 5 w) - x 5)⟫ ≠ 0 ∨
      ⟪x (quad (0 : Fin 7) 1 2 5 w) - x 5, x 0 - x 5⟫ < 0 ∨
      ⟪x (quad (0 : Fin 7) 1 2 5 w) - x 0, x 5 - x 0⟫ < 0) :
    FaceChordView F 3 := by
  set p : ZMod 4 → ℝ³ := quad (x 0) (x 1) (x 2) (x 5) with hp
  set b := u31 F with hb
  set c := x 0 - x 5 with hc
  set κ := det3 (x 2 - x 0) (x 5 - x 1) (x 0 - x 1) with hκ
  have f1_5 : F.f 1 (x 5) < 0 := F.neg 1 5 (by decide)
  have f1_4 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
  have hb3 : ⟪F.N 3, b⟫ = 0 := by
    rw [hb, inner_u31, F.zero 3 5 (by decide), F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  have hc3 : ⟪F.N 3, c⟫ = 0 := by
    rw [hc, F.inner_sub, F.zero 3 5 (by decide), F.zero 3 0 (by decide)]; ring
  have hb1 : ⟪F.N 1, b⟫ = 0 := by
    rw [hb, inner_u31, F.zero 1 0 (by decide)]; ring
  have hc1 : 0 < ⟪F.N 1, c⟫ := by
    rw [hc, F.inner_sub, F.zero 1 0 (by decide)]; linarith
  have x3 : ∀ ε : ℝ, ⟪F.N 3, b + ε • c⟫ = 0 := by
    intro ε; rw [inner_add_right, real_inner_smul_right, hb3, hc3]; ring
  have x1 : ∀ ε : ℝ, 0 < ε → 0 < ⟪F.N 1, b + ε • c⟫ := by
    intro ε hε; rw [inner_add_right, real_inner_smul_right, hb1]; nlinarith
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have e0 := ev_neg (F.N 0) b c hN0
  have e2 := ev_neg (F.N 2) b c hN2
  have e5 := ev_pos (F.N 5) b c hN5
  have e6 := ev_pos (F.N 6) b c hN6
  have hκ0 : κ ≠ 0 := by
    intro h0
    obtain ⟨ε, h0', h2', h5', h6', hε⟩ := (e0.and (e2.and (e5.and (e6.and ev0)))).exists
    obtain ⟨ρ, hρ, hρκ, -⟩ := quadRim0125 F (x3 ε) h0' (x1 ε hε) h2' h5' h6'
    change ρ * κ < 0 at hρκ
    rw [h0, mul_zero] at hρκ; exact lt_irrefl _ hρκ
  have hk : (-κ) * κ < 0 := by nlinarith [sq_pos_of_ne_zero hκ0]
  have hcyc_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < (-κ) * triD p (b + ε • c) i := by
    filter_upwards [e0, e2, e5, e6, ev0] with ε h0' h2' h5' h6' hε
    obtain ⟨ρ, hρ, hρκ, hcyc, -⟩ := quadRim0125 F (x3 ε) h0' (x1 ε hε) h2' h5' h6'
    change ρ * κ < 0 at hρκ
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
    have hT : 0 < (-(ρ * κ)) * (ρ * triD p (b + ε • c) i) := mul_pos (by linarith) h
    have e : (-(ρ * κ)) * (ρ * triD p (b + ε • c) i) = ρ ^ 2 * ((-κ) * triD p (b + ε • c) i) := by ring
    rw [e] at hT
    exact pos_of_mul_pos_right hT (sq_nonneg ρ)
  have hgen' : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, c⟫ ≠ 0 := hgen
  have hU := cornerU p b c (-κ) hcyc_ev hk hbase hgen'
  obtain ⟨ε, h0', h2', h5', h6', hε, hinjU⟩ := (e0.and (e2.and (e5.and (e6.and (ev0.and hU))))).exists
  set u := b + ε • c with hu
  obtain ⟨ρ, hρ, hρκ, hcyc, hin6, hm⟩ := quadRim0125 F (x3 ε) h0' (x1 ε hε) h2' h5' h6'
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) hinjU.2
  set r : ZMod 4 → Fin 7 := quad (0 : Fin 7) 1 2 5 with hr
  have hrx : ∀ i, x (r i) = p i := quad_eq_r
  have hB : 0 < -F.f 1 (x 5) := by linarith
  have hu' : u = (F.f 1 (x 4) - ε) • (x 5 - x 0) + (-F.f 1 (x 5)) • (x 4 - x 0) := u_eq F ε
  have h1 : 0 < ρ * det3 (x 1 - x 0) (x 5 - x 0) u := hcyc 0 3 (by decide) (by decide)
  have h2 : 0 < ρ * det3 (x 5 - x 2) (x 0 - x 2) u := hcyc 2 0 (by decide) (by decide)
  have mid : ∀ (σ δ : ℝ) (q : Fin 7), q ∉ s0x_S24 0 → q ∉ s0x_S24 2 →
      x q = x 0 + σ • (x 5 - x 0) + δ • u → δ ≠ 0 →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x q = x 5 + s • (x 0 - x 5) + δ • u := by
    intro σ δ q hq0 hq2 hxq hδ
    obtain ⟨t1, t2⟩ := hm q hq0 hq2
    obtain ⟨hs0, hs1⟩ := sigma_range (x 0) (x 1) (x 2) (x 5) (x q) u ρ σ δ hxq h1 h2 t1 t2
    refine ⟨1 - σ, δ, by linarith, by linarith, hδ, ?_⟩
    rw [hxq]; ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hne5 : F.f 1 (x 5) ≠ 0 := f1_5.ne
  obtain ⟨al, be, hal, hbe, -, h3⟩ := Minimality.T24.Par.par2546_quad F
  refine ⟨u, 4, inferInstance, r, 3, w, ρ, x3 ε, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quad (0 : Fin 7) 1 2 5 3 ∈ s0x_S24 3; decide
  · show quad (0 : Fin 7) 1 2 5 (3 + 1) ∈ s0x_S24 3; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    have := ext_vertices q hqS hqr
    subst this
    exact hin6 i
  · intro q hqS hqr
    have hq := mid_vertices q hqS hqr
    rcases hq with rfl | rfl
    · refine mid (al + be * (-(F.f 1 (x 4) - ε)) / (-F.f 1 (x 5))) (be / (-F.f 1 (x 5))) 3
        (by decide) (by decide) ?_ (div_ne_zero hbe.ne' hB.ne')
      have : x 3 = x 0 + (al • (x 5 - x 0) + be • (x 4 - x 0)) := by rw [← h3]; abel
      rw [this, hu']
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    · refine mid (-(F.f 1 (x 4) - ε) / (-F.f 1 (x 5))) (1 / (-F.f 1 (x 5))) 4
        (by decide) (by decide) ?_ (div_ne_zero one_ne_zero hB.ne')
      rw [hu']
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
  · simp_rw [hrx]; exact hinjU.1
  · simp_rw [hrx]; exact Or.inl h_uni
  · rcases hw with rfl | rfl <;> (show _ ∉ s0x_S24 3; decide)
  · exact hfar
  · exact hoff

end Minimality.T24.H31
