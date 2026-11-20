module

public import Minimality.Sym24
public import Minimality.RF0345

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012 Minimality.T24.R046

namespace Minimality.T24.RX27

variable {x : Fin 7 → ℝ³}

/-- Rim `(3, 6, 0, 5)` of the view on the `046` circle with `236` back, `346` and `0345` front. -/
theorem quadRim_x27 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN4 : ⟪F.N 4, u⟫ = 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN8 : 0 < ⟪F.N 8, u⟫)
    (hN2 : ⟪F.N 2, u⟫ < 0) (hN3 : 0 < ⟪F.N 3, u⟫)
    (hN6 : ⟪F.N 6, u⟫ < 0) (hN1 : ⟪F.N 1, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 3) (x 6) (x 0) (x 5) (i + 1) - quad (x 3) (x 6) (x 0) (x 5) i)
          (quad (x 3) (x 6) (x 0) (x 5) j - quad (x 3) (x 6) (x 0) (x 5) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 3) (x 6) (x 0) (x 5) (i + 1) - quad (x 3) (x 6) (x 0) (x 5) i)
          (x 1 - quad (x 3) (x 6) (x 0) (x 5) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 3) (x 6) (x 0) (x 5) (i + 1) - quad (x 3) (x 6) (x 0) (x 5) i)
          (x 2 - quad (x 3) (x 6) (x 0) (x 5) i) u) := by
  have hne_PA := cross_ne_zero_of_facet_sign F 8 3 6 (by decide) (by decide) hN8.ne' 3 (by decide) (by decide)
  have hne_AB := cross_ne_zero_of_facet_sign F 1 6 0 (by decide) (by decide) hN1.ne 5 (by decide) (by decide)
  have hne_BQ := cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) hN2.ne 0 (by decide) (by decide)
  have hne_QP := cross_ne_zero_of_facet_sign F 6 5 3 (by decide) (by decide) hN6.ne 2 (by decide) (by decide)
  obtain ⟨ρ, hρ_ne, hcvx, hint⟩ := quadRim_of_signs_gen F 3 6 0 5 7 8 4 2 3 6 3
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    hne_PA hne_AB hne_BQ hne_QP ⟨hN7, hN8⟩ hN4 ⟨hN2, hN3⟩ ⟨hN6, hN3⟩
  exact ⟨ρ, hρ_ne, hcvx,
    hint 1 (by decide) (by decide) (by decide) (by decide),
    hint 2 (by decide) (by decide) (by decide) (by decide)⟩

lemma ext_vertices' (q : Fin 7) (hqS : q ∉ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (3 : Fin 7) 6 0 5 j) :
    q = 1 ∨ q = 2 := by
  revert q; decide

lemma mid_vertices' (q : Fin 7) (hqS : q ∈ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (3 : Fin 7) 6 0 5 j) :
    q = 4 := by
  revert q; decide

lemma far_cand' (m : ZMod 4) (hm : m ≠ 0) (hmS : quad (3 : Fin 7) 6 0 5 m ∉ s0x_S24 4) : m = 3 := by
  revert m; decide

lemma far_cand3' (m : ZMod 4) (hm : m ≠ 3) (hmS : quad (3 : Fin 7) 6 0 5 m ∉ s0x_S24 4) : m = 0 := by
  revert m; decide

lemma w5_notS' : quad (3 : Fin 7) 6 0 5 3 ∉ s0x_S24 4 := by decide
lemma w3_notS' : quad (3 : Fin 7) 6 0 5 0 ∉ s0x_S24 4 := by decide

lemma quad_eq_r' : ∀ i : ZMod 4, x (quad (3 : Fin 7) 6 0 5 i) = quad (x 3) (x 6) (x 0) (x 5) i := by
  intro i; fin_cases i <;> rfl

theorem view_inner' (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (ε : ℝ) :
    ⟪F.N t, u47 F + ε • (x 0 - x 6)⟫ = ⟪F.N t, u47 F⟫ + ε * (F.f t (x 0) - F.f t (x 6)) := by
  rw [inner_add_right, real_inner_smul_right, F.inner_sub]

/-- Cross-046 on the opposite side of the circle: the view `u47 - ε (x6 - x0)` (the mirror of the
`X:u27-` menu view). The silhouette is the rim `(3, 6, 0, 5)` (`346`, `0345` front; `236`, `025`,
`235`, `016` back), the middle `4` lies over `6 -> 0`. Replaces `⟪N6, u47⟫ > 0` of
`ropen_cross_core_beta` by `⟪N6, u47⟫ < 0`, and `⟪N2, u47⟫ ≤ 0` by `< 0`. -/
theorem rx27_cross_neg (F : S0xFac 9 s0x_S24 x)
    (hβ : 0 < F.f 7 (x 4) - F.f 7 (x 0))
    (hC5 : ⟪F.N 5, u47 F⟫ < 0) (hC2 : ⟪F.N 2, u47 F⟫ < 0) (hC6 : ⟪F.N 6, u47 F⟫ < 0)
    (hb1 : min ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫ < max ⟪x 3, u47 F⟫ ⟪x 0, u47 F⟫)
    (hb2 : min ⟪x 3, u47 F⟫ ⟪x 0, u47 F⟫ < max ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫)
    (hfar : (F.f 4 (x 3) < F.f 4 (x 5) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
        ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 3 - x 0, x 6 - x 0⟫ < 0)) ∨
      (F.f 4 (x 5) < F.f 4 (x 3) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 3) (x 6) (x 0) (x 5) i - quad (x 3) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
      ⟪quad (x 3) (x 6) (x 0) (x 5) i - quad (x 3) (x 6) (x 0) (x 5) j, x 0 - x 6⟫ ≠ 0) :
    FaceChordView F 4 := by
  set p : ZMod 4 → ℝ³ := quad (x 3) (x 6) (x 0) (x 5) with hp
  have hα : 0 < -F.f 7 (x 4) := by linarith [F.neg 7 4 (by decide : (4 : Fin 7) ∉ s0x_S24 7)]
  have f30 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f34 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have f36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have f80 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f84 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have f86 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
  have f50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have f56 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have f20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have f26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
  have f70 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  have f76 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have f10 : F.f 1 (x 0) = 0 := F.zero 1 0 (by decide)
  have f16 : F.f 1 (x 6) = 0 := F.zero 1 6 (by decide)
  have f40 : F.f 4 (x 0) = 0 := F.zero 4 0 (by decide)
  have f46 : F.f 4 (x 6) = 0 := F.zero 4 6 (by decide)
  have n3 : 0 < ⟪F.N 3, u47 F⟫ := by
    rw [inner_u47, f34, f30]; nlinarith
  have n8 : 0 < ⟪F.N 8, u47 F⟫ := by
    rw [inner_u47, f84, f86]; nlinarith
  have n1 := inner_N1_u47_neg F
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, u47 F + ε • (x 0 - x 6)⟫ < 0 := by
    have := eventually_pos_affine (A := -⟪F.N 5, u47 F⟫) (B := -F.f 5 (x 0)) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [view_inner', f56]; linarith
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 2, u47 F + ε • (x 0 - x 6)⟫ < 0 := by
    have := eventually_pos_affine (A := -⟪F.N 2, u47 F⟫) (B := F.f 2 (x 6)) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [view_inner', f20]; linarith
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 6, u47 F + ε • (x 0 - x 6)⟫ < 0 := by
    have := eventually_pos_affine (A := -⟪F.N 6, u47 F⟫) (B := -(F.f 6 (x 0) - F.f 6 (x 6))) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [view_inner']; linarith
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, u47 F + ε • (x 0 - x 6)⟫ := by
    have := eventually_pos_affine (A := ⟪F.N 8, u47 F⟫) (B := F.f 8 (x 0) - F.f 8 (x 6)) (Or.inl n8)
    filter_upwards [this] with ε hε
    rw [view_inner']; linarith
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, u47 F + ε • (x 0 - x 6)⟫ := by
    have := eventually_pos_affine (A := ⟪F.N 3, u47 F⟫) (B := F.f 3 (x 0) - F.f 3 (x 6)) (Or.inl n3)
    filter_upwards [this] with ε hε
    rw [view_inner']; linarith
  have eα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (-F.f 7 (x 4)) - ε := by
    have := eventually_pos_affine (A := -F.f 7 (x 4)) (B := -1) (Or.inl hα)
    filter_upwards [this] with ε hε
    linarith
  have hrim : ∀ ε : ℝ, 0 < ε → ⟪F.N 5, u47 F + ε • (x 0 - x 6)⟫ < 0 →
      ⟪F.N 2, u47 F + ε • (x 0 - x 6)⟫ < 0 → ⟪F.N 6, u47 F + ε • (x 0 - x 6)⟫ < 0 →
      0 < ⟪F.N 8, u47 F + ε • (x 0 - x 6)⟫ → 0 < ⟪F.N 3, u47 F + ε • (x 0 - x 6)⟫ →
      ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (p (i + 1) - p i) (p j - p i) (u47 F + ε • (x 0 - x 6))) ∧
      (∀ i : ZMod 4, 0 < ρ * det3 (p (i + 1) - p i) (x 1 - p i) (u47 F + ε • (x 0 - x 6))) ∧
      (∀ i : ZMod 4, 0 < ρ * det3 (p (i + 1) - p i) (x 2 - p i) (u47 F + ε • (x 0 - x 6))) := by
    intro ε hε _ h2 h6 h8 h3
    refine quadRim_x27 F ?_ ?_ h8 h2 h3 h6 ?_
    · rw [view_inner', inner_N4_u47, f40, f46]; ring
    · rw [view_inner', inner_N7_u47, f76]; nlinarith
    · rw [view_inner']; rw [f10, f16]; linarith
  have hU : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, u47 F + ε • (x 0 - x 6)⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, u47 F + ε • (x 0 - x 6)⟫) := by
    have hinj := eventually_injective_quad p (u47 F) (x 0 - x 6) hgen
    have h1 := eventually_min13_lt_max02 p (u47 F) (x 0 - x 6) (by simpa [hp, quad] using hb1)
    have h2 := eventually_min02_lt_max13 p (u47 F) (x 0 - x 6) (by simpa [hp, quad] using hb2)
    filter_upwards [hinj, h1, h2] with ε hi a b
    exact ⟨hi, Minimality.RimCell.isCyclicUnimodal_four _ hi
      (hn_of_min_lt_max (z := fun i => ⟪p i, u47 F + ε • (x 0 - x 6)⟫) b)
      (hp_of_min_lt_max (z := fun i => ⟪p i, u47 F + ε • (x 0 - x 6)⟫) a)⟩
  obtain ⟨ε, h5, h2, h6, h8, h3, hεα, hε, hinjU⟩ :=
    (e5.and (e2.and (e6.and (e8.and (e3.and (eα.and (ev0.and hU))))))).exists
  have hε' : 0 < ε := hε
  set u := u47 F + ε • (x 0 - x 6) with hu
  obtain ⟨ρ, hρ, hcyc, hin1, hin2⟩ := hrim ε hε' h5 h2 h6 h8 h3
  have h4 : ⟪F.N 4, u⟫ = 0 := by rw [hu, view_inner', inner_N4_u47, f40, f46]; ring
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) hinjU.2
  set r : ZMod 4 → Fin 7 := quad (3 : Fin 7) 6 0 5 with hr
  have hrx : ∀ i, x (r i) = p i := quad_eq_r'
  set κ := (-F.f 7 (x 4)) + (F.f 7 (x 4) - F.f 7 (x 0)) with hκdef
  have hκ : 0 < κ := by linarith
  obtain ⟨w, hwS, hfarw, hoffw⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 4 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 4 → F.f 4 (x (r w)) < F.f 4 (x (r m))) ∧
      (⟪F.N 4, cross (x (r (1 + 1)) - x (r 1)) (x (r w) - x (r 1))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 1), x (r (1 + 1)) - x (r 1)⟫ < 0 ∨
        ⟪x (r w) - x (r (1 + 1)), x (r 1) - x (r (1 + 1))⟫ < 0) := by
    rcases hfar with ⟨hf, ho⟩ | ⟨hf, ho⟩
    · refine ⟨0, w3_notS', ?_, ho⟩
      intro m hm hmS
      have := far_cand' m hm hmS
      subst this
      exact hf
    · refine ⟨3, w5_notS', ?_, ho⟩
      intro m hm hmS
      have := far_cand3' m hm hmS
      subst this
      exact hf
  refine ⟨u, 4, inferInstance, r, 1, w, ρ, h4, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, hwS, hfarw, hoffw⟩
  · show quad (3 : Fin 7) 6 0 5 1 ∈ s0x_S24 4; decide
  · show quad (3 : Fin 7) 6 0 5 (1 + 1) ∈ s0x_S24 4; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    rcases ext_vertices' q hqS hqr with rfl | rfl
    · exact hin1 i
    · exact hin2 i
  · intro q hqS hqr
    have hq4 := mid_vertices' q hqS hqr
    subst hq4
    have hra : x (r 1) = x 6 := rfl
    have hra1 : x (r (1 + 1)) = x 0 := rfl
    rw [hra, hra1]
    have hκ' : (-F.f 7 (x 4) - ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) + ε) ≠ 0 := by
      have : (-F.f 7 (x 4) - ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) + ε) = κ := by rw [hκdef]; ring
      rw [this]; exact hκ.ne'
    have hme := middle_eq (x 4) (x 0) (x 6) (-F.f 7 (x 4) - ε) ((F.f 7 (x 4) - F.f 7 (x 0)) + ε) hκ'
    have hsum : (-F.f 7 (x 4) - ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) + ε) = κ := by rw [hκdef]; ring
    have hV : u = (-F.f 7 (x 4) - ε) • (x 4 - x 0) + ((F.f 7 (x 4) - F.f 7 (x 0)) + ε) • (x 4 - x 6) := by
      rw [hu]; unfold u47
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    refine ⟨(-F.f 7 (x 4) - ε) / κ, 1 / κ, ?_, ?_, by positivity, ?_⟩
    · apply div_pos <;> linarith
    · rw [div_lt_one hκ]; linarith
    · rw [hV]; rw [hsum] at hme; exact hme
  · simp_rw [hrx]; exact hinjU.1
  · simp_rw [hrx]; exact Or.inl h_uni

/-- Case conditions of `rx27_cross_neg`. -/
def Case_crossN (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < F.f 7 (x 4) - F.f 7 (x 0) ∧
  ⟪F.N 5, u47 F⟫ < 0 ∧ ⟪F.N 2, u47 F⟫ < 0 ∧ ⟪F.N 6, u47 F⟫ < 0 ∧
  min ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫ < max ⟪x 3, u47 F⟫ ⟪x 0, u47 F⟫ ∧
  min ⟪x 3, u47 F⟫ ⟪x 0, u47 F⟫ < max ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫

/-- Genericity conditions of `rx27_cross_neg`. -/
def Gen_crossN (F : S0xFac 9 s0x_S24 x) : Prop :=
  ((F.f 4 (x 3) < F.f 4 (x 5) ∧
    (⟪F.N 4, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
      ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 3 - x 0, x 6 - x 0⟫ < 0)) ∨
    (F.f 4 (x 5) < F.f 4 (x 3) ∧
    (⟪F.N 4, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
      ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0))) ∧
  ∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 3) (x 6) (x 0) (x 5) i - quad (x 3) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
    ⟪quad (x 3) (x 6) (x 0) (x 5) i - quad (x 3) (x 6) (x 0) (x 5) j, x 0 - x 6⟫ ≠ 0

/-- Hypothesis bundle for `rx27_cross_neg`. -/
def H_crossN (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossN F ∧ Gen_crossN F

theorem leaf_crossN {F : S0xFac 9 s0x_S24 x} (h : H_crossN F) : FaceChordView F 4 :=
  rx27_cross_neg F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2 h.2.1 h.2.2

/-- Mirror bundle (`x ∘ π`): the `X:u27-` view on the `025` circle. -/
def Case_crossN_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossN (Minimality.T24.Sym.sym24 F)
def Gen_crossN_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossN (Minimality.T24.Sym.sym24 F)
/-- Mirror hypothesis bundle for `Sym24` of `rx27_cross_neg`. -/
def H_crossN_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossN_sym F ∧ Gen_crossN_sym F

theorem leaf_crossN_sym {F : S0xFac 9 s0x_S24 x} (h : H_crossN_sym F) : FaceChordView F 2 :=
  Minimality.T24.Sym.faceChordView_sym F (t := 4) (leaf_crossN h)

/-! ### Root of facet `046` on the `012` circle, `+` side (mirror: `s:f025+`) -/

theorem rx27_inner_N4 (F : S0xFac 9 s0x_S24 x) (t : ℝ) :
    ⟪F.N 4, u0 x t⟫ = ⟪F.N 4, x 0 - x 1⟫ + t * ⟪F.N 4, x 2 - x 1⟫ := by
  simp only [u0, inner_add_right, real_inner_smul_right]

/-- Root `t4 = 1/ω4` of `046` on the `012` circle: for `0 < t4`, `N4` vanishes there and decreases. -/
theorem rx27_t4 (F : S0xFac 9 s0x_S24 x) (h : 0 < inv_omega4_012 F) :
    ⟪F.N 4, u0 x (inv_omega4_012 F)⟫ = 0 ∧ ⟪F.N 4, x 2 - x 1⟫ < 0 := by
  have hl := lambda4_pos F
  have h0 := inner_N4_e0 F
  have hs : ⟪F.N 4, x 2 - x 1⟫ < 0 := by
    by_contra hn
    push Not at hn
    have : inv_omega4_012 F ≤ 0 := by
      unfold inv_omega4_012
      rw [h0]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn
    linarith
  refine ⟨?_, hs⟩
  rw [rx27_inner_N4]; unfold inv_omega4_012
  have := hs.ne
  field_simp; ring

/-- Leaf at the root of `046` on the `012` circle, view `u0 (t4 + ε)`: rim `(0, 4, 3, 2)`, `N4 < 0`
after the root. Mirror of the `s:f025+` menu view. -/
theorem rx27_w4_pos (F : S0xFac 9 s0x_S24 x)
    (ht : 0 < inv_omega4_012 F)
    (hN3 : 0 < ⟪F.N 3, u0 x (inv_omega4_012 F)⟫)
    (hN8 : ⟪F.N 8, u0 x (inv_omega4_012 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (inv_omega4_012 F)⟫)
    (hN7 : ⟪F.N 7, u0 x (inv_omega4_012 F)⟫ < 0)
    (hbase : min ⟪x 0, u0 x (inv_omega4_012 F)⟫ ⟪x 3, u0 x (inv_omega4_012 F)⟫ <
      max ⟪x 4, u0 x (inv_omega4_012 F)⟫ ⟪x 2, u0 x (inv_omega4_012 F)⟫)
    (hfar : F.f 0 (x 4) ≠ F.f 0 (x 3))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (inv_omega4_012 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  obtain ⟨hz, hs⟩ := rx27_t4 F ht
  refine leaf_core012 F (inv_omega4_012 F) 1 (Or.inl rfl) ht 4 3 5 6 4 3 8 3 7 6 (by decide)
    (Or.inr (Or.inr (Or.inr rfl))) ?_ (Or.inr ⟨kap2 F, hbase⟩) hgen (hw_of_ne F 4 3 hfar hoff4 hoff3)
  filter_upwards [ev_neg_u0 (F.N 4) _ 1 (Or.inr ⟨hz, by linarith⟩), ev_pos_u0 (F.N 3) _ 1 (Or.inl hN3),
    ev_neg_u0 (F.N 8) _ 1 (Or.inl hN8), ev_pos_u0 (F.N 6) _ 1 (Or.inl hN6),
    ev_neg_u0 (F.N 7) _ 1 (Or.inl hN7)] with ε h4 h3 h8 h6 h7
  exact ⟨⟨h4, h3⟩, ⟨h8, h3⟩, ⟨h7, h6⟩⟩

def Case_w4p (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < inv_omega4_012 F ∧ 0 < ⟪F.N 3, u0 x (inv_omega4_012 F)⟫ ∧
  ⟪F.N 8, u0 x (inv_omega4_012 F)⟫ < 0 ∧ 0 < ⟪F.N 6, u0 x (inv_omega4_012 F)⟫ ∧
  ⟪F.N 7, u0 x (inv_omega4_012 F)⟫ < 0 ∧
  min ⟪x 0, u0 x (inv_omega4_012 F)⟫ ⟪x 3, u0 x (inv_omega4_012 F)⟫ <
    max ⟪x 4, u0 x (inv_omega4_012 F)⟫ ⟪x 2, u0 x (inv_omega4_012 F)⟫

def Gen_w4p (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 4) ≠ F.f 0 (x 3) ∧ (F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4) ∧
  (F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (inv_omega4_012 F)) (x 2 - x 1)

/-- Hypothesis bundle for `rx27_w4_pos`. -/
def H_w4p (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4p F ∧ Gen_w4p F

theorem leaf_w4p {F : S0xFac 9 s0x_S24 x} (h : H_w4p F) : FaceChordView F 0 :=
  rx27_w4_pos F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

def Case_w4p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4p (Minimality.T24.Sym.sym24 F)
def Gen_w4p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_w4p (Minimality.T24.Sym.sym24 F)
/-- Mirror hypothesis bundle for `Sym24` of `rx27_w4_pos`. -/
def H_w4p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4p_sym F ∧ Gen_w4p_sym F

/-- `s:f025+`: the `016` circle at the root of facet `025`. -/
theorem leaf_w4p_sym {F : S0xFac 9 s0x_S24 x} (h : H_w4p_sym F) : FaceChordView F 1 :=
  Minimality.T24.Sym.faceChordView_sym F (t := 0) (leaf_w4p h)

end Minimality.T24.RX27
