module

public import Minimality.R012
public import Minimality.Q45Leaf
public import Minimality.CornerU
public import Minimality.DiagCross
public import Minimality.FaceChordFac
public import Minimality.Type24Corner
public import Minimality.Type24Cap

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R046

/-!
# R046: Carbon's Theorem Cross-046 (`q046_cross`)

Cross-circle implication from `{012, 016}` failing at `ω3` to `FaceChordView F 4`
at `u47 + ε • (x 6 - x 0)` (on the 4-rim `(2, 6, 0, 5)`, middle `4` over `6 -> 0`).
-/

variable {x : Fin 7 → ℝ³}

theorem key_alg (Gaa Gbb Gcc Gab Gac Gbc ω ua ub uc : ℝ)
    (hab : Gab < 0) (hac : Gac < 0) (hbc : Gbc < 0)
    (hCS : Gab ^ 2 < Gaa * Gbb) (hbb : 0 < Gbb)
    (hua : 0 < ua) (hub : 0 < ub) (huc : 0 ≤ uc) (hω : ω * ua = ub + uc)
    (h3 : ω * (Gbb - Gab) ≤ Gaa - Gab) (h4 : ω * (Gcc - Gac) ≤ Gaa - Gac) :
    0 < ua * (Gaa - Gac) + ub * (Gab - Gbc) + uc * (Gac - Gcc) := by
  have hωpos : 0 < ω := by
    have : 0 < ω * ua := by rw [hω]; linarith
    exact pos_of_mul_pos_left this hua.le
  have hD : 0 < Gbb - Gab := by linarith
  have hm := mul_le_mul_of_nonpos_left h3 hab.le
  have h5 : 0 < Gaa + ω * Gab := by
    have : 0 < (Gbb - Gab) * (Gaa + ω * Gab) := by nlinarith
    exact pos_of_mul_pos_right this hD.le
  have hid : ω * (ua * (Gaa - Gac) + ub * (Gab - Gbc) + uc * (Gac - Gcc)) =
      uc * ((Gaa - Gac) - ω * (Gcc - Gac)) + ub * ((Gaa + ω * Gab) - Gac - ω * Gbc) := by
    linear_combination (Gaa - Gac) * hω
  have hpos : 0 < ω * (ua * (Gaa - Gac) + ub * (Gab - Gbc) + uc * (Gac - Gcc)) := by
    rw [hid]
    have t1 : 0 ≤ uc * ((Gaa - Gac) - ω * (Gcc - Gac)) := mul_nonneg huc (by linarith)
    have t2 : 0 < ub * ((Gaa + ω * Gab) - Gac - ω * Gbc) :=
      mul_pos hub (by nlinarith [mul_pos hωpos (neg_pos.mpr hbc)])
    linarith
  exact pos_of_mul_pos_right hpos hωpos.le

theorem lagrange (a b : ℝ³) : ⟪a, b⟫ ^ 2 < ⟪a, a⟫ * ⟪b, b⟫ ∨ cross a b = 0 := by
  by_cases h : cross a b = 0
  · exact Or.inr h
  · left
    have e : ∀ p q : ℝ³, ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
      intro p q
      simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
    have hc : 0 < ⟪cross a b, cross a b⟫ := real_inner_self_pos.mpr h
    have : ⟪cross a b, cross a b⟫ = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ ^ 2 := by
      simp only [e, cross]
      simp
      ring
    linarith

def u1 (x : Fin 7 → ℝ³) (t : ℝ) : ℝ³ := (x 0 - x 1) + t • (x 6 - x 1)

noncomputable def u47 (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (- F.f 7 (x 4)) • (x 4 - x 0) + (F.f 7 (x 4) - F.f 7 (x 0)) • (x 4 - x 6)

theorem inner_comb (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (α β : ℝ) :
    ⟪F.N t, α • (x 4 - x 0) + β • (x 4 - x 6)⟫ =
      α * (F.f t (x 4) - F.f t (x 0)) + β * (F.f t (x 4) - F.f t (x 6)) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]

theorem inner_u47 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u47 F⟫ = (-F.f 7 (x 4)) * (F.f t (x 4) - F.f t (x 0)) +
      (F.f 7 (x 4) - F.f 7 (x 0)) * (F.f t (x 4) - F.f t (x 6)) := inner_comb F t _ _

theorem inner_N4_u47 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 4, u47 F⟫ = 0 := by
  rw [inner_u47, F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; ring

theorem inner_N7_u47 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 7, u47 F⟫ = 0 := by
  rw [inner_u47, F.zero 7 6 (by decide)]; ring

theorem exists_coords (a b c u : ℝ³) (h : det3 a b c ≠ 0) :
    ∃ p q r : ℝ, u = p • a + q • b + r • c := by
  have hv : vol3 a b c ≠ 0 := by
    have : vol3 a b c = det3 a b c := by simp only [det3_expand, vol3]; ring
    rwa [this]
  refine ⟨vol3 u b c / vol3 a b c, vol3 a u c / vol3 a b c, vol3 a b u / vol3 a b c, ?_⟩
  have e : ∀ t : ℝ, vol3 a b c * (t / vol3 a b c) = t := fun t => by field_simp
  refine smul_right_injective _ hv ?_
  simp only
  rw [vol3_smul_cramer, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e, e, e]

theorem pair3 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (p q r : ℝ) :
    ⟪F.N t, p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)⟫ =
      p * (F.f t (x 0) - F.f t (x 1)) + q * (F.f t (x 2) - F.f t (x 1)) +
        r * (F.f t (x 6) - F.f t (x 1)) := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]

theorem exp_diff (ea eb ec : ℝ³) (p q r : ℝ) :
    ⟪ea - ec, p • ea + q • eb + r • ec⟫ = p * (⟪ea, ea⟫ - ⟪ea, ec⟫) +
      q * (⟪ea, eb⟫ - ⟪eb, ec⟫) + r * (⟪ea, ec⟫ - ⟪ec, ec⟫) := by
  have c1 : ⟪eb, ea⟫ = ⟪ea, eb⟫ := real_inner_comm _ _
  have c2 : ⟪ec, ea⟫ = ⟪ea, ec⟫ := real_inner_comm _ _
  have c3 : ⟪ec, eb⟫ = ⟪eb, ec⟫ := real_inner_comm _ _
  simp only [inner_sub_left, inner_add_right, real_inner_smul_right, c2, c3]
  ring

theorem exp_lvl (a b : ℝ³) (ω : ℝ) :
    ⟪a - b, a + ω • b⟫ = ⟪a, a⟫ - ⟪a, b⟫ - ω * (⟪b, b⟫ - ⟪a, b⟫) := by
  have c1 : ⟪b, a⟫ = ⟪a, b⟫ := real_inner_comm _ _
  simp only [inner_sub_left, inner_add_right, real_inner_smul_right, c1]
  ring

theorem base_gt (F : S0xFac 9 s0x_S24 x)
    (hiii : ⟪x 2, u0 x (omega3_012 F)⟫ ≤ ⟪x 0, u0 x (omega3_012 F)⟫)
    (hiv : ⟪x 6, u1 x (omega3_012 F)⟫ ≤ ⟪x 0, u1 x (omega3_012 F)⟫)
    (hob01 : ⟪x 0 - x 1, x 2 - x 1⟫ < 0) (hob02 : ⟪x 0 - x 1, x 6 - x 1⟫ < 0)
    (hob12 : ⟪x 2 - x 1, x 6 - x 1⟫ < 0)
    (hC5 : ⟪F.N 5, u47 F⟫ < 0) (hC0 : ⟪F.N 0, u47 F⟫ ≤ 0) :
    ⟪x 6, u47 F⟫ < ⟪x 0, u47 F⟫ := by
  have hΩ := omega_ne_zero F
  obtain ⟨ua, ub, uc, hu⟩ := exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (u47 F) hΩ
  have hf7 : 0 < -F.f 7 (x 1) := lambda7_pos F
  have hf7x4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have hf7x0 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  have n7 := inner_N7_u47 F
  rw [hu, pair3, F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at n7
  have hom : omega3_012 F * (-F.f 7 (x 1)) = -(F.f 7 (x 0) - F.f 7 (x 1)) := by
    unfold omega3_012
    rw [F.inner_sub, F.inner_sub, F.zero 7 2 (by decide)]
    have : (0 : ℝ) - F.f 7 (x 1) ≠ 0 := by linarith
    field_simp
    ring
  have hωua : omega3_012 F * ua = ub + uc := by
    have : (-F.f 7 (x 1)) * (omega3_012 F * ua - (ub + uc)) = 0 := by
      linear_combination ua * hom - n7
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have n1 : ⟪F.N 1, u47 F⟫ < 0 := by
    rw [inner_u47, F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have := F.neg 1 4 (by decide)
    nlinarith
  have n1' := n1
  rw [hu, pair3, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at n1'
  have hub : 0 < ub := by
    have := F.neg 1 2 (by decide)
    by_contra hn; push Not at hn
    nlinarith
  have n0' := hC0
  rw [hu, pair3, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at n0'
  have huc : 0 ≤ uc := by
    have := F.neg 0 6 (by decide)
    by_contra hn; push Not at hn
    nlinarith
  have n5' := hC5
  rw [hu, pair3, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at n5'
  have hua : 0 < ua := by
    have := F.neg 5 0 (by decide)
    by_contra hn; push Not at hn
    nlinarith
  have c1 : ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := real_inner_comm _ _
  have c2 : ⟪x 6 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
  have c3 : ⟪x 6 - x 1, x 2 - x 1⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
  have hbb : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ := by
    apply real_inner_self_pos.mpr
    intro h0; apply hΩ
    have : x 2 - x 1 = 0 := h0
    simp [det3_expand, this]
  have hCS : ⟪x 0 - x 1, x 2 - x 1⟫ ^ 2 < ⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 2 - x 1, x 2 - x 1⟫ := by
    rcases lagrange (x 0 - x 1) (x 2 - x 1) with h | h
    · exact h
    · exfalso; apply hΩ
      have : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = ⟪cross (x 0 - x 1) (x 2 - x 1), x 6 - x 1⟫ := rfl
      rw [this, h, inner_zero_left]
  have h3 : omega3_012 F * (⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫) ≤
      ⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫ := by
    have h := sub_nonneg.mpr hiii
    rw [← inner_sub_left, show x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) by abel] at h
    have hu0 : u0 x (omega3_012 F) = (x 0 - x 1) + omega3_012 F • (x 2 - x 1) := rfl
    rw [hu0, exp_lvl] at h
    linarith
  have h4 : omega3_012 F * (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫) ≤
      ⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ := by
    have h := sub_nonneg.mpr hiv
    rw [← inner_sub_left, show x 0 - x 6 = (x 0 - x 1) - (x 6 - x 1) by abel] at h
    have hu0 : u1 x (omega3_012 F) = (x 0 - x 1) + omega3_012 F • (x 6 - x 1) := rfl
    rw [hu0, exp_lvl] at h
    linarith
  have hk := key_alg _ _ _ _ _ _ _ ua ub uc hob01 hob02 hob12 hCS hbb hua hub huc hωua h3 h4
  have hd : ⟪x 0, u47 F⟫ - ⟪x 6, u47 F⟫ =
      ua * (⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫) +
      ub * (⟪x 0 - x 1, x 2 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫) +
      uc * (⟪x 0 - x 1, x 6 - x 1⟫ - ⟪x 6 - x 1, x 6 - x 1⟫) := by
    rw [← inner_sub_left, show x 0 - x 6 = (x 0 - x 1) - (x 6 - x 1) by abel, hu, exp_diff]
  linarith

theorem quadRim046 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN4 : ⟪F.N 4, u⟫ = 0)
    (hN5 : ⟪F.N 5, u⟫ < 0) (hN7 : 0 < ⟪F.N 7, u⟫)
    (hN2 : ⟪F.N 2, u⟫ < 0) (hN3 : 0 < ⟪F.N 3, u⟫)
    (hN6 : 0 < ⟪F.N 6, u⟫) (hN1 : ⟪F.N 1, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 2) (x 6) (x 0) (x 5) (i + 1) - quad (x 2) (x 6) (x 0) (x 5) i)
          (quad (x 2) (x 6) (x 0) (x 5) j - quad (x 2) (x 6) (x 0) (x 5) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 2) (x 6) (x 0) (x 5) (i + 1) - quad (x 2) (x 6) (x 0) (x 5) i)
          (x 1 - quad (x 2) (x 6) (x 0) (x 5) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 2) (x 6) (x 0) (x 5) (i + 1) - quad (x 2) (x 6) (x 0) (x 5) i)
          (x 3 - quad (x 2) (x 6) (x 0) (x 5) i) u) := by
  have hne_PA := cross_ne_zero_of_facet_sign F 5 2 6 (by decide) (by decide) hN5.ne 2 (by decide) (by decide)
  have hne_AB := cross_ne_zero_of_facet_sign F 1 6 0 (by decide) (by decide) hN1.ne 8 (by decide) (by decide)
  have hne_BQ := cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) hN2.ne 0 (by decide) (by decide)
  have hne_QP := cross_ne_zero_of_facet_sign F 2 5 2 (by decide) (by decide) hN2.ne 3 (by decide) (by decide)
  obtain ⟨ρ, hρ_ne, hcvx, hint⟩ := quadRim_of_signs_gen F 2 6 0 5 5 7 4 2 3 2 6
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (Or.inl (by decide)) (Or.inl (by decide)) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inl (by decide)) (Or.inr (by decide))
    hne_PA hne_AB hne_BQ hne_QP ⟨hN5, hN7⟩ hN4 ⟨hN2, hN3⟩ ⟨hN2, hN6⟩
  exact ⟨ρ, hρ_ne, hcvx,
    hint 1 (Or.inr (by decide)) (by decide) (Or.inl (by decide)) (Or.inl (by decide)),
    hint 3 (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (Or.inl (by decide))⟩

theorem inner_N1_u47_neg (F : S0xFac 9 s0x_S24 x) : ⟪F.N 1, u47 F⟫ < 0 := by
  have hf7x4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have hf7x0 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  rw [inner_u47, F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
  have := F.neg 1 4 (by decide)
  nlinarith

theorem beta_pos (F : S0xFac 9 s0x_S24 x) (hi : 0 < ⟪F.N 5, x 4 - x 0⟫)
    (hC5 : ⟪F.N 5, u47 F⟫ < 0) : 0 < F.f 7 (x 4) - F.f 7 (x 0) := by
  have hf7x4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  rw [F.inner_sub] at hi
  rw [inner_u47, F.zero 5 6 (by decide)] at hC5
  have := F.neg 5 4 (by decide)
  by_contra hn; push Not at hn
  nlinarith

theorem view_inner (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (ε : ℝ) :
    ⟪F.N t, u47 F + ε • (x 6 - x 0)⟫ = ⟪F.N t, u47 F⟫ + ε * (F.f t (x 6) - F.f t (x 0)) := by
  rw [inner_add_right, real_inner_smul_right, F.inner_sub]

theorem signs_view (F : S0xFac 9 s0x_S24 x) (hC2 : ⟪F.N 2, u47 F⟫ ≤ 0)
    (ε : ℝ) (hε : 0 < ε)
    (hεβ : 0 < (F.f 7 (x 4) - F.f 7 (x 0)) - ε)
    (h5 : ⟪F.N 5, u47 F + ε • (x 6 - x 0)⟫ < 0) (h6 : 0 < ⟪F.N 6, u47 F + ε • (x 6 - x 0)⟫) :
    ⟪F.N 4, u47 F + ε • (x 6 - x 0)⟫ = 0 ∧ ⟪F.N 5, u47 F + ε • (x 6 - x 0)⟫ < 0 ∧
    0 < ⟪F.N 7, u47 F + ε • (x 6 - x 0)⟫ ∧ ⟪F.N 2, u47 F + ε • (x 6 - x 0)⟫ < 0 ∧
    0 < ⟪F.N 3, u47 F + ε • (x 6 - x 0)⟫ ∧ 0 < ⟪F.N 6, u47 F + ε • (x 6 - x 0)⟫ ∧
    ⟪F.N 1, u47 F + ε • (x 6 - x 0)⟫ < 0 := by
  refine ⟨?_, h5, ?_, ?_, ?_, h6, ?_⟩
  · rw [view_inner, inner_N4_u47, F.zero 4 6 (by decide), F.zero 4 0 (by decide)]; ring
  · rw [view_inner, inner_N7_u47, F.zero 7 6 (by decide)]
    have := F.neg 7 0 (by decide)
    nlinarith
  · rw [view_inner]
    have := F.neg 2 6 (by decide)
    rw [F.zero 2 0 (by decide)]
    nlinarith
  · rw [view_inner, inner_u47, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]
    have := F.neg 3 6 (by decide)
    nlinarith
  · rw [view_inner, F.zero 1 6 (by decide), F.zero 1 0 (by decide)]
    have := inner_N1_u47_neg F
    linarith

theorem rho_pos (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ}
    (hin : 0 < ρ * det3 (x 6 - x 2) (x 1 - x 2) u) (hN5 : ⟪F.N 5, u⟫ < 0) :
    0 < ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) :=
  rho_mul_omega_pos_of_inner_neg F u ρ hin hN5

lemma quad_eq_r : ∀ i : ZMod 4, x (quad (2 : Fin 7) 6 0 5 i) = quad (x 2) (x 6) (x 0) (x 5) i := by
  intro i; fin_cases i <;> rfl

lemma ext_vertices (q : Fin 7) (hqS : q ∉ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (2 : Fin 7) 6 0 5 j) :
    q = 1 ∨ q = 3 := by
  revert q; decide

lemma mid_vertices (q : Fin 7) (hqS : q ∈ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (2 : Fin 7) 6 0 5 j) :
    q = 4 := by
  revert q; decide

lemma far_cand (m : ZMod 4) (hm : m ≠ 0) (hmS : quad (2 : Fin 7) 6 0 5 m ∉ s0x_S24 4) : m = 3 := by
  revert m; decide

lemma far_cand3 (m : ZMod 4) (hm : m ≠ 3) (hmS : quad (2 : Fin 7) 6 0 5 m ∉ s0x_S24 4) : m = 0 := by
  revert m; decide

lemma w5_notS : quad (2 : Fin 7) 6 0 5 3 ∉ s0x_S24 4 := by decide

/-- Cross-046 core: depth fact `hbase` replaces hiii, hiv, strict obtuseness; far vertex 2 or 5. -/
theorem q046_cross_core (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 4 - x 0⟫)
    (hii : 0 < ⟪F.N 6, u47 F⟫)
    (hbase : ⟪x 6, u47 F⟫ < ⟪x 0, u47 F⟫)
    (hC5 : ⟪F.N 5, u47 F⟫ < 0) (hC2 : ⟪F.N 2, u47 F⟫ ≤ 0)
    (hfar : (F.f 4 (x 2) < F.f 4 (x 5) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
        ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0)) ∨
      (F.f 4 (x 5) < F.f 4 (x 2) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, x 6 - x 0⟫ ≠ 0) :
    FaceChordView F 4 := by
  have hβ := beta_pos F hi hC5
  set p : ZMod 4 → ℝ³ := quad (x 2) (x 6) (x 0) (x 5) with hp
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩdef
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have hΩ2 : 0 < Ω ^ 2 := sq_pos_of_ne_zero hΩ
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, u47 F + ε • (x 6 - x 0)⟫ < 0 := by
    have := eventually_pos_affine (A := -⟪F.N 5, u47 F⟫) (B := F.f 5 (x 0)) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [view_inner, F.zero 5 6 (by decide)]
    linarith
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 6, u47 F + ε • (x 6 - x 0)⟫ := by
    have := eventually_pos_affine (A := ⟪F.N 6, u47 F⟫) (B := F.f 6 (x 6) - F.f 6 (x 0)) (Or.inl hii)
    filter_upwards [this] with ε hε
    rw [view_inner]; exact hε
  have eβ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (F.f 7 (x 4) - F.f 7 (x 0)) - ε := by
    have := eventually_pos_affine (A := F.f 7 (x 4) - F.f 7 (x 0)) (B := -1) (Or.inl hβ)
    filter_upwards [this] with ε hε
    linarith
  have hk : Ω * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0 := by
    have h := omega_mul_det3_0256_pos_unconditional F
    have e : det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) =
        - det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) := by
      show det3 (x 0 - x 2) (x 5 - x 6) (x 2 - x 6) = _
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; linarith
  have hcyc_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < Ω * triD p (u47 F + ε • (x 6 - x 0)) i := by
    filter_upwards [e5, e6, eβ, ev0] with ε h5 h6 hb hε
    have hε' : 0 < ε := hε
    obtain ⟨h4, h5', h7, h2, h3, h6', h1⟩ := signs_view F hC2 ε hε' hb h5 h6
    obtain ⟨ρ, hρ, hcyc, hin, hin3⟩ := quadRim046 F h4 h5' h7 h2 h3 h6' h1
    have hρΩ : 0 < ρ * Ω := rho_pos F (hin 0) h5'
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
    have hT : 0 < (ρ * Ω) * (ρ * triD p (u47 F + ε • (x 6 - x 0)) i) := mul_pos hρΩ h
    have e : (ρ * Ω) * (ρ * triD p (u47 F + ε • (x 6 - x 0)) i) =
        ρ ^ 2 * (Ω * triD p (u47 F + ε • (x 6 - x 0)) i) := by ring
    rw [e] at hT
    exact pos_of_mul_pos_right hT (sq_nonneg ρ)
  have hbase' : min ⟪p 1, u47 F⟫ ⟪p 3, u47 F⟫ < max ⟪p 0, u47 F⟫ ⟪p 2, u47 F⟫ := by
    have h6 : ⟪p 1, u47 F⟫ = ⟪x 6, u47 F⟫ := rfl
    have h0 : ⟪p 2, u47 F⟫ = ⟪x 0, u47 F⟫ := rfl
    exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le (by rw [h6]; exact hbase) (by rw [h0]; exact le_max_right _ _))
  have hgen' : ∀ i j : ZMod 4, i ≠ j → ⟪p i - p j, u47 F⟫ ≠ 0 ∨ ⟪p i - p j, x 6 - x 0⟫ ≠ 0 := hgen
  have hU := cornerU p (u47 F) (x 6 - x 0) Ω hcyc_ev hk hbase' hgen'
  obtain ⟨ε, h5, h6, hb, hε, hinjU⟩ := (e5.and (e6.and (eβ.and (ev0.and hU)))).exists
  have hε' : 0 < ε := hε
  set u := u47 F + ε • (x 6 - x 0) with hu
  obtain ⟨h4, h5', h7, h2, h3, h6', h1⟩ := signs_view F hC2 ε hε' hb h5 h6
  obtain ⟨ρ, hρ, hcyc, hin, hin3⟩ := quadRim046 F h4 h5' h7 h2 h3 h6' h1
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) hinjU.2
  set r : ZMod 4 → Fin 7 := quad (2 : Fin 7) 6 0 5 with hr
  have hrx : ∀ i, x (r i) = p i := quad_eq_r
  set κ := (-F.f 7 (x 4)) + (F.f 7 (x 4) - F.f 7 (x 0)) with hκdef
  have hα : 0 < -F.f 7 (x 4) := by linarith [F.neg 7 4 (by decide : (4 : Fin 7) ∉ s0x_S24 7)]
  have hκ : 0 < κ := by linarith
  obtain ⟨w, hwS, hfarw, hoffw⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 4 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 4 → F.f 4 (x (r w)) < F.f 4 (x (r m))) ∧
      (⟪F.N 4, cross (x (r (1 + 1)) - x (r 1)) (x (r w) - x (r 1))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 1), x (r (1 + 1)) - x (r 1)⟫ < 0 ∨
        ⟪x (r w) - x (r (1 + 1)), x (r 1) - x (r (1 + 1))⟫ < 0) := by
    rcases hfar with ⟨hf, ho⟩ | ⟨hf, ho⟩
    · refine ⟨0, by decide, ?_, ho⟩
      intro m hm hmS
      have := far_cand m hm hmS
      subst this
      exact hf
    · refine ⟨3, w5_notS, ?_, ho⟩
      intro m hm hmS
      have := far_cand3 m hm hmS
      subst this
      exact hf
  refine ⟨u, 4, inferInstance, r, 1, w, ρ, h4, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, hwS, hfarw, hoffw⟩
  · show quad (2 : Fin 7) 6 0 5 1 ∈ s0x_S24 4; decide
  · show quad (2 : Fin 7) 6 0 5 (1 + 1) ∈ s0x_S24 4; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    rcases ext_vertices q hqS hqr with rfl | rfl
    · exact hin i
    · exact hin3 i
  · intro q hqS hqr
    have hq4 := mid_vertices q hqS hqr
    subst hq4
    have hra : x (r 1) = x 6 := rfl
    have hra1 : x (r (1 + 1)) = x 0 := rfl
    rw [hra, hra1]
    have hκ' : (-F.f 7 (x 4) + ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) - ε) ≠ 0 := by
      have : (-F.f 7 (x 4) + ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) - ε) = κ := by rw [hκdef]; ring
      rw [this]; exact hκ.ne'
    have hme := middle_eq (x 4) (x 0) (x 6) (-F.f 7 (x 4) + ε) ((F.f 7 (x 4) - F.f 7 (x 0)) - ε) hκ'
    have hsum : (-F.f 7 (x 4) + ε) + ((F.f 7 (x 4) - F.f 7 (x 0)) - ε) = κ := by rw [hκdef]; ring
    have hV : u = (-F.f 7 (x 4) + ε) • (x 4 - x 0) + ((F.f 7 (x 4) - F.f 7 (x 0)) - ε) • (x 4 - x 6) := by
      rw [hu]; unfold u47
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    refine ⟨(-F.f 7 (x 4) + ε) / κ, 1 / κ, ?_, ?_, by positivity, ?_⟩
    · apply div_pos <;> linarith
    · rw [div_lt_one hκ]; linarith
    · rw [hV]; rw [hsum] at hme; exact hme
  · simp_rw [hrx]; exact hinjU.1
  · simp_rw [hrx]; exact Or.inl h_uni


/-- **Theorem Cross-046**: If `{012, 016}` fail at `ω3` and `a4 < 1`, `<N6, u47> > 0`
(with strict obtuseness at `1`, C-bar signs at `u47`, `hfar`, `hoff`, `hgen`),
then `FaceChordView F 4` holds at `u47 + ε • (x 6 - x 0)`. -/
theorem q046_cross (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 4 - x 0⟫)
    (hii : 0 < ⟪F.N 6, u47 F⟫)
    (hiii : ⟪x 2, u0 x (omega3_012 F)⟫ ≤ ⟪x 0, u0 x (omega3_012 F)⟫)
    (hiv : ⟪x 6, u1 x (omega3_012 F)⟫ ≤ ⟪x 0, u1 x (omega3_012 F)⟫)
    (hob01 : ⟪x 0 - x 1, x 2 - x 1⟫ < 0) (hob02 : ⟪x 0 - x 1, x 6 - x 1⟫ < 0)
    (hob12 : ⟪x 2 - x 1, x 6 - x 1⟫ < 0)
    (hC5 : ⟪F.N 5, u47 F⟫ < 0) (hC2 : ⟪F.N 2, u47 F⟫ ≤ 0) (hC0 : ⟪F.N 0, u47 F⟫ ≤ 0)
    (hfar : F.f 4 (x 2) < F.f 4 (x 5))
    (hoff : ⟪F.N 4, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
      ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, x 6 - x 0⟫ ≠ 0) :
    FaceChordView F 4 :=
  q046_cross_core F hi hii (base_gt F hiii hiv hob01 hob02 hob12 hC5 hC0) hC5 hC2
    (Or.inl ⟨hfar, hoff⟩) hgen

/-- The Type24 structure of an S0xFac on the 24-facet family. -/
noncomputable def mkT (F : S0xFac 9 s0x_S24 x) : Type24 x where
  t012 := ⟨F.f 0, F.N 0, F.hN 0, fun i hi => F.zero 0 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 0 i (by simpa [s0x_S24] using hi)⟩
  t016 := ⟨F.f 1, F.N 1, F.hN 1, fun i hi => F.zero 1 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 1 i (by simpa [s0x_S24] using hi)⟩
  t126 := ⟨F.f 5, F.N 5, F.hN 5, fun i hi => F.zero 5 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 5 i (by simpa [s0x_S24] using hi)⟩
  t236 := ⟨F.f 7, F.N 7, F.hN 7, fun i hi => F.zero 7 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 7 i (by simpa [s0x_S24] using hi)⟩
  t046 := ⟨F.f 4, F.N 4, F.hN 4, fun i hi => F.zero 4 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 4 i (by simpa [s0x_S24] using hi)⟩
  t025 := ⟨F.f 2, F.N 2, F.hN 2, fun i hi => F.zero 2 i (by simpa [s0x_S24] using hi),
    fun i hi => F.neg 2 i (by simpa [s0x_S24] using hi)⟩

theorem cbar_core (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, u47 F⟫ = - F.f 5 (x 0) * F.f 7 (x 1) * (1 + omega4 x) * oblX2 x 4 ∧
    ⟪F.N 2, u47 F⟫ = - F.f 2 (x 1) * F.f 7 (x 1) * oblX2 x 4 * Delta24 x := by
  have T := mkT F
  have s7 : ∀ v, F.f 7 (x v) = F.f 7 (x 1) *
      (1 - (oblX2 x v + oblX6 x v - omega3 x * oblX0 x v)) := fun v => (mkT F).side236 v
  have s2 : ∀ v, F.f 2 (x v) = F.f 2 (x 1) *
      (1 - (oblX0 x v + oblX2 x v - omega5 x * oblX6 x v)) := fun v => (mkT F).side025 v
  have e5 : ∀ v, F.f 5 (x v) = F.f 5 (x 1) + oblX0 x v * (F.f 5 (x 0) - F.f 5 (x 1)) +
      oblX2 x v * (F.f 5 (x 2) - F.f 5 (x 1)) + oblX6 x v * (F.f 5 (x 6) - F.f 5 (x 1)) :=
    fun v => (mkT F).eval (mkT F).t126 v
  have eq4 : oblX0 x 4 + oblX6 x 4 - omega4 x * oblX2 x 4 = 1 := (mkT F).eq4
  have hc : oblX6 x 4 = 1 - oblX0 x 4 + omega4 x * oblX2 x 4 := by linarith
  have o0 := (mkT F).oblX0_zero'; have o2 := Type24.oblX2_zero' (x := x)
  have o6 := Type24.oblX6_zero (x := x)
  have p6 := Type24.oblX0_six (x := x)
  have q2 := Type24.oblX2_six (x := x)
  have r6 := (mkT F).oblX6_six
  have z1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have z2 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have z6 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have w4 := e5 4
  rw [z1, z2, z6] at w4
  have y2 := s7 4; have y0 := s7 0
  have g0 := s2 4; have g6 := s2 6
  have g00 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have f7_6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have f5_6 : F.f 5 (x 6) = 0 := z6
  have h6 : F.f 6 (x 6) = F.f 6 (x 6) := rfl
  constructor
  · rw [inner_u47, F.zero 5 6 (by decide)]
    rw [w4, y2, y0, hc, o0, o2, o6]
    ring
  · rw [inner_u47]
    rw [g00, g6, g0, y2, y0, hc, o0, o2, o6, p6, q2, r6]
    unfold Delta24
    ring



theorem cbar_hC5 (F : S0xFac 9 s0x_S24 x)
    (hCbar : 0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x) :
    ⟪F.N 5, u47 F⟫ < 0 := by
  rw [(cbar_core F).1]
  have a := F.neg 5 0 (by decide)
  have b := F.neg 7 1 (by decide)
  have c := (mkT F).X2_pos (v := 4) (by decide)
  have d := hCbar.2.1
  have : 0 < F.f 5 (x 0) * F.f 7 (x 1) := mul_pos_of_neg_of_neg a b
  have : 0 < F.f 5 (x 0) * F.f 7 (x 1) * (1 + omega4 x) * oblX2 x 4 := by positivity
  linarith

theorem cbar_hC2 (F : S0xFac 9 s0x_S24 x)
    (hCbar : 0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x) :
    ⟪F.N 2, u47 F⟫ ≤ 0 := by
  rw [(cbar_core F).2]
  have a := F.neg 2 1 (by decide)
  have b := F.neg 7 1 (by decide)
  have c := (mkT F).X2_pos (v := 4) (by decide)
  have d := hCbar.2.2.2
  have : 0 < F.f 2 (x 1) * F.f 7 (x 1) := mul_pos_of_neg_of_neg a b
  have : 0 ≤ F.f 2 (x 1) * F.f 7 (x 1) * oblX2 x 4 * Delta24 x := by positivity
  linarith

theorem cbar_hC (F : S0xFac 9 s0x_S24 x)
    (hCbar : 0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x) :
    ⟪F.N 5, u47 F⟫ < 0 ∧ ⟪F.N 2, u47 F⟫ ≤ 0 := ⟨cbar_hC5 F hCbar, cbar_hC2 F hCbar⟩

theorem q046_cross_cbar (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 4 - x 0⟫)
    (hii : 0 < ⟪F.N 6, u47 F⟫)
    (hbase : ⟪x 6, u47 F⟫ < ⟪x 0, u47 F⟫)
    (hCbar : 0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x)
    (hfar : (F.f 4 (x 2) < F.f 4 (x 5) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
        ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0)) ∨
      (F.f 4 (x 5) < F.f 4 (x 2) ∧
      (⟪F.N 4, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
      ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, x 6 - x 0⟫ ≠ 0) :
    FaceChordView F 4 := by
  obtain ⟨hC5, hC2⟩ := cbar_hC F hCbar
  exact q046_cross_core F hi hii hbase hC5 hC2 hfar hgen


end Minimality.T24.R046
