module

public import Minimality.Q45Tie
public import Minimality.CaseC09Cross
public import Minimality.CornerU
public import Minimality.HEnd

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.RimFromSigns

namespace Minimality.T24.Q45
variable {x : Fin 7 → ℝ³}

/-- Canonical tie-62 `α` parameter: `⟪x 6 - x 2, e4 x⟫`. -/
noncomputable def tieAlpha62 (x : Fin 7 → ℝ³) : ℝ := ⟪x 6 - x 2, e4 x⟫

/-- Canonical tie-62 `β` parameter: `-⟪x 6 - x 2, e5 x⟫`. -/
noncomputable def tieBeta62 (x : Fin 7 → ℝ³) : ℝ := -⟪x 6 - x 2, e5 x⟫

theorem inner_tie62 (x : Fin 7 → ℝ³) :
    ⟪x 6, u_Pi x (tieAlpha62 x) (tieBeta62 x)⟫ = ⟪x 2, u_Pi x (tieAlpha62 x) (tieBeta62 x)⟫ := by
  have h : ⟪x 6 - x 2, u_Pi x (tieAlpha62 x) (tieBeta62 x)⟫ = 0 := by
    simp only [u_Pi, tieAlpha62, tieBeta62, inner_add_right, real_inner_smul_right]
    ring
  rw [inner_sub_left] at h
  linarith

lemma rj0t_inner_tilt (p b d : ℝ³) (ε : ℝ) : ⟪p, b + ε • d⟫ = ⟪p, b⟫ + ε * ⟪p, d⟫ := by
  rw [inner_add_right, real_inner_smul_right]

lemma rj0t_ev_lt (p q b d : ℝ³) (h : ⟪p, b⟫ < ⟪q, b⟫ ∨ (⟪p, b⟫ = ⟪q, b⟫ ∧ ⟪p, d⟫ < ⟪q, d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪p, b + ε • d⟫ < ⟪q, b + ε • d⟫ := by
  filter_upwards [Minimality.CaseC09.ev_lt h] with ε hε
  rwa [rj0t_inner_tilt, rj0t_inner_tilt]

lemma rj0t_ev_ne (p q b d : ℝ³) (h : ⟪p, b⟫ ≠ ⟪q, b⟫ ∨ ⟪p, d⟫ ≠ ⟪q, d⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪p, b + ε • d⟫ ≠ ⟪q, b + ε • d⟫ := by
  rcases lt_trichotomy ⟪p, b⟫ ⟪q, b⟫ with h1 | h1 | h1
  · filter_upwards [rj0t_ev_lt p q b d (Or.inl h1)] with ε hε using hε.ne
  · have hd : ⟪p, d⟫ ≠ ⟪q, d⟫ := by
      rcases h with h | h
      · exact (h h1).elim
      · exact h
    rcases lt_or_gt_of_ne hd with h2 | h2
    · filter_upwards [rj0t_ev_lt p q b d (Or.inr ⟨h1, h2⟩)] with ε hε using hε.ne
    · filter_upwards [rj0t_ev_lt q p b d (Or.inr ⟨h1.symm, h2⟩)] with ε hε using hε.ne'
  · filter_upwards [rj0t_ev_lt q p b d (Or.inl h1)] with ε hε using hε.ne'

/-- the tilt `b + eps (sigma (x4 - x5))` is the J0 view with moved coefficients -/
lemma rj0t_tilt_eq (x : Fin 7 → ℝ³) (α β σ ε : ℝ) :
    u_Pi x α β + ε • (σ • (x 4 - x 5)) = u_Pi x (α - σ * ε) (β + σ * ε) := by
  ext j
  simp only [u_Pi, e4, e5, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-! ### Rim 4 3 2 1 6 (vertex 1 exposed, N6 < 0) -/

theorem rj0t_rim5C (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0) (hN0 : ⟪F.N 0, u⟫ < 0) (hN1 : ⟪F.N 1, u⟫ < 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) (hN6 : ⟪F.N 6, u⟫ < 0)
    (hN7 : 0 < ⟪F.N 7, u⟫) (hN8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quint (x 4) (x 3) (x 2) (x 1) (x 6) (i + 1) - quint (x 4) (x 3) (x 2) (x 1) (x 6) i)
        (quint (x 4) (x 3) (x 2) (x 1) (x 6) j - quint (x 4) (x 3) (x 2) (x 1) (x 6) i) u := by
  have cr0 := cross_ne_zero_of_facet_sign F 8 4 3 (by decide) (by decide) hN8.ne' 4 (by decide) (by decide)
  have cr1 := cross_ne_zero_of_facet_sign F 6 3 2 (by decide) (by decide) hN6.ne 8 (by decide) (by decide)
  have cr2 := cross_ne_zero_of_facet_sign F 0 2 1 (by decide) (by decide) hN0.ne 6 (by decide) (by decide)
  have cr3 := cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) hN1.ne 0 (by decide) (by decide)
  have cr4 := cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) hN4.ne 1 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 3 4 3 (by decide) (by decide) u hN3 cr0
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 6 7 3 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN6, hN7⟩ cr1
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 0 5 2 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN5⟩ cr2
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 1 5 1 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN1, hN5⟩ cr3
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 4 8 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN4, hN8⟩ cr4
  exact ⟨σ0, hσ0n, rim5_assemble (x 4) (x 3) (x 2) (x 1) (x 6) u σ0 σ1 σ2 σ3 σ4
    (hσ0 2 (by decide)) (hσ0 1 (by decide)) (hσ0 6 (by decide))
    (hσ1 1 (by decide)) (hσ1 6 (by decide)) (hσ1 4 (by decide))
    (hσ2 6 (by decide)) (hσ2 4 (by decide)) (hσ2 3 (by decide))
    (hσ3 4 (by decide)) (hσ3 3 (by decide)) (hσ3 2 (by decide))
    (hσ4 3 (by decide)) (hσ4 2 (by decide)) (hσ4 1 (by decide))⟩

theorem rj0t_signs_C (F : S0xFac 9 s0x_S24 x) (s t α β : ℝ) (hs0 : 0 < s) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hα : 0 < α) (hβ : 0 < β) (h8 : 0 < α * (1 - s) + β * t) (h6 : α * s + β * (1 - t) < 0) :
    ⟪F.N 3, u_Pi x α β⟫ = 0 ∧ ⟪F.N 0, u_Pi x α β⟫ < 0 ∧ ⟪F.N 1, u_Pi x α β⟫ < 0 ∧
    ⟪F.N 2, u_Pi x α β⟫ < 0 ∧ ⟪F.N 4, u_Pi x α β⟫ < 0 ∧ ⟪F.N 6, u_Pi x α β⟫ < 0 ∧
    0 < ⟪F.N 8, u_Pi x α β⟫ := by
  refine ⟨inner_N3_u_Pi F α β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inner_N0_u_Pi F α β]
    have := mul_neg_of_pos_of_neg hα (inner_N0_e5_neg F)
    have := mul_neg_of_pos_of_neg hβ (inner_N0_e4_neg F)
    linarith
  · rw [inner_N1_u_Pi F α β]
    have := mul_neg_of_pos_of_neg hα (inner_N1_e5_neg F)
    have := mul_neg_of_pos_of_neg hβ (inner_N1_e4_neg F)
    linarith
  · rw [inner_N2_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hβ (inner_N2_e4_neg F)
  · rw [inner_N4_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hα (inner_N4_e5_neg F)
  · have hrel := inner_N6_u_Pi F s t α β hdecomp
    have hneg : (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫ < 0 :=
      mul_neg_of_neg_of_pos h6 (inner_N6_e5_pos F)
    rw [← hrel] at hneg
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hs0.le hn]
  · have hrel := inner_N8_u_Pi F s t α β hdecomp
    have hpos : 0 < (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫ := mul_pos h8 (inner_N8_e4_pos F)
    rw [← hrel] at hpos
    exact pos_of_mul_pos_right hpos ht.le

lemma rj0t_ext_C (q : Fin 7) (hqS : q ∉ s0x_S24 3) (hqr : ∀ j : ZMod 5, q ≠ quint (4 : Fin 7) 3 2 1 6 j) :
    False := by
  revert q; decide

lemma rj0t_mid_C (q : Fin 7) (hqS : q ∈ s0x_S24 3) (hqr : ∀ j : ZMod 5, q ≠ quint (4 : Fin 7) 3 2 1 6 j) :
    q = 0 ∨ q = 5 := by
  revert q; decide

lemma rj0t_far_C (m : ZMod 5) (hmS : quint (4 : Fin 7) 3 2 1 6 m ∉ s0x_S24 3) :
    quint (4 : Fin 7) 3 2 1 6 m = 1 ∨ quint (4 : Fin 7) 3 2 1 6 m = 2 ∨ quint (4 : Fin 7) 3 2 1 6 m = 6 := by
  revert m; decide

lemma rj0t_rinj_C : ∀ a b : ZMod 5, quint (4 : Fin 7) 3 2 1 6 a = quint (4 : Fin 7) 3 2 1 6 b → a = b := by
  decide

lemma rj0t_quint_eq_C : ∀ i : ZMod 5, x (quint (4 : Fin 7) 3 2 1 6 i) = quint (x 4) (x 3) (x 2) (x 1) (x 6) i := by
  intro i; fin_cases i <;> rfl

/-- middle `0` over the chord `4 -> 3` when `h6 < 0`. -/
lemma rj0t_mid0 (x : Fin 7 → ℝ³) (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h8 : α * (1 - s) + β * t ≠ 0) :
    x 0 = x 4 + (α / (α * (1 - s) + β * t)) • (x 3 - x 4) + (-t / (α * (1 - s) + β * t)) • u_Pi x α β := by
  ext j
  have hj := congrArg (fun v => v j) hdecomp
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj
  simp only [u_Pi, e4, e5, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  linear_combination (-α) * hj

lemma rj0t_mid5 (x : Fin 7 → ℝ³) (s t α β : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h8 : α * (1 - s) + β * t ≠ 0) :
    x 5 = x 4 + ((α + β) / (α * (1 - s) + β * t)) • (x 3 - x 4) +
      ((1 - s - t) / (α * (1 - s) + β * t)) • u_Pi x α β := by
  ext j
  have hj := congrArg (fun v => v j) hdecomp
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj
  simp only [u_Pi, e4, e5, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  linear_combination (-(α + β)) * hj

lemma rj0t_bounds_C (s t α β : ℝ) (hst : 1 < s + t) (hα : 0 < α) (hβ : 0 < β)
    (h8 : 0 < α * (1 - s) + β * t) (h6 : α * s + β * (1 - t) < 0) :
    (0 < α / (α * (1 - s) + β * t) ∧ α / (α * (1 - s) + β * t) < 1) ∧
    (0 < (α + β) / (α * (1 - s) + β * t) ∧ (α + β) / (α * (1 - s) + β * t) < 1) ∧
    ((1 - s - t) / (α * (1 - s) + β * t) ≠ 0) := by
  refine ⟨⟨div_pos hα h8, ?_⟩, ⟨div_pos (add_pos hα hβ) h8, ?_⟩, ?_⟩
  · rw [div_lt_one h8]; nlinarith
  · rw [div_lt_one h8]; nlinarith
  · exact div_ne_zero (by linarith) h8.ne'

/-- **Leaf J0-Tie62, quad rim.** On the 0345 circle at `u_Pi x α β` with vertex 1 hidden
(`N5 < 0`) and the adjacent tie `z6 = z2` of the quad rim `(6, 4, 5, 2)`: the tilt
`u ± eps (x4 - x5)` is a face-circle view with that quad rim. -/
theorem rj0t_tie62_quad (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t)
    (hst : 1 < s + t) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (h8 : 0 < α * (1 - s) + β * t)
    (h6 : 0 < α * s + β * (1 - t))
    (hN5 : ⟪F.N 5, u_Pi x α β⟫ < 0)
    (htie : ⟪x 6, u_Pi x α β⟫ = ⟪x 2, u_Pi x α β⟫)
    (σ : ℝ) (hΔ : σ * ⟪x 6 - x 2, x 4 - x 5⟫ ≠ 0)
    (hn : σ * ⟪x 6 - x 2, x 4 - x 5⟫ < 0 ∨
      min ⟪x 6, u_Pi x α β⟫ ⟪x 5, u_Pi x α β⟫ < max ⟪x 4, u_Pi x α β⟫ ⟪x 2, u_Pi x α β⟫)
    (hp : 0 < σ * ⟪x 6 - x 2, x 4 - x 5⟫ ∨
      min ⟪x 4, u_Pi x α β⟫ ⟪x 2, u_Pi x α β⟫ < max ⟪x 6, u_Pi x α β⟫ ⟪x 5, u_Pi x α β⟫)
    (h64 : ⟪x 6, u_Pi x α β⟫ ≠ ⟪x 4, u_Pi x α β⟫) (h65 : ⟪x 6, u_Pi x α β⟫ ≠ ⟪x 5, u_Pi x α β⟫)
    (h45 : ⟪x 4, u_Pi x α β⟫ ≠ ⟪x 5, u_Pi x α β⟫) (h42 : ⟪x 4, u_Pi x α β⟫ ≠ ⟪x 2, u_Pi x α β⟫)
    (h52 : ⟪x 5, u_Pi x α β⟫ ≠ ⟪x 2, u_Pi x α β⟫)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set b : ℝ³ := u_Pi x α β with hb
  set dd : ℝ³ := σ • (x 4 - x 5) with hdd
  set Δ : ℝ := ⟪x 6 - x 2, x 4 - x 5⟫ with hΔdef
  have hd62 : ⟪x 6 - x 2, dd⟫ = σ * Δ := by rw [hdd, real_inner_smul_right]
  have hΔσ : ⟪x 6, dd⟫ - ⟪x 2, dd⟫ = σ * Δ := by rw [← inner_sub_left, hd62]
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by intro i; fin_cases i <;> rfl
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have eα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < α + ε * (-σ) :=
    eventually_pos_affine (A := α) (B := -σ) (Or.inl hα)
  have eβ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < β + ε * σ :=
    eventually_pos_affine (A := β) (B := σ) (Or.inl hβ)
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (α * (1 - s) + β * t) + ε * (σ * (s + t - 1)) :=
    eventually_pos_affine (A := α * (1 - s) + β * t) (B := σ * (s + t - 1)) (Or.inl h8)
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (α * s + β * (1 - t)) + ε * (σ * (1 - s - t)) :=
    eventually_pos_affine (A := α * s + β * (1 - t)) (B := σ * (1 - s - t)) (Or.inl h6)
  have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -⟪F.N 5, b⟫ + ε * (-⟪F.N 5, dd⟫) :=
    eventually_pos_affine (A := -⟪F.N 5, b⟫) (B := -⟪F.N 5, dd⟫) (Or.inl (by linarith))
  have hn' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⟪x 6, b + ε • dd⟫ < ⟪x 4, b + ε • dd⟫ ∨ ⟪x 6, b + ε • dd⟫ < ⟪x 2, b + ε • dd⟫ ∨
        ⟪x 5, b + ε • dd⟫ < ⟪x 4, b + ε • dd⟫ ∨ ⟪x 5, b + ε • dd⟫ < ⟪x 2, b + ε • dd⟫) := by
    rcases hn with hneg | hm
    · filter_upwards [rj0t_ev_lt (x 6) (x 2) b dd (Or.inr ⟨htie, by linarith⟩)] with ε h
      exact Or.inr (Or.inl h)
    · rcases hn_of_min_lt_max (z := fun i => ⟪p_quad i, b⟫) hm with h | h | h | h
      · filter_upwards [rj0t_ev_lt (x 6) (x 4) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inl h'
      · filter_upwards [rj0t_ev_lt (x 6) (x 2) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inl h')
      · filter_upwards [rj0t_ev_lt (x 5) (x 4) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inr (Or.inl h'))
      · filter_upwards [rj0t_ev_lt (x 5) (x 2) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inr (Or.inr h'))
  have hp' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⟪x 4, b + ε • dd⟫ < ⟪x 6, b + ε • dd⟫ ∨ ⟪x 2, b + ε • dd⟫ < ⟪x 6, b + ε • dd⟫ ∨
        ⟪x 4, b + ε • dd⟫ < ⟪x 5, b + ε • dd⟫ ∨ ⟪x 2, b + ε • dd⟫ < ⟪x 5, b + ε • dd⟫) := by
    rcases hp with hpos | hm
    · filter_upwards [rj0t_ev_lt (x 2) (x 6) b dd (Or.inr ⟨htie.symm, by linarith⟩)] with ε h
      exact Or.inr (Or.inl h)
    · rcases hp_of_min_lt_max (z := fun i => ⟪p_quad i, b⟫) hm with h | h | h | h
      · filter_upwards [rj0t_ev_lt (x 4) (x 6) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inl h'
      · filter_upwards [rj0t_ev_lt (x 2) (x 6) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inl h')
      · filter_upwards [rj0t_ev_lt (x 4) (x 5) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inr (Or.inl h'))
      · filter_upwards [rj0t_ev_lt (x 2) (x 5) b dd (Or.inl (by exact h))] with ε h'
        exact Or.inr (Or.inr (Or.inr h'))
  have i64 := rj0t_ev_ne (x 6) (x 4) b dd (Or.inl h64)
  have i65 := rj0t_ev_ne (x 6) (x 5) b dd (Or.inl h65)
  have i45 := rj0t_ev_ne (x 4) (x 5) b dd (Or.inl h45)
  have i42 := rj0t_ev_ne (x 4) (x 2) b dd (Or.inl h42)
  have i52 := rj0t_ev_ne (x 5) (x 2) b dd (Or.inl h52)
  have i62 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x 6, b + ε • dd⟫ ≠ ⟪x 2, b + ε • dd⟫ :=
    rj0t_ev_ne (x 6) (x 2) b dd (Or.inr (by intro h; apply hΔ; linarith))
  obtain ⟨ε, hε, hα', hβ', h8', h6', hN5', hn2, hp2, j64, j65, j45, j42, j52, j62⟩ :=
    (ev0.and (eα.and (eβ.and (e8.and (e6.and (e5.and (hn'.and (hp'.and (i64.and (i65.and (i45.and (i42.and (i52.and (i62)))))))))))))).exists
  set u : ℝ³ := b + ε • dd with hu
  have hu_Pi : u = u_Pi x (α - σ * ε) (β + σ * ε) := rj0t_tilt_eq x α β σ ε
  have hα2 : 0 < α - σ * ε := by linarith
  have hβ2 : 0 < β + σ * ε := by linarith
  have h82 : 0 < (α - σ * ε) * (1 - s) + (β + σ * ε) * t := by nlinarith
  have h62 : 0 < (α - σ * ε) * s + (β + σ * ε) * (1 - t) := by nlinarith
  have hN5u : ⟪F.N 5, u⟫ < 0 := by
    rw [hu, rj0t_inner_tilt]; linarith
  have hN5Pi : ⟪F.N 5, u_Pi x (α - σ * ε) (β + σ * ε)⟫ < 0 := by rw [← hu_Pi]; exact hN5u
  have hsigns := lemma_signs_J0 F s t (α - σ * ε) (β + σ * ε) hs0 ht hst hdecomp hα2 hβ2 h82 h62 hN5Pi
  rw [← hu_Pi] at hsigns
  obtain ⟨hN3, hN2, hN4, hN5s, hN6, hN7, hN8⟩ := hsigns
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5s hN6 hN7 hN8
  have hinj : Function.Injective (fun i => ⟪p_quad i, u⟫) :=
    injective4 (by exact j64) (by exact j65) (by exact j62) (by exact j45) (by exact j42)
      (by exact j52)
  have h_uni : IsCyclicUnimodal (fun i => ⟪p_quad i, u⟫) :=
    Minimality.RimCell.isCyclicUnimodal_four _ hinj hn2 hp2
  have hsum : α - σ * ε + (β + σ * ε) ≠ 0 := by linarith
  have h_mb := middle_bounds_J0 s t _ _ hst hα2 hβ2 h82 h62
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, 1, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r 1) = x 4 := rfl
    have hra1 : x (r (1 + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨(α - σ * ε) / ((α - σ * ε) + (β + σ * ε)), -(1 / ((α - σ * ε) + (β + σ * ε))),
        h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi]
      exact middle_quad_x0 x _ _ hsum
    · refine ⟨((1 - s) * (α - σ * ε) + t * (β + σ * ε)) / ((α - σ * ε) + (β + σ * ε)),
        (s + t - 1) / ((α - σ * ε) + (β + σ * ε)), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi]
      exact middle_quad_x3 x s t _ _ hdecomp hsum
  · simp_rw [hr]
    exact hinj
  · simp_rw [hr]
    exact Or.inl (Minimality.strictUnimodal_of_cyclic (by decide) h_uni)
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        exact lt_of_le_of_ne (not_lt.mp h26) hS3.symm
  · have hra : x (r 1) = x 4 := rfl
    have hra1 : x (r (1 + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf J0-Tie62, pentagon rim.** On the 0345 circle at `u_Pi x α β` with `h6 < 0`
(`N6 < 0`, the case `t > 1`), vertex 1 exposed, the tie `z6 = z2` of the pentagon rim
`(4, 3, 2, 1, 6)` (chord `4 -> 3`, middles 0 and 5): the tilt `u ± eps (x4 - x5)` is a face-circle
view; the depths `z1 < z2 = z6 < z4 < z3` are strictly unimodal with the tie broken by the tilt. -/
theorem rj0t_tie62_pent (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t)
    (hst : 1 < s + t) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (h8 : 0 < α * (1 - s) + β * t)
    (h6 : α * s + β * (1 - t) < 0)
    (hN5 : 0 < ⟪F.N 5, u_Pi x α β⟫) (hN7 : 0 < ⟪F.N 7, u_Pi x α β⟫)
    (htie : ⟪x 6, u_Pi x α β⟫ = ⟪x 2, u_Pi x α β⟫)
    (σ : ℝ) (hΔ : σ * ⟪x 6 - x 2, x 4 - x 5⟫ ≠ 0)
    (h12 : ⟪x 1, u_Pi x α β⟫ < ⟪x 2, u_Pi x α β⟫)
    (h64 : ⟪x 6, u_Pi x α β⟫ < ⟪x 4, u_Pi x α β⟫)
    (h43 : ⟪x 4, u_Pi x α β⟫ < ⟪x 3, u_Pi x α β⟫)
    (w : Fin 7) (hw : w = 1 ∨ w = 2 ∨ w = 6)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 3 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 3 - x 4⟫ < 0 ∨
      ⟪x w - x 3, x 4 - x 3⟫ < 0) :
    FaceChordView F 3 := by
  set b : ℝ³ := u_Pi x α β with hb
  set dd : ℝ³ := σ • (x 4 - x 5) with hdd
  set Δ : ℝ := ⟪x 6 - x 2, x 4 - x 5⟫ with hΔdef
  have hd62 : ⟪x 6 - x 2, dd⟫ = σ * Δ := by rw [hdd, real_inner_smul_right]
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have eα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < α + ε * (-σ) :=
    eventually_pos_affine (A := α) (B := -σ) (Or.inl hα)
  have eβ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < β + ε * σ :=
    eventually_pos_affine (A := β) (B := σ) (Or.inl hβ)
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (α * (1 - s) + β * t) + ε * (σ * (s + t - 1)) :=
    eventually_pos_affine (A := α * (1 - s) + β * t) (B := σ * (s + t - 1)) (Or.inl h8)
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -(α * s + β * (1 - t)) + ε * (-(σ * (1 - s - t))) :=
    eventually_pos_affine (A := -(α * s + β * (1 - t))) (B := -(σ * (1 - s - t)))
      (Or.inl (by linarith))
  have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, b⟫ + ε * ⟪F.N 5, dd⟫ :=
    eventually_pos_affine (A := ⟪F.N 5, b⟫) (B := ⟪F.N 5, dd⟫) (Or.inl hN5)
  have e7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 7, b⟫ + ε * ⟪F.N 7, dd⟫ :=
    eventually_pos_affine (A := ⟪F.N 7, b⟫) (B := ⟪F.N 7, dd⟫) (Or.inl hN7)
  have l43 := rj0t_ev_lt (x 4) (x 3) b dd (Or.inl h43)
  have l23 := rj0t_ev_lt (x 2) (x 3) b dd (Or.inl (by linarith))
  have l12 := rj0t_ev_lt (x 1) (x 2) b dd (Or.inl h12)
  have l64 := rj0t_ev_lt (x 6) (x 4) b dd (Or.inl h64)
  have l16 := rj0t_ev_lt (x 1) (x 6) b dd (Or.inl (by linarith))
  have l24 := rj0t_ev_lt (x 2) (x 4) b dd (Or.inl (by linarith))
  have j62 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x 6, b + ε • dd⟫ ≠ ⟪x 2, b + ε • dd⟫ :=
    rj0t_ev_ne (x 6) (x 2) b dd (Or.inr (by
      intro h
      apply hΔ
      rw [← hd62, inner_sub_left, h, sub_self]))
  obtain ⟨ε, hε, hα', hβ', h8', h6', hN5', hN7', m43, m23, m12, m64, m16, m24, j62'⟩ :=
    (ev0.and (eα.and (eβ.and (e8.and (e6.and (e5.and (e7.and (l43.and (l23.and (l12.and (l64.and (l16.and (l24.and (j62)))))))))))))).exists
  set u : ℝ³ := b + ε • dd with hu
  have hu_Pi : u = u_Pi x (α - σ * ε) (β + σ * ε) := rj0t_tilt_eq x α β σ ε
  have hα2 : 0 < α - σ * ε := by linarith
  have hβ2 : 0 < β + σ * ε := by linarith
  have h82 : 0 < (α - σ * ε) * (1 - s) + (β + σ * ε) * t := by nlinarith
  have h62 : (α - σ * ε) * s + (β + σ * ε) * (1 - t) < 0 := by nlinarith
  have hN5u : 0 < ⟪F.N 5, u⟫ := by rw [hu, rj0t_inner_tilt]; exact hN5'
  have hN7u : 0 < ⟪F.N 7, u⟫ := by rw [hu, rj0t_inner_tilt]; exact hN7'
  have hsigns := rj0t_signs_C F s t (α - σ * ε) (β + σ * ε) hs0 ht hdecomp hα2 hβ2 h82 h62
  rw [← hu_Pi] at hsigns
  obtain ⟨hN3, hN0, hN1, hN2, hN4, hN6, hN8⟩ := hsigns
  obtain ⟨ρ, hρ, hconv⟩ := rj0t_rim5C F hN3 hN0 hN1 hN4 hN5u hN6 hN7u hN8
  set p5 : ZMod 5 → ℝ³ := quint (x 4) (x 3) (x 2) (x 1) (x 6) with hp5
  have hinj : Function.Injective (fun i => ⟪p5 i, u⟫) :=
    injective5
      (by intro h; change ⟪x 4, u⟫ = ⟪x 3, u⟫ at h; linarith)
      (by intro h; change ⟪x 4, u⟫ = ⟪x 2, u⟫ at h; linarith)
      (by intro h; change ⟪x 4, u⟫ = ⟪x 1, u⟫ at h; linarith)
      (by intro h; change ⟪x 4, u⟫ = ⟪x 6, u⟫ at h; linarith)
      (by intro h; change ⟪x 3, u⟫ = ⟪x 2, u⟫ at h; linarith)
      (by intro h; change ⟪x 3, u⟫ = ⟪x 1, u⟫ at h; linarith)
      (by intro h; change ⟪x 3, u⟫ = ⟪x 6, u⟫ at h; linarith)
      (by intro h; change ⟪x 2, u⟫ = ⟪x 1, u⟫ at h; linarith)
      (by intro h; change ⟪x 2, u⟫ = ⟪x 6, u⟫ at h; exact j62' h.symm)
      (by intro h; change ⟪x 1, u⟫ = ⟪x 6, u⟫ at h; linarith)
  have hcu : IsCyclicUnimodal (fun i => ⟪p5 i, u⟫) := by
    refine isCyclicUnimodal_of_top (by norm_num) hinj 1 ?_
    intro i hi
    have hc : ∀ i : ZMod 5, i ≠ 1 → i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    rcases hc i hi with rfl | rfl | rfl | rfl
    · exact Or.inr (by exact m43)
    · exact Or.inl (by exact m23)
    · exact Or.inl (by exact m12)
    · exact Or.inr (by exact m64)
  set r : ZMod 5 → Fin 7 := quint (4 : Fin 7) 3 2 1 6 with hr
  have hrx : ∀ i, x (r i) = p5 i := rj0t_quint_eq_C
  obtain ⟨wi, hrw⟩ : ∃ wi : ZMod 5, r wi = w := by
    rcases hw with rfl | rfl | rfl
    exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩]
  have h8ne : (α - σ * ε) * (1 - s) + (β + σ * ε) * t ≠ 0 := h82.ne'
  have hbd := rj0t_bounds_C s t _ _ hst hα2 hβ2 h82 h62
  refine ⟨u, 5, inferInstance, r, 0, wi, ρ, hN3, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quint (4 : Fin 7) 3 2 1 6 0 ∈ s0x_S24 3; decide
  · show quint (4 : Fin 7) 3 2 1 6 (0 + 1) ∈ s0x_S24 3; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hconv i j hj1 hj2
  · intro q hqS hqr i
    exact (rj0t_ext_C q hqS hqr).elim
  · intro q hqS hqr
    have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 3 := rfl
    rw [hra, hra1]
    rcases rj0t_mid_C q hqS hqr with rfl | rfl
    · refine ⟨(α - σ * ε) / ((α - σ * ε) * (1 - s) + (β + σ * ε) * t),
        -t / ((α - σ * ε) * (1 - s) + (β + σ * ε) * t), hbd.1.1, hbd.1.2, ?_, ?_⟩
      · exact div_ne_zero (neg_ne_zero.mpr ht.ne') h82.ne'
      · rw [hu_Pi]; exact rj0t_mid0 x s t _ _ hdecomp h8ne
    · refine ⟨((α - σ * ε) + (β + σ * ε)) / ((α - σ * ε) * (1 - s) + (β + σ * ε) * t),
        (1 - s - t) / ((α - σ * ε) * (1 - s) + (β + σ * ε) * t), hbd.2.1.1, hbd.2.1.2, hbd.2.2, ?_⟩
      rw [hu_Pi]; exact rj0t_mid5 x s t _ _ hdecomp h8ne
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl (Minimality.strictUnimodal_of_cyclic (by decide) hcu)
  · rw [hrw]
    rcases hw with rfl | rfl | rfl <;> decide
  · intro m hmw hmS
    rw [hrw]
    exact hmin (r m) (fun h => hmw (rj0t_rinj_C _ _ (h.trans hrw.symm))) (rj0t_far_C m hmS)
  · have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 3 := rfl
    rw [hra, hra1, hrw]
    exact hoff

end Minimality.T24.Q45
