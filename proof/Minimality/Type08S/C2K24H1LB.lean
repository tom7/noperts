module

public import Minimality.Type08S.C2K24H1LA

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k24h1l_cone {E : List (ℝ × ℝ)} {B c v1 v2 : ℝ}
    (h : k18Cone ((0, 1) :: (-B, -c) :: E) v1 v2) :
    0 < v2 ∧ 0 < -B * v1 - c * v2 ∧ k18Cone E v1 v2 := by
  have h1 := h (0, 1) (by simp)
  have h2 := h (-B, -c) (by simp)
  simp only at h1 h2
  refine ⟨by linarith, by linarith, fun l hl => h l (by simp [hl])⟩

set_option maxHeartbeats 12800000 in
/-- Type 08 M-stratum H1 tie, side `L1 = ⟪a - c', b' - c⟫ ≥ 0`: one cell at the view `b' - c`
(silhouette `(b', a, c', a', c)`). -/
theorem k24h1_ge {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (ht : ⟪c - a', a - b'⟫ = 0) (hL : 0 ≤ ⟪a - c', b' - c⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨⟨hα1, hβ1, hβB, hβ6, hγ6⟩, -, -⟩ := hH1
  have hkeys := k24h1l_keys hC hM hrel hα1 hβ1 hβ6 hγ6 ht
  obtain ⟨hF3, hF1, hF5⟩ := hkeys
  have hC' := hC
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC'
  have hs : 0 < β1 - 1 := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ³, p = (β1 - 1)⁻¹ • (a - d) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ³, q = b - d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ³, r = α1 • p + (c - d) := ⟨_, rfl⟩
  have hAd : a - d = (β1 - 1) • p := by
    rw [hp, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hCd : c - d = r - α1 • p := by rw [hr]; abel
  have hBd : b - d = q := hq.symm
  have hbc : b' - c = (β1 - 1) • r := by
    have e : b' - c = α1 • (a - d) + (β1 - 1) • (c - d) := by rw [hb']; module
    rw [e, hAd, hCd]; module
  have hΔ : det3 p q r ≠ 0 := by
    have e : det3 p q r = (β1 - 1)⁻¹ * det3 (a - d) (b - d) (c - d) := by
      rw [hr, hp, hq]
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (inv_ne_zero hs.ne') hdet
  have hr0 : r ≠ 0 := k17f_r0 hΔ
  have Ea : fpoint p q r d (β1 - 1, 0, 0) = a := by
    rw [k17f_fp]; have : a = d + (β1 - 1) • p := by rw [← hAd]; abel
    rw [this]; module
  have Ed : fpoint p q r d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint p q r d (0, 1, 0) = b := by
    rw [k17f_fp]; have : b = d + q := by rw [← hBd]; abel
    rw [this]; module
  have Ec : fpoint p q r d (-α1, 0, 1) = c := by
    rw [k17f_fp]; have : c = d + (r - α1 • p) := by rw [← hCd]; abel
    rw [this]; module
  have Eb' : fpoint p q r d (-α1, 0, β1) = b' := by
    rw [k17f_fp, hb', hAd, hCd]; module
  have Ec' : fpoint p q r d (α1 * (β1 - 1), β1, 0) = c' := by
    rw [k17f_fp, hc', hAd, hBd]; module
  have Ea' : fpoint p q r d (-α1 * γ6, β6, γ6) = a' := by
    rw [k17f_fp, ha', hBd, hCd]; module
  -- heights
  have hzr : ⟪r, r⟫ ≠ 0 := (real_inner_self_pos.2 hr0).ne'
  have hF3' : ⟪a', r⟫ < ⟪c, r⟫ := by
    rw [hbc, inner_smul_right] at hF3
    have := (pos_iff_pos_of_mul_pos (show 0 < (β1 - 1) * ⟪c - a', r⟫ from hF3)).1 hs
    rw [inner_sub_left] at this; linarith
  have hF1' : ⟪a, r⟫ < ⟪b', r⟫ := by
    rw [hbc, inner_smul_right] at hF1
    have := (pos_iff_pos_of_mul_pos (show 0 < (β1 - 1) * ⟪b' - a, r⟫ from hF1)).1 hs
    rw [inner_sub_left] at this; linarith
  have hF2' : ⟪c, r⟫ < ⟪b', r⟫ := by
    have : 0 < ⟪b' - c, r⟫ := by
      rw [hbc, inner_smul_left]; simp only [conj_trivial]
      exact mul_pos hs (real_inner_self_pos.2 hr0)
    rw [inner_sub_left] at this; linarith
  have hF4' : ⟪c', r⟫ ≤ ⟪a, r⟫ := by
    rw [hbc, inner_smul_right] at hL
    have : 0 ≤ ⟪a - c', r⟫ := by
      by_contra hn; push Not at hn; nlinarith [mul_pos hs (neg_pos.2 hn)]
    rw [inner_sub_left] at this; linarith
  -- tie breaking functional
  obtain ⟨E, hEray, hEex⟩ : ∃ E : List (ℝ × ℝ), (∀ l ∈ E, k18LexPos (l.1 * (-1) + l.2 * 0) (l.1 * 0 + l.2 * 1)) ∧
      (⟪c', r⟫ = ⟪a, r⟫ → ∀ v1 v2 : ℝ, k18Cone E v1 v2 →
        ⟪c', fcomb p q r v1 v2 0⟫ < ⟪a, fcomb p q r v1 v2 0⟫) := by
    rcases hF4'.lt_or_eq with h | h
    · exact ⟨[], by simp, fun e => absurd e h.ne⟩
    · refine ⟨[(⟪a - c', p⟫, ⟪a - c', q⟫)], ?_, ?_⟩
      · intro l hl
        simp only [List.mem_singleton] at hl; subst hl
        left
        simp only [mul_neg, mul_one, mul_zero, add_zero]
        have h0 : ⟪a - c', r⟫ = 0 := by rw [inner_sub_left]; linarith
        have h0' : ⟪a - c', b' - c⟫ = 0 := by rw [hbc, inner_smul_right, h0]; ring
        have := hF5 h0'
        rw [hAd, inner_smul_right] at this
        have h5 := (pos_iff_pos_of_mul_pos (show 0 < (β1 - 1) * ⟪c' - a, p⟫ from this)).1 hs
        have e5 : ⟪a - c', p⟫ = -⟪c' - a, p⟫ := by rw [← inner_neg_left, neg_sub]
        linarith
      · intro _ v1 v2 hv
        have := hv (⟪a - c', p⟫, ⟪a - c', q⟫) (by simp)
        simp only at this
        have e : ⟪a - c', fcomb p q r v1 v2 0⟫ = ⟪a - c', p⟫ * v1 + ⟪a - c', q⟫ * v2 := by
          simp only [fcomb, zero_smul, add_zero, inner_add_right, inner_smul_right]; ring
        rw [inner_sub_left] at e
        linarith
  have hZ : ∀ i, fpoint p q r d (k24h1lY α1 β1 β6 γ6 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k24h1lY_0, Eb']; simp [V8]
    · rw [k24h1lY_1, Ea]; simp [V8]
    · rw [k24h1lY_2, Ec']; simp [V8]
    · rw [k24h1lY_3, Ea']; simp [V8]
    · rw [k24h1lY_4, Ec]; simp [V8]
  refine ⟨r, hr0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) p q r d hΔ (k := 5) (by norm_num)
    (k24h1lY α1 β1 β6 γ6) (k24h1lY_inj hα1 hβ1 hβ6 hγ6) hZ
    ((0, 1) :: (-β6, -(α1 * (γ6 - 1))) :: E) (by simp) ?_ ?_ ?_
    (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro v1 v2 hC D hD i j h1 h2
    obtain ⟨hv2, hw, -⟩ := k24h1l_cone hC
    exact (k24h1l_tsc hD hα1 hβ1 hβ6 hγ6 hβB hv2 (by linarith)).1 i j h1 h2
  · intro y hy hyx
    have hV : y = fpoint p q r d (-α1, 0, β1) ∨ y = fpoint p q r d (β1 - 1, 0, 0) ∨
        y = fpoint p q r d (α1 * (β1 - 1), β1, 0) ∨ y = fpoint p q r d (-α1 * γ6, β6, γ6) ∨
        y = fpoint p q r d (-α1, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (0, 1, 0) := by
      rw [Eb', Ea, Ec', Ea', Ec, Ed, Eb]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone ((0, 1) :: (-β6, -(α1 * (γ6 - 1))) :: E) v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
          TSc D (k24h1lY α1 β1 β6 γ6 (i + 1) - k24h1lY α1 β1 β6 γ6 i) (t - k24h1lY α1 β1 β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      obtain ⟨hv2, hw, -⟩ := k24h1l_cone hC
      exact (k24h1l_tsc hD hα1 hβ1 hβ6 hγ6 hβB hv2 (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24h1lY_0])).elim
    · exact (hyx 1 (by rw [k24h1lY_1])).elim
    · exact (hyx 2 (by rw [k24h1lY_2])).elim
    · exact (hyx 3 (by rw [k24h1lY_3])).elim
    · exact (hyx 4 (by rw [k24h1lY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨hv2, hw', hCE⟩ := k24h1l_cone hC
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have hpt0 : fpoint p q r d (k24h1lY α1 β1 β6 γ6 0) = b' := by rw [k24h1lY_0, Eb']
    have hpt1 : fpoint p q r d (k24h1lY α1 β1 β6 γ6 1) = a := by rw [k24h1lY_1, Ea]
    have hpt2 : fpoint p q r d (k24h1lY α1 β1 β6 γ6 2) = c' := by rw [k24h1lY_2, Ec']
    have hpt3 : fpoint p q r d (k24h1lY α1 β1 β6 γ6 3) = a' := by rw [k24h1lY_3, Ea']
    have hpt4 : fpoint p q r d (k24h1lY α1 β1 β6 γ6 4) = c := by rw [k24h1lY_4, Ec]
    refine k19_lexUni_nb _ _ hw 0 ?_ ?_ ?_
    · simp only [e0, f0, hpt0, hpt4, hpt1]; left; exact hF2'
    · simp only [e0, f0, hpt0, hpt4, hpt1]; left; exact hF1'
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [e1, f1, hpt0, hpt1, hpt2]; left; left; exact hF1'
      · simp only [e2, f2, hpt1, hpt2, hpt3]
        rcases hF4'.lt_or_eq with h | h
        · left; left; exact h
        · left; right; exact ⟨h, hEex h v1 v2 hCE⟩
      · simp only [e3, f3, hpt2, hpt3, hpt4]; right; left; exact hF3'
      · simp only [e4, f4, hpt3, hpt4, hpt0]; right; left; exact hF2'
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | hl
    · right; simp
    · left; simp only [neg_mul, mul_neg, mul_one, mul_zero, add_zero, neg_neg]; linarith
    · exact hEray l hl

end C2
end Type08Sp
end Minimality
