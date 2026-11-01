module

public import Minimality.Type08S.C2K5sG

@[expose] public section

/-!
# K5s / H: `S4TRK2` on `s = 0` has a lex cell, except `B' > 0 ∧ ⟪a' - b, b - d⟫ = 0 ∧ 0 ≤ ⟪a' - b, c - d⟫`
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5_delta (g P Q : ℝ) (hg : 0 < g) (hP : 0 < P) (hQ : 0 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ δ * Q < g ∧ δ * g < P := by
  refine ⟨min (g / (2 * (Q + 1))) (P / (2 * (g + 1))), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have h1 : min (g / (2 * (Q + 1))) (P / (2 * (g + 1))) ≤ g / (2 * (Q + 1)) := min_le_left _ _
    have h2 : g / (2 * (Q + 1)) * (Q + 1) = g / 2 := by field_simp
    have h3 : 0 < min (g / (2 * (Q + 1))) (P / (2 * (g + 1))) := lt_min (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ Q + 1)]
  · have h1 : min (g / (2 * (Q + 1))) (P / (2 * (g + 1))) ≤ P / (2 * (g + 1)) := min_le_right _ _
    have h2 : P / (2 * (g + 1)) * (g + 1) = P / 2 := by field_simp
    have h3 : 0 < min (g / (2 * (Q + 1))) (P / (2 * (g + 1))) := lt_min (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ g + 1)]

theorem k5_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : S4TRK2 a a' b b' c c' d)
    (hs : ⟪a' - b, a - d⟫ = 0)
    (hres : ¬ (0 < ⟪a - d, b - d⟫ ∧ ⟪a' - b, b - d⟫ = 0 ∧ 0 ≤ ⟪a' - b, c - d⟫)) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT, hL, hγ⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have eA : det3 (c - b') (a - d) (b - d) = -(1 - γ4) * D := by
    rw [hb']; simp only [hD, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hγ41 : γ4 = 1 := by
    have := (mul_eq_zero.mp (by rw [← eA]; exact hγ : -(1 - γ4) * D = 0)).resolve_right hD0
    linarith
  subst hγ41
  have hβ11 : β1 < 1 := by nlinarith
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hΔ : det3 p q r ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 p q r := by simp only [hp, hq, hr, det3_expand]; ring
    rw [e, h]
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hB : 0 ≤ ⟪a - d, b - d⟫ := by
    have ha1 : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) := by rw [ha', one_smul]
    refine k1_B_nonneg hp0 hc' hb' ha1 hα4 hβ6 ?_
    rcases hL with ⟨hK, hN, -, -⟩ | ⟨hK, hX, -, hE', -, -⟩
    · exact Or.inl ⟨hK, hN⟩
    · exact Or.inr ⟨hK, hX, hE'⟩
  have hBp : 0 ≤ ⟪p, r⟫ := by rw [real_inner_comm]; exact hB
  have hEq : ⟪c', b - d⟫ = ⟪b', b - d⟫ := by
    rcases hL with ⟨hK, hN, -, -⟩ | ⟨hK, hX, -, hE', -, -⟩
    · exact hN.2.1.symm
    · exact hE'
  have es : ⟪a' - b, a - d⟫ = (β6 - 1) * ⟪p, r⟫ + ⟪q, r⟫ := by
    have : a' - b = (β6 - 1) • (b - d) + (c - d) := by rw [ha']; module
    rw [this, inner_add_left, real_inner_smul_left]
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint p q r d (1, 0, 0) = b := by simp only [fpoint, fcomb, hp]; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq]; module
  have eA1 : fpoint p q r d (0, 0, 1) = a := by simp only [fpoint, fcomb, hr]; module
  have eA' : fpoint p q r d (β6, 1, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eC' : fpoint p q r d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, 1, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, 1, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (β1, 0, α1) := by
    intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl eO.symm)
    · exact Or.inl eA1.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl eA'.symm)))
    · exact Or.inr (Or.inr (Or.inl eB.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eB'.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eC.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eC'.symm)))))
  have hne : a - d ≠ 0 := by
    intro had; apply hdet
    have h0 : r = 0 := had
    rw [h0]; simp [det3_expand]
  refine ⟨a - d, hne, ?_⟩
  have hf : a' - b = (β6 - 1) • p + q := by rw [ha']; module
  have hs' : (β6 - 1) * ⟪p, r⟫ + ⟪q, r⟫ = 0 := by rw [← es]; exact hs
  rcases hBp.lt_or_eq with hB' | hB0
  · have hres' : ¬ (⟪(β6 - 1) • p + q, p⟫ = 0 ∧ 0 ≤ ⟪(β6 - 1) • p + q, q⟫) := by
      rw [← hf]; intro hh
      exact hres ⟨by rw [real_inner_comm]; exact hB', hh⟩
    have hf : a' - b = (β6 - 1) • p + q := by rw [ha']; module
    by_cases hX1 : ⟪(β6 - 1) • p + q, p⟫ < 0 ∨ ⟪(β6 - 1) • p + q, q⟫ < 0
    · obtain ⟨u1, u2, t1, t2, h1, h2, h3, h4, h5, h6, h7⟩ := k5_tilt1 _ _ hX1
      refine k5x1_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (lt_trans one_pos hα1) hβ1 hβ11 hα4 hβ6 hB'
        h1 h2 h3 h4 h5 (Or.inr ⟨hs', h6, h7⟩) ?_ hVall
      intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k1Cyc, pc5_0, eO]; simp [V8]
      · simp only [k1Cyc, pc5_1, eB]; simp [V8]
      · simp only [k1Cyc, pc5_2, eA']; simp [V8]
      · simp only [k1Cyc, pc5_3, eB']; simp [V8]
      · simp only [k1Cyc, pc5_4, eC]; simp [V8]
    · have hx0 : 0 < ⟪(β6 - 1) • p + q, p⟫ := by
        push_neg at hX1
        rcases hX1.1.lt_or_eq with h | h
        · exact h
        · exact absurd ⟨h.symm, hX1.2⟩ hres'
      obtain ⟨u1, u2, t1, t2, h1, h2, h3, h4, h5, h6, h7⟩ := k5_tilt2 _ _ (Or.inl hx0)
      refine k5x2_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα1 hβ1 hβ11 hα4 hβ6 hB'
        h1 h2 h3 h4 h5 (Or.inr ⟨hs', h6, h7⟩) ?_ hVall
      intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k1Cyc6, six_0, eA1]; simp [V8]
      · simp only [k1Cyc6, six_1, eC']; simp [V8]
      · simp only [k1Cyc6, six_2, eB]; simp [V8]
      · simp only [k1Cyc6, six_3, eA']; simp [V8]
      · simp only [k1Cyc6, six_4, eC]; simp [V8]
      · simp only [k1Cyc6, six_5, eO]; simp [V8]


  · -- B' = 0, hence C' = 0 and D_c = β1 |p|^2 > 0
    have hB0' : ⟪p, r⟫ = 0 := hB0.symm
    have hC0 : ⟪q, r⟫ = 0 := by rw [hB0', mul_zero, zero_add] at hs'; exact hs'
    have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
    have hg : 0 < ⟪p, q⟫ := by
      have e1 : ⟪c', p⟫ = ⟪d, p⟫ + α1 * ⟪r, p⟫ + β1 * ⟪p, p⟫ := by
        rw [hc']; simp only [inner_add_left, real_inner_smul_left] <;> ring
      have e2 : ⟪b', p⟫ = ⟪d, p⟫ + α4 * ⟪r, p⟫ + ⟪q, p⟫ := by
        rw [hb']; simp only [inner_add_left, real_inner_smul_left] <;> ring
      have hrp : ⟪r, p⟫ = 0 := by rw [real_inner_comm]; exact hB0'
      have : ⟪c', p⟫ = ⟪b', p⟫ := hEq
      rw [e1, e2, hrp] at this
      have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
      nlinarith [mul_pos hβ1 hpp]
    obtain ⟨δ, hδ, hδ1, hδ2⟩ := k5_delta _ _ _ hg hpp (real_inner_self_nonneg (x := q))
    refine k5x2z_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα1 hβ1 hβ11 hα4 hβ6 hB0' hC0 hδ hδ1 hδ2 hg ?_ hVall
    intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k1Cyc6, six_0, eA1]; simp [V8]
    · simp only [k1Cyc6, six_1, eC']; simp [V8]
    · simp only [k1Cyc6, six_2, eB]; simp [V8]
    · simp only [k1Cyc6, six_3, eA']; simp [V8]
    · simp only [k1Cyc6, six_4, eC]; simp [V8]
    · simp only [k1Cyc6, six_5, eO]; simp [V8]

end C2
end Type08Sp
end Minimality
