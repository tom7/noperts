module

public import Minimality.Type08S.L2.K83A
public import Minimality.Type08S.C2K46ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option maxHeartbeats 2000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality
namespace Type08Sp
open C2

theorem k83_D1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hγ : 0 < γ6)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hD : ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0) :
    k28l2aU0 a b c d α1 β1 = 0 := by
  obtain ⟨hPR, -, -, -⟩ := k32e_facts hC hM
  obtain ⟨i1, i2, -⟩ := k83_Uip (α1 := α1) (β1 := β1) hPR
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  have e9 : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  rw [e9] at hz1
  simp only [inner_add_left, real_inner_smul_left] at hz1
  rw [real_inner_comm (k28l2aU0 a b c d α1 β1) (a - d), real_inner_comm (k28l2aU0 a b c d α1 β1) (b - d)] at hz1
  rw [i1, i2, hD] at hz1
  apply k83_U0zero hPR hD
  have : γ6 * ⟪k28l2aU0 a b c d α1 β1, c - d⟫ = 0 := by
    rw [real_inner_comm (k28l2aU0 a b c d α1 β1) (c - d)] at *
    linarith
  exact (mul_eq_zero.1 this).resolve_left hγ.ne'

theorem k83_reduce {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hne : ⟪c - a', a - b'⟫ ≠ 0) (h : K46LeftMN2 W) :
    ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧ K6sM a a' b b' c c' d ∧
      K16Rel a b c d α1 β1 ∧ 1 < α1 ∧ 1 < β1 ∧ 1 < β6 ∧ 1 < γ6 ∧ β1 < β6 + γ6 ∧
      ⟪a - c', a - b'⟫ ≤ 0 ∧ 0 ≤ ⟪c' - a, b' - c⟫ ∧ 0 ≤ ⟪c' - a', b' - c⟫ ∧
      (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) ≤ α1 + β1 - 1 ∧
      0 < ⟪a - c', d - a'⟫ ∧
      ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧
      ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫ ∧
      (β6 * (α1 - 1) = β1 * (γ6 - 1) ∨ k28l2aU0 a b c d α1 β1 = 0) := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, hH1, hL2, hK⟩ := h
  have hM := hs.2.2
  obtain ⟨hα, hβ, hσ, hβ6, hγ6⟩ := hH1.1
  have hrel : K16Rel a b c d α1 β1 := by
    obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
    exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ hγ6' h3
  have hX3 : ⟪a - c', a - b'⟫ ≤ 0 := by
    rcases hH1.2.2 with h0 | h0
    · exact (hne h0).elim
    · exact h0.2
  have hX4 : 0 ≤ ⟪c' - a, b' - c⟫ := hL2.1.2.1
  have hH : 0 ≤ ⟪c' - a', b' - c⟫ := hL2.1.2.2.1
  refine ⟨α1, β1, β6, γ6, hC, hM, hrel, hα, hβ, hβ6, hγ6, hσ, hX3, hX4, hH, hL2.1.1, hH1.2.1, ?_⟩
  have hU0 : k28l2aU0 a b c d α1 β1 = 0 →
      ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧
      ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫ ∧
      (β6 * (α1 - 1) = β1 * (γ6 - 1) ∨ k28l2aU0 a b c d α1 β1 = 0) := fun hu => by
    rw [hu]; simp
  have hI2 := k83_I2 hC hM
  have hγ0 : 0 < γ6 := by linarith
  -- from hz1, hz2 get the disjunction
  have hfin : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 →
      ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫ →
      (β6 * (α1 - 1) = β1 * (γ6 - 1) ∨ k28l2aU0 a b c d α1 β1 = 0) := by
    intro hz1 hz2
    by_cases hg : β6 * (α1 - 1) - β1 * (γ6 - 1) = 0
    · left; linarith
    · right
      have hz3 : ⟪c - a', k28l2aU0 a b c d α1 β1⟫ = 0 := by
        rw [inner_sub_left]; linarith
      rw [hz1, hz3] at hI2
      have hD : ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0 := by
        have : (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) *
            (β6 * (α1 - 1) - β1 * (γ6 - 1)) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hg
      exact k83_D1 hC hM hγ0 hz1 hD
  rcases hK with ⟨h3, h4⟩ | ⟨h4, hl, hz⟩ | ⟨hl, hz⟩
  · exact hU0 (k83_C1 hC hM hα hβ h3 h4)
  · rcases k41_c2_split hC hM hrel hH1 hL2 hne h4 hl with h3 | ⟨hlt, hHe⟩
    · exact hU0 (k83_C1 hC hM hα hβ h3 h4)
    · have hg := k83_r0_gWb W hs hC hH1 h4 hz hlt hHe
      have hz3 : ⟪c - a', k28l2aU0 a b c d α1 β1⟫ = 0 := by
        rw [hl] at hI2
        have : γ6 * ⟪c - a', k28l2aU0 a b c d α1 β1⟫ = 0 := by rw [hI2]; rw [hg]; ring
        exact (mul_eq_zero.1 this).resolve_left hγ0.ne'
      have hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫ := by
        rw [inner_sub_left] at hz3; linarith
      exact ⟨hl, hz2, Or.inl hg⟩
  · exact ⟨hl, hz, hfin hl hz⟩

end Type08Sp
end Minimality
