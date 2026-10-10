module

public import SmallRupert.L8Shapes

@[expose] public section

/-!
# Theorem 8.3: every T4 is Rupert
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **T4, combinatorial form** (LEMMAS.md L6/8.3): the quadrilateral facet
`A K₁ T K₂` (`K₁`, `K₂` of degree 3) and the triangles `K₁AC`, `K₁CT`,
`K₂AB`, `K₂BT`, `ABC`, `BCT`. -/
structure IsT4 (A B C T K₁ K₂ : ℝ³) : Prop where
  nodup : [A, B, C, T, K₁, K₂].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, T]
  quad : IsFacet {A, B, C, T, K₁, K₂} {A, K₁, T, K₂}
  facet_K₁AC : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ A C
  facet_K₁CT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ C T
  facet_K₂AB : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ A B
  facet_K₂BT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ B T
  facet_ABC : IsFacetTriangle {A, B, C, T, K₁, K₂} A B C
  facet_BCT : IsFacetTriangle {A, B, C, T, K₁, K₂} B C T

/-- The facet conditions put a T4 in normal form (as for Cor. 5.7, with the
quadrilateral facet making `A, T, K₁, K₂` coplanar: `β₁ γ₂ = c₁ b₂`). -/
theorem IsT4.exists_normalForm {A B C T K₁ K₂ : ℝ³} (h : IsT4 A B C T K₁ K₂) :
    ∃ a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ, 0 < a₁ ∧ 0 < β₁ ∧ 0 < c₁ ∧ 0 < t₁ ∧
      0 < a₂ ∧ 0 < b₂ ∧ 0 < γ₂ ∧ 0 < t₂ ∧
      a₁ - β₁ + c₁ + t₁ = 1 ∧ a₂ + b₂ - γ₂ + t₂ = 1 ∧ β₁ * γ₂ = c₁ * b₂ ∧
      K₁ = a₁ • A - β₁ • B + c₁ • C + t₁ • T ∧ K₂ = a₂ • A + b₂ • B - γ₂ • C + t₂ • T := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hAB, hAC, hAT, hAK₁, hAK₂⟩, ⟨hBC, hBT, hBK₁, hBK₂⟩, ⟨hCT, hCK₁, hCK₂⟩,
    ⟨hTK₁, hTK₂⟩, hK₁K₂, -⟩ := hnd
  obtain ⟨l1A, l1B, l1C, l1T, hs1, hK₁⟩ := exists_bary h.affineIndependent K₁
  obtain ⟨l2A, l2B, l2C, l2T, hs2, hK₂⟩ := exists_bary h.affineIndependent K₂
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₁ ▸ affine_apply_comb4 f hs1 :
    f K₁ = l1A * f A + l1B * f B + l1C * f C + l1T * f T)
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₂ ▸ affine_apply_comb4 f hs2 :
    f K₂ = l2A * f A + l2B * f B + l2C * f C + l2T * f T)
  obtain ⟨f, fB, fC, fT, hf⟩ := h.facet_BCT
  have fA := hf A (by simp) hAB hAC hAT
  have fK₁ := hf K₁ (by simp) (Ne.symm hBK₁) (Ne.symm hCK₁) (Ne.symm hTK₁)
  have fK₂ := hf K₂ (by simp) (Ne.symm hBK₂) (Ne.symm hCK₂) (Ne.symm hTK₂)
  rw [ev1, fB, fC, fT] at fK₁
  rw [ev2, fB, fC, fT] at fK₂
  simp only [mul_zero, add_zero] at fK₁ fK₂
  have h1A : 0 < l1A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  have h2A : 0 < l2A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  obtain ⟨g, gA, gB, gC, hg⟩ := h.facet_ABC
  have gT := hg T (by simp) (Ne.symm hAT) (Ne.symm hBT) (Ne.symm hCT)
  have gK₁ := hg K₁ (by simp) (Ne.symm hAK₁) (Ne.symm hBK₁) (Ne.symm hCK₁)
  have gK₂ := hg K₂ (by simp) (Ne.symm hAK₂) (Ne.symm hBK₂) (Ne.symm hCK₂)
  rw [ev1, gA, gB, gC] at gK₁
  rw [ev2, gA, gB, gC] at gK₂
  simp only [mul_zero, zero_add] at gK₁ gK₂
  have h1T : 0 < l1T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  have h2T : 0 < l2T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  obtain ⟨hh, hhK, hhA, hhC, hhx⟩ := h.facet_K₁AC
  have hhB := hhx B (by simp) hBK₁ (Ne.symm hAB) hBC
  have hhT := hhx T (by simp) hTK₁ (Ne.symm hAT) (Ne.symm hCT)
  have e := ev1 hh
  rw [hhK, hhA, hhC] at e
  simp only [mul_zero, zero_add, add_zero] at e
  have h1B : l1B < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc hhB.le, mul_neg_of_pos_of_neg h1T hhT]
  obtain ⟨m, mK, mA, mB, hm⟩ := h.facet_K₂AB
  have mC := hm C (by simp) hCK₂ (Ne.symm hAC) (Ne.symm hBC)
  have mT := hm T (by simp) hTK₂ (Ne.symm hAT) (Ne.symm hBT)
  have e2 := ev2 m
  rw [mK, mA, mB] at e2
  simp only [mul_zero, zero_add, add_zero] at e2
  have h2C : l2C < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc mC.le, mul_neg_of_pos_of_neg h2T mT]
  -- the quadrilateral facet `A K₁ T K₂`
  obtain ⟨q, hq0, hq⟩ := h.quad
  have qA := hq0 A (by simp)
  have qK₁ := hq0 K₁ (by simp)
  have qT := hq0 T (by simp)
  have qK₂ := hq0 K₂ (by simp)
  have qB := hq B (by simp) (by simp [Ne.symm hAB, hBK₁, hBT, hBK₂])
  have qC := hq C (by simp) (by simp [Ne.symm hAC, hCK₁, hCT, hCK₂])
  rw [ev1, qA, qT] at qK₁
  rw [ev2, qA, qT] at qK₂
  simp only [mul_zero, zero_add, add_zero] at qK₁ qK₂
  have h1C : 0 < l1C := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos_of_neg_of_neg h1B qB, mul_nonneg_of_nonpos_of_nonpos hc qC.le]
  have h2B : 0 < l2B := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos_of_neg_of_neg h2C qC, mul_nonneg_of_nonpos_of_nonpos hc qB.le]
  have hcop : l1B * l2C = l1C * l2B := by
    have h1 : l1B * q B = -(l1C * q C) := by linarith
    have h2 : l2B * q B = -(l2C * q C) := by linarith
    have hqB : q B ≠ 0 := qB.ne
    have : (l1B * l2C - l1C * l2B) * q B = 0 := by linear_combination l2C * h1 - l1C * h2
    have := (mul_eq_zero.mp this).resolve_right hqB
    linarith
  refine ⟨l1A, -l1B, l1C, l1T, l2A, l2B, -l2C, l2T, h1A, by linarith, h1C, h1T, h2A, h2B,
    by linarith, h2T, by linarith, by linarith, by linear_combination hcop, ?_, ?_⟩
  · rw [hK₁]; module
  · rw [hK₂]; module

/-- **Theorem 8.3.**  Every T4 is Rupert. -/
theorem isRupert_T4 {A B C T K₁ K₂ : ℝ³} (h : IsT4 A B C T K₁ K₂) :
    IsRupert {A, B, C, T, K₁, K₂} := by
  sorry

end SmallRupert

end
