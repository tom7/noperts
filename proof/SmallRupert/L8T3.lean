module

public import SmallRupert.L8Shapes

@[expose] public section

/-!
# Theorem 8.4: every T3 is Rupert
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **T3 (tetragonal antiwedge), combinatorial form** (LEMMAS.md 8.4): the
quadrilateral facets `A C C' A'` and `B C C' B'`, and the triangles `ABC`,
`A'B'C'`, `ABB'`, `AB'A'` (the bent quad `ABB'A'` with diagonal `AB'`). -/
structure IsT3 (A B C A' B' C' : ℝ³) : Prop where
  nodup : [A, B, C, A', B', C'].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, C']
  quad₁ : IsFacet {A, B, C, A', B', C'} {A, C, C', A'}
  quad₂ : IsFacet {A, B, C, A', B', C'} {B, C, C', B'}
  facet_ABC : IsFacetTriangle {A, B, C, A', B', C'} A B C
  facet_A'B'C' : IsFacetTriangle {A, B, C, A', B', C'} A' B' C'
  facet_ABB' : IsFacetTriangle {A, B, C, A', B', C'} A B B'
  facet_AB'A' : IsFacetTriangle {A, B, C, A', B', C'} A B' A'

/-- The facet conditions put a T3 in normal form, in the frame
`(A - C, B - C, C' - C)`: `A' = (α, 0, α')`, `B' = (0, β, β')` with the convex
quads (`α + α' > 1`, `β + β' > 1`) and the bent quad `ABB'A'` with diagonal
`AB'` (`α' (1 - β) < β' (1 - α)`). -/
theorem IsT3.exists_normalForm {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    ∃ α α' β β' : ℝ, 0 < α ∧ 0 < α' ∧ 0 < β ∧ 0 < β' ∧ 1 < α + α' ∧ 1 < β + β' ∧
      α' * (1 - β) < β' * (1 - α) ∧
      A' = C + cmb (A - C) (B - C) (C' - C) α 0 α' ∧
      B' = C + cmb (A - C) (B - C) (C' - C) 0 β β' := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hAB, hAC, hAA', hAB', hAC'⟩, ⟨hBC, hBA', hBB', hBC'⟩, ⟨hCA', hCB', hCC'⟩,
    ⟨hA'B', hA'C'⟩, hB'C', -⟩ := hnd
  obtain ⟨lA, lB, lC, lC', hs1, hA'⟩ := exists_bary h.affineIndependent A'
  obtain ⟨mA, mB, mC, mC', hs2, hB'⟩ := exists_bary h.affineIndependent B'
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hA' ▸ affine_apply_comb4 f hs1 :
    f A' = lA * f A + lB * f B + lC * f C + lC' * f C')
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hB' ▸ affine_apply_comb4 f hs2 :
    f B' = mA * f A + mB * f B + mC * f C + mC' * f C')
  -- the quads
  obtain ⟨q₁, hq₁0, hq₁⟩ := h.quad₁
  have q₁A := hq₁0 A (by simp)
  have q₁C := hq₁0 C (by simp)
  have q₁C' := hq₁0 C' (by simp)
  have q₁A' := hq₁0 A' (by simp)
  have q₁B := hq₁ B (by simp) (by simp [Ne.symm hAB, hBC, hBC', hBA'])
  have q₁B' := hq₁ B' (by simp) (by simp [Ne.symm hAB', Ne.symm hCB', hB'C', Ne.symm hA'B'])
  obtain ⟨q₂, hq₂0, hq₂⟩ := h.quad₂
  have q₂B := hq₂0 B (by simp)
  have q₂C := hq₂0 C (by simp)
  have q₂C' := hq₂0 C' (by simp)
  have q₂B' := hq₂0 B' (by simp)
  have q₂A := hq₂ A (by simp) (by simp [hAB, hAC, hAC', hAB'])
  have q₂A' := hq₂ A' (by simp) (by simp [Ne.symm hBA', Ne.symm hCA', hA'C', hA'B'])
  have e1 := ev1 q₁
  rw [q₁A', q₁A, q₁C, q₁C'] at e1
  have hlB : lB = 0 := by
    have : lB * q₁ B = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right q₁B.ne
  have e2 := ev2 q₂
  rw [q₂B', q₂B, q₂C, q₂C'] at e2
  have hmA : mA = 0 := by
    have : mA * q₂ A = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right q₂A.ne
  have e3 := ev1 q₂
  rw [q₂B, q₂C, q₂C'] at e3
  have hα : 0 < lA := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hc q₂A.le]
  have e4 := ev2 q₁
  rw [q₁A, q₁C, q₁C'] at e4
  have hβ : 0 < mB := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hc q₁B.le]
  -- the triangle `ABC`
  obtain ⟨g, gA, gB, gC, hg⟩ := h.facet_ABC
  have gC' := hg C' (by simp) (Ne.symm hAC') (Ne.symm hBC') (Ne.symm hCC')
  have gA' := hg A' (by simp) (Ne.symm hAA') (Ne.symm hBA') (Ne.symm hCA')
  have gB' := hg B' (by simp) (Ne.symm hAB') (Ne.symm hBB') (Ne.symm hCB')
  rw [ev1, gA, gB, gC] at gA'
  rw [ev2, gA, gB, gC] at gB'
  have hα' : 0 < lC' := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hc gC'.le]
  have hβ' : 0 < mC' := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hc gC'.le]
  -- the bent quad `ABB'A'`
  obtain ⟨k, kA, kB, kB', hk⟩ := h.facet_ABB'
  have kC := hk C (by simp) (Ne.symm hAC) (Ne.symm hBC) hCB'
  have kC' := hk C' (by simp) (Ne.symm hAC') (Ne.symm hBC') (Ne.symm hB'C')
  have kA' := hk A' (by simp) (Ne.symm hAA') (Ne.symm hBA') hA'B'
  rw [ev2, kA, kB] at kB'
  rw [ev1, kA, kB] at kA'
  obtain ⟨n, nA, nB', nA', hn⟩ := h.facet_AB'A'
  have nC := hn C (by simp) (Ne.symm hAC) hCB' hCA'
  have nC' := hn C' (by simp) (Ne.symm hAC') (Ne.symm hB'C') (Ne.symm hA'C')
  rw [ev1, nA] at nA'
  have hmC : mC = 1 - mB - mC' := by linarith
  have hlC : lC = 1 - lA - lC' := by linarith
  have hB0 : mC * k C + mC' * k C' = 0 := by linarith
  have hA0 : lC * k C + lC' * k C' < 0 := by linarith
  have hN0 : lC * n C + lC' * n C' = 0 := by rw [hlB] at nA'; linarith
  have hbb : 1 < mB + mC' := by
    have h1 : mC' * k C' < 0 := mul_neg_of_pos_of_neg hβ' kC'
    have h2 : 0 < mC * k C := by linarith
    have h3 : mC < 0 := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hc kC.le]
    linarith
  have haa : 1 < lA + lC' := by
    have h1 : lC' * n C' < 0 := mul_neg_of_pos_of_neg hα' nC'
    have h2 : 0 < lC * n C := by linarith
    have h3 : lC < 0 := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hc nC.le]
    linarith
  have hbent : lC' * (1 - mB) < mC' * (1 - lA) := by
    have h1 : mC' * (lC * k C + lC' * k C') < 0 := mul_neg_of_pos_of_neg hβ' hA0
    have h2 : k C * (mC' * lC - lC' * mC) < 0 := by linear_combination h1 - lC' * hB0
    have h3 : 0 < mC' * lC - lC' * mC := by
      by_contra hc; push Not at hc
      linarith [mul_nonneg_of_nonpos_of_nonpos kC.le hc]
    rw [hmC, hlC] at h3; linarith
  refine ⟨lA, lC', mB, mC', hα, hα', hβ, hβ', haa, hbb, hbent, ?_, ?_⟩
  · rw [hA', hlB, hlC]; simp only [cmb]; module
  · rw [hB', hmA, hmC]; simp only [cmb]; module

/-- **Theorem 8.4.**  Every T3 is Rupert. -/
theorem isRupert_T3 {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    IsRupert {A, B, C, A', B', C'} := by
  sorry

end SmallRupert

end
