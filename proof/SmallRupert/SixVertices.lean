module

public import SmallRupert.BicappedTetrahedron
public import SmallRupert.Crossing

@[expose] public section

/-!
# L6 (partial): six-vertex types covered by the coplanar-silhouette theorem

* T2, pentagonal pyramids: `isRupert_of_pyramid`.
* T7, bicapped tetrahedra: `isRupert_bicappedTetrahedron`.
* T1, triangular prisms whose lateral lines meet (`isRupert_frustum`), and
  prisms with parallel lateral edges not all of the same length
  (`isRupert_parallelPrism`).  Translation prisms `T + [0, w]` are open.
* T5 (capped square pyramid) in normal form, unless `S₁S₄ ∥ S₂S₃`
  (`isRupert_cappedSquarePyramid_normalForm`).
* T3, T4, T6: not covered in general (LEMMAS.md L6); nothing stated.
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- **T1, concurrent lateral lines (frustum).**  A triangular prism whose
three lateral lines meet at a point `O` (LEMMAS.md L6, first T1 case): the
small end is `A' = O + α (A - O)` etc. with `α, β, γ ∈ (0, 1)`, and `OABC` is
a nondegenerate tetrahedron.  View from `O` through the centroid of the big
end `ABC`. -/
theorem isRupert_frustum (A B C O : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, O]) (α β γ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    IsRupert {A, B, C, O + α • (A - O), O + β • (B - O), O + γ • (C - O)} := by
  classical
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdet : det4 A B C O ≠ 0 := fun h0 =>
    not_coplanar_of_affineIndependent hind (coplanar_of_det4_eq_zero h0)
  set N := cross (B - A) (C - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by simp [det4, ← hNdef, h0])
  have hind3 : AffineIndependent ℝ ![A, B, C] := affineIndependent_of_cross_ne_zero hN
  have hinj := hind3.injective
  have hAB : A ≠ B := fun h => by have := @hinj 0 1 (by simp [h]); exact absurd this (by decide)
  have hAC : A ≠ C := fun h => by have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hBC : B ≠ C := fun h => by have := @hinj 1 2 (by simp [h]); exact absurd this (by decide)
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNC : ⟪N, C⟫ = c := by
    have := inner_cross_right (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, B, C} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNB
    · exact hNC
  set G := (1 / 3 : ℝ) • A + (1 / 3 : ℝ) • B + (1 / 3 : ℝ) • C
  have hNG : ⟪N, G⟫ = c := by
    simp only [G, inner_add_right, real_inner_smul_right, hNB, hNC, ← hc]; ring
  have hu₀ : ⟪N, G - O⟫ ≠ 0 := by
    rw [inner_sub_right, hNG]
    intro h0; apply hdet
    simp only [det4, ← hNdef, inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, C} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hind3 (G - O) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact absurd rfl hvW.2.2
  · exact exists_weights3 hAB hAC hBC (t := 1 - α) (α := α + (1 - α) / 3)
      (β := (1 - α) / 3) (γ := (1 - α) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - β) (α := (1 - β) / 3)
      (β := β + (1 - β) / 3) (γ := (1 - β) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - γ) (α := (1 - γ) / 3)
      (β := (1 - γ) / 3) (γ := γ + (1 - γ) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)

/-- **T1, parallel lateral edges of unequal lengths.**  `A' = A + s_A w` etc.
with `s_A, s_B, s_C > 0` not all equal: view through a lateral quadrilateral
whose opposite lateral edge is shorter than the longer of its two. -/
theorem isRupert_parallelPrism (A B C w : ℝ³) (hABC : ¬ Collinear ℝ ({A, B, C} : Set ℝ³))
    (hw : w ∉ (affineSpan ℝ ({A, B, C} : Set ℝ³)).direction) (sA sB sC : ℝ)
    (hA : 0 < sA) (hB : 0 < sB) (hC : 0 < sC) (hne : ¬ (sA = sB ∧ sB = sC)) :
    IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
  sorry

/-- **T5 in normal form.**  `(A, B, C, T) = (E, S₃, S₂, S₁)`, the cap
`K = (a₁, -β₁, c₁, t₁)` and `S₄ = (0, b₂, -γ₂, t₂)` in barycentrics, convexity
at `ES₁`: `β₁ γ₂ < c₁ b₂`.  If `γ₂ ≠ b₂` (i.e. `S₁S₄ ∦ S₂S₃`), the view
through `ES₁S₂` (`γ₂ < b₂`) or through `ES₃S₄` (`γ₂ > b₂`) is admissible. -/
theorem isRupert_cappedSquarePyramid_normalForm (A B C T : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : b₂ - γ₂ + t₂ = 1)
    (hconv : β₁ * γ₂ < c₁ * b₂) (hpar : γ₂ ≠ b₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T, b₂ • B - γ₂ • C + t₂ • T} := by
  sorry

end SmallRupert

end
