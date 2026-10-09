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

/-- **T1, concurrent lateral lines (frustum).**  `A' = O + α (A - O)` etc.
with `α, β, γ ∈ (0, 1)`: view from `O` through the big triangle `ABC`. -/
theorem isRupert_frustum (A B C O : ℝ³) (hABC : ¬ Collinear ℝ ({A, B, C} : Set ℝ³))
    (hO : O ∉ affineSpan ℝ ({A, B, C} : Set ℝ³)) (α β γ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    IsRupert {A, B, C, O + α • (A - O), O + β • (B - O), O + γ • (C - O)} := by
  sorry

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
