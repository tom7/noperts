module

public import SmallRupert.Coplanar

@[expose] public section

/-!
# Corollary 5.7: every bicapped tetrahedron is Rupert

`isRupert_bicap_normalForm` is the computational core: in barycentric
coordinates with respect to the tetrahedron `(A, B, C, T)`,
`K₁ = (a₁, -β₁, c₁, t₁)` and `K₂ = (a₂, b₂, -γ₂, t₂)` with all eight letters
positive, and convexity at the edge `AT` reads `β₁ γ₂ < c₁ b₂`.  Then
`U_ACT ≠ ∅` when `γ₂ < b₂` and `U_ABT ≠ ∅` otherwise (since `xy > 1`).

`isRupert_bicappedTetrahedron` is the combinatorial statement: the six points
have the eight facets `K₁AC, K₁CT, K₁TA, K₂AB, K₂BT, K₂TA, ABC, BCT`
(`IsFacetTriangle`: a supporting plane through the three points with the
other points strictly on one side).  It reduces to the normal form by
reading the barycentric signs off the facet inequalities (LEMMAS.md's use of
Lemma 5.5).  Numerically, 49/49 random normal-form samples satisfy all eight
facet conditions, and 300 samples agree with the `U_ACT`/`U_ABT` criterion.
-/

namespace SmallRupert

/-- `P Q R` lies on a facet of `conv V`: an affine functional vanishes at
`P`, `Q`, `R` and is negative at every other point of `V`. -/
def IsFacetTriangle (V : Finset ℝ³) (P Q R : ℝ³) : Prop :=
  ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f P = 0 ∧ f Q = 0 ∧ f R = 0 ∧
    ∀ x ∈ V, x ≠ P → x ≠ Q → x ≠ R → f x < 0

/-- The six points form a bicapped tetrahedron with caps `K₁` (over the
face `ACT` of `ABCT`) and `K₂` (over `ABT`), LEMMAS.md's labelling. -/
structure IsBicappedTetrahedron (A B C T K₁ K₂ : ℝ³) : Prop where
  nodup : [A, B, C, T, K₁, K₂].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, T]
  facet_K₁AC : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ A C
  facet_K₁CT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ C T
  facet_K₁TA : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ T A
  facet_K₂AB : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ A B
  facet_K₂BT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ B T
  facet_K₂TA : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ T A
  facet_ABC : IsFacetTriangle {A, B, C, T, K₁, K₂} A B C
  facet_BCT : IsFacetTriangle {A, B, C, T, K₁, K₂} B C T

/-- **Corollary 5.7, normal form.** -/
theorem isRupert_bicap_normalForm (A B C T : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (ha₂ : 0 < a₂) (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : a₂ + b₂ - γ₂ + t₂ = 1)
    (hAT : β₁ * γ₂ < c₁ * b₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T,
      a₂ • A + b₂ • B - γ₂ • C + t₂ • T} := by
  sorry

/-- The facet conditions put a bicapped tetrahedron in normal form. -/
theorem IsBicappedTetrahedron.exists_normalForm {A B C T K₁ K₂ : ℝ³}
    (h : IsBicappedTetrahedron A B C T K₁ K₂) :
    ∃ a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ, 0 < a₁ ∧ 0 < β₁ ∧ 0 < c₁ ∧ 0 < t₁ ∧
      0 < a₂ ∧ 0 < b₂ ∧ 0 < γ₂ ∧ 0 < t₂ ∧
      a₁ - β₁ + c₁ + t₁ = 1 ∧ a₂ + b₂ - γ₂ + t₂ = 1 ∧ β₁ * γ₂ < c₁ * b₂ ∧
      K₁ = a₁ • A - β₁ • B + c₁ • C + t₁ • T ∧ K₂ = a₂ • A + b₂ • B - γ₂ • C + t₂ • T := by
  sorry

/-- **Corollary 5.7.** Every bicapped tetrahedron is Rupert. -/
theorem isRupert_bicappedTetrahedron {A B C T K₁ K₂ : ℝ³}
    (h : IsBicappedTetrahedron A B C T K₁ K₂) : IsRupert {A, B, C, T, K₁, K₂} := by
  obtain ⟨a₁, β₁, c₁, t₁, a₂, b₂, γ₂, t₂, ha₁, hβ₁, hc₁, ht₁, ha₂, hb₂, hγ₂, ht₂,
    hs₁, hs₂, hAT, rfl, rfl⟩ := h.exists_normalForm
  exact isRupert_bicap_normalForm A B C T h.affineIndependent a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂
    ha₁ hβ₁ hc₁ ht₁ ha₂ hb₂ hγ₂ ht₂ hs₁ hs₂ hAT

end SmallRupert

end
