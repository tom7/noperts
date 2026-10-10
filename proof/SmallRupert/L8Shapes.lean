module

public import SmallRupert.Tilt

@[expose] public section

/-!
# Theorems 8.2–8.4: every T5, T4 and T3 is Rupert

Each shape is given by its facet structure (as for T5 in `SixVertices.lean`).
The views are tilted off a direction parallel to an edge or face
(Lemma 8.0); one of two or three predicted 4-cycles (or a 5-cycle) is robustly
unimodal, and Corollary 8.0′ (with Theorem 7.5) gives the passage.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Theorem 8.2.**  Every T5 (capped square pyramid) is Rupert, including the
L6 exceptions `S₁S₄ ∥ S₂S₃`. -/
theorem isRupert_cappedSquarePyramid_all {E S₁ S₂ S₃ S₄ K : ℝ³}
    (h : IsCappedSquarePyramid E S₁ S₂ S₃ S₄ K) : IsRupert {E, S₁, S₂, S₃, S₄, K} := by
  sorry

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

/-- **Theorem 8.3.**  Every T4 is Rupert. -/
theorem isRupert_T4 {A B C T K₁ K₂ : ℝ³} (h : IsT4 A B C T K₁ K₂) :
    IsRupert {A, B, C, T, K₁, K₂} := by
  sorry

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

/-- **Theorem 8.4.**  Every T3 is Rupert. -/
theorem isRupert_T3 {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    IsRupert {A, B, C, A', B', C'} := by
  sorry

end SmallRupert

end
