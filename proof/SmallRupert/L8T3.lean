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

/-- **Theorem 8.4.**  Every T3 is Rupert. -/
theorem isRupert_T3 {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    IsRupert {A, B, C, A', B', C'} := by
  sorry

end SmallRupert

end
