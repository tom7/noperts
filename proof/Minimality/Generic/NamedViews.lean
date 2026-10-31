module

public import Minimality.Generic.LimitSeq
public import Minimality.Generic.PairR2T

@[expose] public section

/-!
# Generic named views (covariance)

`namedView vtx` (`Type16Limit`): the segment directions and the vertex-crossing lines of a table
`vtx` of pairs of label triples.  Here: the family `x ↦ namedView vtx x v` is a covariant view
(continuous, equivariant under unimodular linear maps).  Types 16, 21 and 29 instantiate it.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts

/-- **The named views from a table of vertex crossings are covariant.** -/
theorem covView_namedView {k : ℕ}
    (vtx : Fin k → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7))
    (v : (Fin 7 × Fin 7) ⊕ Fin k) :
    CovView (fun y : Fin 7 → ℝ³ => namedView vtx y v) := by
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    exact tendsto_namedView vtx (fun m => (continuous_apply m).tendsto y) v
  · intro L y hL
    have hd : detMap L = 1 := by rw [detMap_eq_det]; exact hL
    rcases v with ⟨i, j⟩ | t
    · show L (y j) - L (y i) = L (y j - y i)
      rw [map_sub]
    · show planeLine (L (y _)) (L (y _)) (L (y _)) (L (y _)) (L (y _)) (L (y _)) = _
      rw [planeLine_map, hd, one_smul]
      rfl

end Minimality
