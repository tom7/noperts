module

public import Minimality.Type24HoleReduce
public import Minimality.SplitEdgePlane
public import Minimality.EdgeViewLink

/-!
# `HoleLeaf` without the `SplitAny` conjunct

Merge Hydrogen Task EV (Carbon A71 Theorem 1.1).  `Gen.splitAny_edgePlaneAny` (SplitEdgePlane.lean)
says that every generic split view yields an Edge-Plane view, so the `SplitAny` conjunct of
`HoleLeaf` is redundant.  Leaf lattice arrow: `SplitAny => EdgePlaneAny`.
`HoleLeaf` itself is unchanged.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0

namespace Minimality.T24

private theorem s24_sep' :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- `HoleLeaf` without the redundant `SplitAny` conjunct. -/
def HoleLeafMin (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ ¬ FacetCellF F ∧ ¬ Gen.AnyFaceChord F ∧ ¬ Gen.LexAny F ∧
    ¬ BoxApplies (Finset.univ.image x) ∧ ¬ Gen.EdgePlaneAny x

/-- The `SplitAny` conjunct of `HoleLeaf` is redundant (it implies `EdgePlaneAny`). -/
theorem holeLeaf_iff_min (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    HoleLeaf x F ↔ HoleLeafMin x F := by
  constructor
  · rintro ⟨h1, h2, h3, h4, _, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h6, h7⟩
    exact ⟨h1, h2, h3, h4,
      fun hs => h7 (Gen.splitAny_edgePlaneAny F (EdgeViewLink.inj_of_fac24 F) s24_sep' hs), h6, h7⟩

end Minimality.T24
