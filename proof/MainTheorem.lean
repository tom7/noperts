module

public import Mathlib.LinearAlgebra.AffineSpace.Dimension
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
This file states the main theorem using only Mathlib imports, following the conventions
proposed on Zulip here:
https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs/near/556956066

See also the Formal Conjectures version of the theorem statement:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/Rupert.lean
-/

@[expose] public section

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def proj_xy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a finite set of vertices. -/
def IsRupert (vertices : Finset ℝ³) : Prop :=
   ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
   ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

/--
There exists a nontrivial convex polyhedron with seven vertices that does not have the Rupert Property.
-/
def ExistsNonRupertPolyhedronSizeSeven : Prop :=
  ∃ vs : Finset ℝ³,
    vs.card ≤ 7 ∧
    (interior (convexHull ℝ vs : Set ℝ³)).Nonempty ∧
    ¬IsRupert vs

/--
There does not exist a nontrivial convex polyhedron with fewer than seven vertices that does not have the Rupert Property.
-/
def NotExistsNonRupertPolyhedronBelowSizeSeven : Prop :=
  ¬∃ vs : Finset ℝ³,
    vs.card < 7 ∧
    (interior (convexHull ℝ vs : Set ℝ³)).Nonempty ∧
    ¬IsRupert vs

/--
Seven vertices is the smallest Nopert
-/
def MinimalNopert : Prop :=
  ExistsNonRupertPolyhedronSizeSeven ∧ NotExistsNonRupertPolyhedronBelowSizeSeven

/--
Every 7-vertex nopert is simplicial (all triangular faces).
(Still open!)
-/
def AnySevenVertexNopertIsSimplicial : Prop :=
   ∀ vs : Finset ℝ³,
     vs.card ≤ 7 →
     (interior (convexHull ℝ (vs : Set ℝ³))).Nonempty →
     ¬ IsRupert vs →
     ∀ face : Set ℝ³,
       IsExtreme ℝ (convexHull ℝ (vs : Set ℝ³)) face ∧ (affineSpan ℝ face).finDim = 2 ∧ Convex ℝ face →
       (face.extremePoints ℝ).ncard = 3

end
