module

public import Minimality.SixVertices

@[expose] public section

/-!
# The 29 non-simplicial combinatorial types of 7-vertex polyhedra

A convex polyhedron with 7 vertices has one of 34 combinatorial types: 5 simplicial
(all 10 faces triangles) and 29 with a face of 4 or more vertices
(`FEWER-FACES.md` §3; enumerated exactly by `enum7`, matching OEIS A049337).
`sevenTypeFaces k` lists the faces of type `k + 1` in the gallery labelling of
`FEWER-FACES.md` §4 (the labelling the per-type theorems of `Minimality/Cases.lean`
use), computed as the convex hulls of the realizations
`dense/flat7/gallery29/typeNN-*f-nice.txt` (the plain `typeNN-*f.txt` files use other
labellings, and those of types 17, 19, 23 realize types 19, 16, 22). The 29 lists are pairwise
non-isomorphic (2, 8, 11, 8 types with 6, 7, 8, 9 faces).

The classification step, `exists_sevenType` (`Minimality/Classify.lean`): seven points in
convex position with a facet of exactly 4 points realize one of the 29 types.
-/

namespace Minimality

/-- The faces of the 29 non-simplicial 7-vertex types: `sevenTypeFaces k` is
type `k + 1` (so `sevenTypeFaces 9` is type 10). -/
def sevenTypeFaces : Fin 29 → List (Finset (Fin 7)) :=
  ![
    -- type 01
    [{0, 1, 2}, {0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 5, 6}, {3, 4, 6}, {3, 5, 6}],
    -- type 02
    [{0, 1, 2}, {0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 6}, {2, 5, 6}, {3, 4, 5, 6}],
    -- type 03
    [{0, 1, 2}, {0, 1, 3}, {0, 2, 3, 4, 5, 6}, {1, 2, 5}, {1, 3, 6}, {1, 4, 5}, {1, 4, 6}],
    -- type 04
    [{0, 1, 2}, {0, 1, 3, 4}, {0, 2, 6}, {0, 4, 5}, {0, 5, 6}, {1, 2, 3, 5, 6}, {3, 4, 5}],
    -- type 05
    [{0, 1, 2, 3}, {0, 1, 4, 5}, {0, 3, 4}, {1, 2, 5, 6}, {2, 3, 4}, {2, 4, 6}, {4, 5, 6}],
    -- type 06
    [{0, 1, 2, 3}, {0, 2, 4}, {0, 3, 5}, {0, 4, 5}, {1, 2, 4, 5, 6}, {1, 3, 6}, {3, 5, 6}],
    -- type 07
    [{0, 1, 2}, {0, 1, 3}, {0, 2, 5, 6}, {0, 3, 4, 6}, {1, 2, 3, 4}, {2, 4, 5}, {4, 5, 6}],
    -- type 08
    [{0, 1, 2, 3}, {0, 1, 4}, {0, 2, 4, 5}, {1, 3, 6}, {1, 4, 6}, {2, 3, 5, 6}, {4, 5, 6}],
    -- type 09
    [{0, 1, 2}, {0, 1, 3, 4}, {0, 2, 5, 6}, {0, 4, 6}, {1, 2, 3}, {2, 3, 5}, {3, 4, 5, 6}],
    -- type 10
    [{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 4, 5}, {1, 3, 4, 6}, {2, 3, 5, 6}, {4, 5, 6}],
    -- type 11
    [{0, 1, 3}, {0, 1, 5}, {0, 2, 3, 4, 6}, {0, 4, 5}, {1, 2, 3}, {1, 2, 6}, {1, 4, 5}, {1, 4, 6}],
    -- type 12
    [{0, 1, 3, 5}, {0, 2, 4}, {0, 2, 5}, {0, 3, 4, 6}, {1, 2, 3}, {1, 2, 5}, {2, 3, 6}, {2, 4, 6}],
    -- type 13
    [{0, 1, 3}, {0, 1, 4, 5}, {0, 2, 3}, {0, 2, 4}, {1, 2, 3}, {1, 2, 6}, {1, 5, 6}, {2, 4, 5, 6}],
    -- type 14
    [{0, 1, 4}, {0, 1, 6}, {0, 2, 3, 5}, {0, 3, 6}, {0, 4, 5}, {1, 4, 5, 6}, {2, 3, 6}, {2, 5, 6}],
    -- type 15
    [{0, 1, 4, 5, 6}, {0, 2, 4}, {0, 2, 6}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4}, {2, 3, 6}, {3, 5, 6}],
    -- type 16
    [{0, 2, 3, 5}, {0, 2, 4}, {0, 3, 6}, {0, 4, 6}, {1, 3, 5, 6}, {1, 4, 5}, {1, 4, 6}, {2, 4, 5}],
    -- type 17
    [{0, 2, 4, 6}, {0, 3, 4}, {0, 3, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 5}, {1, 3, 6}, {2, 3, 4, 5}],
    -- type 18
    [{0, 1, 4}, {0, 1, 5}, {0, 3, 4}, {0, 3, 5, 6}, {1, 2, 4, 5}, {2, 4, 6}, {2, 5, 6}, {3, 4, 6}],
    -- type 19
    [{0, 2, 3, 5}, {0, 2, 6}, {0, 3, 4}, {0, 4, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 5, 6}, {3, 4, 6}],
    -- type 20
    [{0, 1, 3, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {1, 3, 4}, {1, 4, 6}, {2, 4, 5, 6}, {3, 4, 5}],
    -- type 21
    [{0, 1, 4}, {0, 1, 5}, {0, 2, 5, 6}, {0, 4, 6}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4, 6}, {2, 3, 5}],
    -- type 22
    [{0, 1, 2}, {0, 1, 3, 4}, {0, 2, 3}, {1, 2, 5}, {1, 4, 6}, {1, 5, 6}, {2, 3, 4}, {2, 4, 6}, {2, 5, 6}],
    -- type 23
    [{0, 1, 3}, {0, 1, 4}, {0, 3, 4, 5}, {1, 2, 3}, {1, 2, 5}, {1, 4, 6}, {1, 5, 6}, {2, 3, 5}, {4, 5, 6}],
    -- type 24
    [{0, 1, 2}, {0, 1, 6}, {0, 2, 5}, {0, 3, 4, 5}, {0, 4, 6}, {1, 2, 6}, {2, 3, 5}, {2, 3, 6}, {3, 4, 6}],
    -- type 25
    [{0, 1, 3}, {0, 1, 4}, {0, 2, 4, 6}, {0, 3, 5}, {0, 5, 6}, {1, 2, 4}, {1, 2, 6}, {1, 3, 6}, {3, 5, 6}],
    -- type 26
    [{0, 1, 3}, {0, 1, 6}, {0, 2, 4, 6}, {0, 3, 4}, {1, 3, 6}, {2, 3, 5}, {2, 3, 6}, {2, 4, 5}, {3, 4, 5}],
    -- type 27
    [{0, 1, 2}, {0, 1, 6}, {0, 2, 5}, {0, 4, 5}, {0, 4, 6}, {1, 2, 3}, {1, 3, 6}, {2, 3, 5, 6}, {4, 5, 6}],
    -- type 28
    [{0, 1, 5}, {0, 1, 6}, {0, 2, 3}, {0, 2, 4, 5}, {0, 3, 6}, {1, 4, 5}, {1, 4, 6}, {2, 3, 4}, {3, 4, 6}],
    -- type 29
    [{0, 1, 2}, {0, 1, 5}, {0, 2, 3}, {0, 3, 5}, {1, 2, 4}, {1, 4, 5, 6}, {2, 3, 4}, {3, 4, 6}, {3, 5, 6}]]

/-- The labelled points `x` realize the faces `fs`: every listed face is cut out
by an affine functional, zero at its points and negative at the others. -/
def RealizesFaces (x : Fin 7 → ℝ³) (fs : List (Finset (Fin 7))) : Prop :=
  ∀ f ∈ fs, ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, ∀ i, (i ∈ f → φ (x i) = 0) ∧ (i ∉ f → φ (x i) < 0)

/-- A face of a realized type is a facet of the labelled point set. -/
theorem isFacet_of_realizesFaces {x : Fin 7 → ℝ³} {fs : List (Finset (Fin 7))}
    (hR : RealizesFaces x fs) {f : Finset (Fin 7)} (hf : f ∈ fs) :
    IsFacet (Finset.univ.image x) (f.image x) := by
  classical
  obtain ⟨φ, hφ⟩ := hR f hf
  refine ⟨φ, fun p hp => ?_, fun p hp hpf => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (hφ i).1 hi
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hφ i).2 fun hi => hpf (Finset.mem_image_of_mem x hi)

end Minimality

end
