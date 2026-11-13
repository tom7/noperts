module

public import EuclideanSpaceNotation
public import MainTheorem

/-!
# The Septopert shell: the continuous Septopert family

The Septopert family `(−a,b,b), (c,e,e), (−f,−f,−f)` with their coordinate permutations is determined up to
similarity by its invariants `(A, P, C, E) = (a + b, a − f, c − b, e − b)`, up to scale. We use the
parameters `p = (P/A, C/A, E/A) ∈ ℝ³`, and for them the representative with `a = 0, b = 1`:

* `(0, 1, 1)`, `(1, 0, 1)`, `(1, 1, 0)`,
* `(1 + y, 1 + z, 1 + z)`, `(1 + z, 1 + y, 1 + z)`, `(1 + z, 1 + z, 1 + y)`,
* `(s, s, s)`,

where `(s, y, z) = (p 0, p 1, p 2)`. In these coordinates the *Septopert island* is the region of shapes
without a Rupert passage around the Septopert Classic, `(1268289, 426431, 376317, −279863)`; numerically
(from external numerics) it is a curved tetrahedron bounded by the cube-corner wall `s = 1/3`, the
exact-Triforce plane `y − z = 1/2`, two curved local-passage faces and a facet cut by a global passage family.
-/

@[expose] public section

namespace SeptopertShell

/-- The 7 vertices of the Septopert-family shape with parameters `p = (P/A, C/A, E/A)`. -/
noncomputable def shellVerts (p : ℝ³) : Finset ℝ³ :=
  {!₂[(0 : ℝ), 1, 1], !₂[(1 : ℝ), 0, 1], !₂[(1 : ℝ), 1, 0],
   !₂[1 + p 1, 1 + p 2, 1 + p 2], !₂[1 + p 2, 1 + p 1, 1 + p 2], !₂[1 + p 2, 1 + p 2, 1 + p 1],
   !₂[p 0, p 0, p 0]}

/-- The parameters of the Septopert Classic, `(P/A, C/A, E/A)` for
`(A, P, C, E) = (1268289, 426431, 376317, −279863)`. It lies inside the island. -/
noncomputable def classicParams : ℝ³ :=
  !₂[(426431 : ℝ) / 1268289, (376317 : ℝ) / 1268289, (-279863 : ℝ) / 1268289]

/-- A point far outside the island, `(P/A, C/A, E/A) = (1, 0, 0)` (the solid with apex `(1, 1, 1)`). -/
noncomputable def outsideParams : ℝ³ := !₂[(1 : ℝ), 0, 0]

end SeptopertShell

end
