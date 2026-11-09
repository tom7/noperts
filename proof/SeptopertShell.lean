module

public import SeptopertShell.Watertight
public import SeptopertShell.View
public import SeptopertShell.Poly
public import SeptopertShell.IPoly
public import SeptopertShell.Slab
public import SeptopertShell.Closure
public import SeptopertShell.ClosurePar
public import SeptopertShell.Parse
public import SeptopertShell.Data

/-!
# A watertight shell of Rupert shapes around the Septopert island

**Goal.** A set `W ⊆ ℝ³` of Septopert-family parameters `(P/A, C/A, E/A)` (`SeptopertShell.shellVerts`)
such that every shape in `W` is Rupert, and every continuous path from the Septopert Classic to a point far
outside meets `W`: the island of shapes around the Classic without a passage is enclosed by certified
Rupert shapes.

**Plan** (numerics and certificates: nopert229, `out/bottleneck/famcensus/islandmap/`).

1. *Faces and charts.* The island is bounded by five surfaces: the cube-corner wall `s = 1/3`, the exact
   Triforce plane `y − z = 1/2`, the slanted face, the bottom face and a facet cut by a global passage.
   Each gets a polynomial chart `(s, y, δ) ↦ (s, y, Z_i(s, y) ± δ)` (`s ↦ 1/3 − δ` for the wall, on its acute
   side) in which the face is near `δ = 0` and `δ > 0` is outside; `g_i(p) := ±(p 2 − Z_i(p 0, p 1))` is the
   chart's `δ`.
2. *Certified slabs.* For each face, a rational polynomial witness in `(x₀, x₁, δ)`: a view `v` (at `δ = 0` the face's
   exact view, e.g. a vertex difference), an inner rotation `Q = Cayley(c) · M₀` and a translation `t`, and a box
   in chart coordinates with `δ ∈ [δ₁, δ₂]`, such that on the box `0 < v 2` and every inner vertex `Q p + t` lies,
   seen along `v`, inside a triangle of outer vertices: three triple products, polynomials with rational
   coefficients, proved positive on the box by exact monomial bounds with subdivision. Then every shape in the box
   is Rupert (`SeptopertShell.isRupert_of_view`: the outer rotation is built from `v`).
3. *Watertightness.* `D := B₀ ∩ {p | ∀ i, g_i p ≤ δ_m}` with `δ₁ < δ_m < δ₂` and a bounding box `B₀`.
   Its frontier lies in `⋃ i, {g_i = δ_m, g_j ≤ δ_m (j ≠ i)}` (certified to avoid the faces of `B₀`), and each
   of those pieces lies in the slab of face `i` (a polynomial covering condition, certified the same way).
   With `classicParams ∈ D` and `outsideParams ∉ D`, `separates_of_frontier_subset` gives the theorem.

Status (2026-11-09): done. `islandEnclosed_of_closureData` (standard axioms) and the native check
`checkSeptopertShell` on the inlined certificate `SeptopertShell.shellText` (`data/shell.txt`, 27 slabs and the
closure, 0.2 MB: integer condition polynomials and
centred-form subdivision trees; 4 min on 32 tasks; it prints "instantiated: IslandEnclosed"). The data is untrusted and
regenerable: nopert229 `out/bottleneck/famcensus/islandmap/bnd/shell_build.sh` (witness fits with the C++ polish,
exact C++ certificates with centred bounds, closure.py --lean).
-/

@[expose] public section

namespace SeptopertShell

/-- **The Septopert island is enclosed by Rupert shapes.** -/
def IslandEnclosed : Prop :=
  ∃ W : Set ℝ³, (∀ p ∈ W, IsRupert (shellVerts p)) ∧ Separates W classicParams outsideParams

/-- **The island is enclosed, given checked closure data** (the slab certificates are checked inside
`ClosureData.check`). The executable `checkSeptopertShell` evaluates the checks natively on the certificate files. -/
theorem islandEnclosed_of_closureData (C : ClosureData) (h : C.check = true) (hin : C.classicOk = true) :
    IslandEnclosed :=
  islandEnclosed_of_check C h hin

end SeptopertShell

end
