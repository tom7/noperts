module

public import Pipeline.IcoModel
public import SnubDodecahedron.RationalVertices
public import SnubDodecahedron.OrbitData

@[expose] public section

/-!
# The snub dodecahedron as a fivefold solid model

The snub dodecahedron, in a frame where z is a 5-fold axis: its 60 vertices
rotate 12 seed vertices about z in steps of 2π/5 (vertex `12k + s` is seed `s`
rotated by `2πk/5`, up to rounding). The data (`rationalVertices`,
`seedVertex`) is in `SnubDodecahedron.RationalVertices`, which imports only
Mathlib so that the kernel-checked tangent-cone table built on it is not
rebuilt when the pipeline changes.

`icosahedralSolid` (a scoped instance: in effect inside `namespace
SnubDodecahedron` only) makes this data, with its I-orbit tables
(`OrbitData`: one free orbit), an `IcosahedralSolid`, hence a `FivefoldSolid`
and a `SolidModel` for the certificate pipeline; the facts it needs are
checked by the kernel below.
-/

namespace SnubDodecahedron

open Noperts Noperts.Pipeline

theorem seedVertex_xy_sq_le_one :
    ∀ t : Fin 12, (SnubDodecahedron.seedVertex t 0) ^ 2 +
      (SnubDodecahedron.seedVertex t 1) ^ 2 ≤ 1 := by
  decide +kernel

/-- The printed rational vertices agree with the tight rational rotations of
the seeds (`tightVertex`) to `4 · 10⁻¹⁶`. Kernel checked. -/
theorem rationalVertices_tight_sq_close : ∀ i : Fin (5 * 12),
    (rationalVertices i 0 - tightVertex SnubDodecahedron.seedVertex i 0) ^ 2 +
    (rationalVertices i 1 - tightVertex SnubDodecahedron.seedVertex i 1) ^ 2 +
    (rationalVertices i 2 - tightVertex SnubDodecahedron.seedVertex i 2) ^ 2 ≤
      (4 / 10^16 : ℚ) ^ 2 := by
  decide +kernel

/-- Every rational vertex has norm in `[1/10, 1 - 10⁻¹²]`. -/
theorem rationalVertices_sq_norm_bounds : ∀ i : Fin (5 * 12),
    (1 / 100 : ℚ) ≤ rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 +
        rationalVertices i 2 ^ 2 ∧
      rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 := by
  decide +kernel

theorem orbits_check : icoOrbitsCheck 12 iOrbitCount vertexOrbitIndex vertexElementIndex
    orbitStabilizer orbitSlot orbitStab = true := by
  decide +kernel

/-- The snub dodecahedron's model for the certificate pipeline. -/
scoped instance icosahedralSolid : IcosahedralSolid where
  seedCount := 12
  seedCount_pos := by norm_num
  rationalVertices := rationalVertices
  seedVertex := SnubDodecahedron.seedVertex
  seed_xy_sq_le_one := seedVertex_xy_sq_le_one
  tight_sq_close := rationalVertices_tight_sq_close
  rationalVertex_sq_norm_bounds := rationalVertices_sq_norm_bounds
  iOrbitCount := iOrbitCount
  iOrbitCount_pos := by decide
  vertexOrbitIndex := vertexOrbitIndex
  orbitStabilizer := orbitStabilizer
  vertexElementIndex := vertexElementIndex
  orbitSlot := orbitSlot
  orbitStab := orbitStab
  orbits_check := orbits_check

end SnubDodecahedron

end
