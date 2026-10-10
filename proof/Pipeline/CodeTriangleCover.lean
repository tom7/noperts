module

public import Pipeline.WedgeCover
public import Pipeline.IcoView

@[expose] public section

/-!
# A solid's cover of the view triangle by code triangles

The identity-tube tables of an icosahedral solid are organized by code
triangle: the face-visibility code cells of the view triangle T
(`icoViewTriangle`), split into projective triangles. The solid's generated
`WedgeCoverData` lists them (`codeTriangles`, in pack order), with T itself
(`baseTriangle`) and a decision tree (`coverTree`) whose check proves that
they cover T (`WedgeCover.base_covered`).

`CodeTriangleCover` is that data, for the shared solution tree
(`Pipeline.AtlasProjectiveSolutionTree`). Each solid provides it as a scoped
instance in its `SolidModel`, next to its `IcosahedralSolid`. The check
`coverValid` is the same computation as the solid's own
`WedgeCover.coverValid` (equal by `rfl`).
-/

namespace Noperts.Pipeline

open Noperts.Atlas.ProjectiveView

/-- The code triangles of a solid and the tree that proves they cover its
view triangle (see the module documentation). -/
class CodeTriangleCover where
  codeTriangles : Array WedgeCover.Tri
  baseTriangle : WedgeCover.Tri
  coverTree : WedgeCover.Node
  baseTriangle_valid : WedgeCover.baseTriangleValid baseTriangle = true
  /-- The base triangle is the icosahedral view triangle T (checked by the
  kernel on the solid's data). -/
  icoViewTriangle_eq : toReal icoViewTriangle = toReal baseTriangle

namespace WedgeCover

variable [CodeTriangleCover]

/-- The projective triangles of all face-visibility code cells, in code order
(as exported to the code packs). -/
abbrev codeTriangles : Array Tri := CodeTriangleCover.codeTriangles

/-- The view triangle T that the code triangles cover. -/
abbrev baseTriangle : Tri := CodeTriangleCover.baseTriangle

/-- The cover check, evaluated natively by the verifier. -/
def coverValid : Bool :=
  CodeTriangleCover.coverTree.check codeTriangles (baseConstraints baseTriangle)

/-- Every point of the base triangle lies in one of the code triangles,
given the (natively checked) cover. -/
theorem codeTriangles_cover (hcover : coverValid = true) (u : Fin 3 → ℝ)
    (hu : InTriangle (toReal baseTriangle) u) :
    ∃ t : ℕ, ∃ tri, codeTriangles[t]? = some tri ∧ InTriangle (toReal tri) u :=
  base_covered baseTriangle CodeTriangleCover.baseTriangle_valid codeTriangles
    CodeTriangleCover.coverTree hcover u hu

end WedgeCover

end Noperts.Pipeline

end
