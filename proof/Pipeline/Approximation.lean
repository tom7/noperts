module

public import Pipeline.SolidModel

@[expose] public section

/-!
# The rational model approximates the polyhedron

Every `C5Model` (within `modelErrorQ ≤ 10⁻¹²` of the rational model) is a
`κ`-approximation (`κ = 10⁻¹⁰`) of the rational model, the budget of the
general checker; in particular so is the exact model (the rational seeds
moved by the exact symmetry). (How a solid shows that its exact model meets
`modelErrorQ` is its own business: the Septopert's model is exact, the
icosahedral solids bridge from the rational vertices to the exact fivefold
rotations through rational Taylor values of cos and sin, `FivefoldModel`.)
-/

open RationalApprox Real

namespace Noperts.Pipeline

variable [SolidModel]

/-- Every `C5Model` is a `κ`-approximation of the rational model. -/
theorem C5Model.vertex_close (P : C5Model) (i : VertexIndex) :
    ‖P.vertex i - toR3 (rationalVertex i)‖ ≤ κ :=
  (P.vertex_close_model i).trans (modelErrorQ_real_le.trans (by norm_num [κ]))

noncomputable def C5Model.approximation (P : C5Model) :
    RationalApprox.κApproxPoly P.polyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := P.vertex_close i

theorem vertex_close (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤ κ :=
  exactModel.vertex_close i

noncomputable def exactApproximation :
    RationalApprox.κApproxPoly exactPolyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := vertex_close i

end Noperts.Pipeline

end
