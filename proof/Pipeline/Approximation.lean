module

public import Pipeline.Vertices

@[expose] public section

/-!
# The rational model approximates the polyhedron

The rational vertices are exact (`exactVertex_eq`), so the exact model is a
`κ`-approximation (indeed a 0-approximation) of the rational one, and every
`C5Model` (within `modelErrorQ` of the rational model) is a
`κ`-approximation too. (The fivefold pipeline needed rational Taylor
approximations of `Rz(2πk/5)` here; the C3 action is exact.)
-/

open RationalApprox Real

namespace Noperts.Pipeline

theorem vertex_close (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤ κ := by
  rw [exactVertex_eq, sub_self, norm_zero]
  norm_num [κ]

noncomputable def exactApproximation :
    RationalApprox.κApproxPoly exactPolyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := vertex_close i

/-- Every `C5Model` is a `κ`-approximation of the rational model. -/
theorem C5Model.vertex_close (P : C5Model) (i : VertexIndex) :
    ‖P.vertex i - toR3 (rationalVertex i)‖ ≤ κ :=
  (P.vertex_close_model i).trans (by norm_num [modelErrorQ, κ])

noncomputable def C5Model.approximation (P : C5Model) :
    RationalApprox.κApproxPoly P.polyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := P.vertex_close i

end Noperts.Pipeline

end
