module

public import Noperthedron.PentagonalHexecontahedron.Approximation

@[expose] public section

/-!
# The tight vertex error

The projective local certificates use a per-vertex error `tightVertexErrorQ`
(`6 · 10⁻¹⁶`, the value `modelErrorQ` has). For the fivefold pipeline this
bounded trigonometric rounding; here the rational model is exact, so the
exact model meets it with distance 0, and every `C5Model` meets it by its
`close` field.
-/

namespace Noperthedron.PentagonalHexecontahedron

/-- Uniform vertex error used by the support-sensitive local checker. -/
def tightVertexErrorQ : ℚ := 6 / 10^16

theorem vertex_close_tight (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤
      (tightVertexErrorQ : ℝ) := by
  rw [exactVertex_eq, sub_self, norm_zero]
  norm_num [tightVertexErrorQ]

theorem modelErrorQ_eq : modelErrorQ = tightVertexErrorQ := rfl

/-- Every `C5Model` meets the tight bound the projective certificates use. -/
theorem C5Model.vertex_close_tight (P : C5Model) (i : VertexIndex) :
    ‖P.vertex i - toR3 (rationalVertex i)‖ ≤ (tightVertexErrorQ : ℝ) :=
  modelErrorQ_eq ▸ P.vertex_close_model i

/-- The verified model: the exact C3 images of the rational seeds (the
rational model itself). -/
noncomputable def exactModel : C5Model where
  seed s := toR3 (seedVertex s)
  close i := by
    simpa [modelErrorQ_eq, exactVertex] using vertex_close_tight i

theorem exactModel_vertex (i : VertexIndex) : exactModel.vertex i = exactVertex i := rfl

theorem exactModel_verts : exactModel.verts = exactVerts := rfl

end Noperthedron.PentagonalHexecontahedron

end
