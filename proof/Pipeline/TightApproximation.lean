module

public import Pipeline.Approximation

@[expose] public section

/-!
# The tight vertex error

The general checker allows a loose `κ = 10⁻¹⁰` per vertex. The projective
local certificates, which work near outer-silhouette transitions where that
allowance is much larger than the actual rounding, use the solid's own
per-vertex error `tightVertexErrorQ = modelErrorQ` instead: 0 for the
Septopert (the C++ checker's `MODEL_EXACT`: `supportError = 0`, and exact
support ties pass the `≤ 0` support checks), `6 · 10⁻¹⁶` for the icosahedral
solids. Every `C5Model` meets it by its `close` field.
-/

namespace Noperts.Pipeline

variable [SolidModel]

/-- Uniform vertex error used by the support-sensitive local checker. -/
def tightVertexErrorQ : ℚ := modelErrorQ

theorem modelErrorQ_eq : modelErrorQ = tightVertexErrorQ := rfl

theorem tightVertexErrorQ_nonneg : 0 ≤ tightVertexErrorQ := modelErrorQ_nonneg

theorem tightVertexErrorQ_real_nonneg : (0 : ℝ) ≤ (tightVertexErrorQ : ℝ) := by
  exact_mod_cast tightVertexErrorQ_nonneg

/-- Every `C5Model` meets the tight bound the projective certificates use. -/
theorem C5Model.vertex_close_tight (P : C5Model) (i : VertexIndex) :
    ‖P.vertex i - toR3 (rationalVertex i)‖ ≤ (tightVertexErrorQ : ℝ) :=
  P.vertex_close_model i

theorem vertex_close_tight (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤ (tightVertexErrorQ : ℝ) :=
  exactModel.vertex_close_tight i

end Noperts.Pipeline

end
