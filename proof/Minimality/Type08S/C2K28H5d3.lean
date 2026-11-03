module

public import Minimality.Type08S.C2K28H5a2
public import Minimality.Type08S.C2K28H5d2

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cell A with `hD2` discharged from the locus literals. -/
theorem k28h5_A' {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6)
    (hS : 0 < ⟪c' - a, b' - a⟫) (hT : ⟪a - d, a - c'⟫ < 0)
    (hrb : ∀ κ g : ℝ, κ = ⟪c' - a, b' - a⟫ / ⟪c' - a, c' - a⟫ → g = (α1 - 1) * (1 - κ) / β1 →
      0 < γ6 * g * (β1 - 1) + α1 * (β6 + γ6 * κ - 1)) :
    HasLexCell (V8 a a' b b' c c' d) :=
  k28h5_A hC hM hrel h5 hS hT (k28h5a_hD2 hC hM hrel h5 hS) hrb

end C2
end Type08Sp
end Minimality
