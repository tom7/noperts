module

public import Minimality.Type08S.C2K28B4a3
public import Minimality.Type08S.C2K28B4d2

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Lz = 0 with Lp < 0: leaf A's cell does not use Lz. -/
theorem k28b4_Az0 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : ⟪c' - a', b' - c⟫ < 0)
    (hLz : ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) :=
  k28b4_A hC hM hrel hα hβ hσ hLp

end C2
end Type08Sp
end Minimality
