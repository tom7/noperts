module

public import Minimality.Type08S.C2K5FM

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **QTa wrapper (boxes A, B, C, E; box D as an explicit residual `hD`).**  `Δ = det3 (a-d) (b-d) (c-d)`;
`β1 - 1 ~ det3 (a-d) (c'-b) (c-d) / Δ`, `α4 - 1 ~ det3 (b'-a) (b-d) (c-d) / Δ`, `β6 - 1 ~ det3 (a'-b) (c-d) (a-d) / Δ`.
Slices excluded: `β1 = 1`, `α4 = 1`, `β6 = 1` (`hβ1 hα4 hβ6`), `D_c = 0`, `D_c < 0 ∧ ζ_C = 0` (`hcase`, box C),
`ζ_E = ⟪b - a', a - c'⟫ = 0` (`hζE`, box E).  `hD` is box D (`β1 > 1, α4 > 1, β6 > 1`). -/
theorem k5f_qta_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hβ1 : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0)
    (hα4 : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0)
    (hβ6 : det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ≠ 0)
    (hcase : 0 < ⟪b - d, c - d⟫ ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ ≠ 0))
    (hζE : ⟪b - a', a - c'⟫ ≠ 0)
    (hD : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) →
      0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) →
      0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) →
      HasLexCell (V8 a a' b b' c c' d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rcases lt_or_gt_of_ne hβ1 with h1 | h1
  · exact k5f_A_hasLexCell W hT hκ h1
  · rcases lt_or_gt_of_ne hα4 with h4 | h4
    · rcases lt_or_gt_of_ne hβ6 with h6 | h6
      · exact k5f_B_hasLexCell W hT h4 h6
      · exact k5f_C_hasLexCell W hT hκ hfar h1 h4 h6 hcase
    · rcases lt_or_gt_of_ne hβ6 with h6 | h6
      · exact k5f_E_hasLexCell W hT hκ hfar h1 h4 h6 hζE
      · exact hD h1 h4 h6

end C2
end Type08Sp
end Minimality
