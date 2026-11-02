module

public import Minimality.Type08S.C2K6TAD

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **Task 4c: QTa with `β6 = 1`** (`β1 > 1`, `α4 ≠ 1`, `ζ(d,b) ≠ 0`; `Δ = det3 (a-d) (b-d) (c-d)`).
`α4 < 1`: box B's face `Q_ab` at `c - d` (`k6t1_B_hasLexCell`); `α4 > 1`: box D's two cells at `a - b'`
(`k6t1_qta_D_hasLexCell`).  No leftover other than the hypotheses `hα4`, `hζ`. -/
theorem k6t1_Ta_b61 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hβ1 : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hα4 : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0)
    (hβ6 : det3 (a' - b) (c - d) (a - d) = 0)
    (hζ : ⟪d - b, a - b'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rcases lt_or_gt_of_ne hα4 with h4 | h4
  · refine k6t1_B_hasLexCell W hT hfar h4.le (by rw [hβ6]; simp) (Or.inl h4) hβ1
  · exact k6t1_qta_D_hasLexCell W hT hκ hfar hζ hβ1 h4 (by rw [hβ6]; simp)

end C2
end Type08Sp
end Minimality
