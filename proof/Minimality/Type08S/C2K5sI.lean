module

public import Minimality.Type08S.C2K5sH

@[expose] public section

/-!
# K5s / I: `s4TRK3_hasLexCell`

`S4TRK3` has a lex cell at the edge view `a - d`, except on the sub-slice
`0 < ⟪a - d, b - d⟫ ∧ ⟪a' - b, b - d⟫ = 0 ∧ 0 ≤ ⟪a' - b, c - d⟫` (codim 7 inside `S4TRK3`; numerically no cell at `a - d` there).
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

theorem s4TRK3_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TRK3 a a' b b' c c' d)
    (hres : ¬ (0 < ⟪a - d, b - d⟫ ∧ ⟪a' - b, b - d⟫ = 0 ∧ 0 ≤ ⟪a' - b, c - d⟫)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  exact C2.k5_hasLexCell N h.1 h.2 hres


end Type08Sp
end Minimality
