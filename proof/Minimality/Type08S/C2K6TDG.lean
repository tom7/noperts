module

public import Minimality.Type08S.C2K6TDF

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

/-- The `β1 = 1`, `B = 0` tie of QTa (not Touch): codim 5. -/
def K6t4B11 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (a - d) (c' - b) (c - d) = 0 ∧ ⟪b - d, a - d⟫ = 0

end C2
end Type08Sp
end Minimality
