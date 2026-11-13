module

public import Minimality.Type08S.C2K6TAE

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

/-! ## QTc -/

/-- Tc, `α4 = 1` (task 2a, not done): the slice itself. -/
def K6tTcA41 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (b - a) (a' - a) (b' - a) = 0 ∧ det3 (b' - a) (b - d) (c - d) = 0

end C2
end Type08Sp
end Minimality
