module

public import Minimality.Type08S.C2K14J

@[expose] public section

/-!
# K14 / K: Ta box C leftover cut to `D_c = 0`; `K14LeftTa'`; wrapper `k14_Ta'`
-/
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

/-- Ta box C with `D_c = 0` only (the tie `D_c < 0 ∧ ζ_C = 0` is closed by `k14_TaC_hasLexCell`). -/
def K14TaC (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
  0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ∧
  ⟪b - d, c - d⟫ = 0

end C2
end Type08Sp
end Minimality
