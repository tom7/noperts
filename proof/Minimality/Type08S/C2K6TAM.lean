module

public import Minimality.Type08S.C2K6TAL

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

/-- Ta box C (`β1 > 1`, `α4 < 1`, `β6 > 1`) with `D_c = 0` (task 4d) or `D_c < 0 ∧ ζ_C = 0` (task 4e): unfinished. -/
def K6tTaC (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
  0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ∧
  (⟪b - d, c - d⟫ = 0 ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ = 0))

/-- Ta `α4 = 1`, `β1 > 1`, `β6 ≥ 1` (task 4b: C1 cell and X1 pentagon; unfinished). -/
def K6tTaA41 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) = 0 ∧
  0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d)

/-- Ta box E (`β1 > 1`, `α4 > 1`, `β6 < 1`) with `ζ_E = 0` (task 4f; unfinished). -/
def K6tTaE (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) < 0 ∧ ⟪b - a', a - c'⟫ = 0

end C2
end Type08Sp
end Minimality
