module

public import Minimality.Type08S.C2K6PC

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Double-tie stratum D1: `ρ_a = 0` and `ζ(c',d) = 0` (view `b - c`). -/
def K6sD1 (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - c⟫ = 0 ∧ ⟪c' - d, b - c⟫ = 0

/-- Double-tie stratum D2: `ρ_a = 0`, `ζ(b',d) = 0 < ζ(c',d)`. -/
def K6sD2 (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - c⟫ = 0 ∧ ⟪b' - d, b - c⟫ = 0 ∧ 0 < ⟪c' - d, b - c⟫

end C2
end Type08Sp
end Minimality
