module

public import Minimality.Type08S.C2K1F

@[expose] public section

/-!
# K5s / A: the K1 cells X1, X2 with a free tilt segment and a tie rule for `a' ~ b` (`s = 0`)
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

theorem k5_wdiff (p q r d : ℝ³) (β6 v1 v2 : ℝ) :
    ⟪fpoint p q r d (β6, 1, 0), fcomb p q r v1 v2 0⟫ - ⟪fpoint p q r d (1, 0, 0), fcomb p q r v1 v2 0⟫ =
      v1 * ⟪(β6 - 1) • p + q, p⟫ + v2 * ⟪(β6 - 1) • p + q, q⟫ := by
  simp only [fpoint, fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_right, inner_sub_left, inner_zero_left]
  rw [real_inner_comm q p]
  ring

end C2
end Type08Sp
end Minimality
