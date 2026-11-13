module

public import Minimality.Type08S.C2K17GA2

@[expose] public section

/-!
# K17GA / GA3: R3 (S1.1c) depth facts and wrappers
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k17ga_ip3 (p q r : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • p + x2 • q + x3 • r, y1 • p + y2 • q + y3 • r⟫ =
      x1 * y1 * ⟪p, p⟫ + (x1 * y2 + x2 * y1) * ⟪p, q⟫ + (x1 * y3 + x3 * y1) * ⟪p, r⟫ + x2 * y2 * ⟪q, q⟫ +
        (x2 * y3 + x3 * y2) * ⟪q, r⟫ + x3 * y3 * ⟪r, r⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm q p, real_inner_comm r p, real_inner_comm r q]
  ring

theorem k17ga_ipc (p q r u v : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) (hu : u = x1 • p + x2 • q + x3 • r)
    (hv : v = y1 • p + y2 • q + y3 • r) :
    ⟪u, v⟫ = x1 * y1 * ⟪p, p⟫ + (x1 * y2 + x2 * y1) * ⟪p, q⟫ + (x1 * y3 + x3 * y1) * ⟪p, r⟫ + x2 * y2 * ⟪q, q⟫ +
        (x2 * y3 + x3 * y2) * ⟪q, r⟫ + x3 * y3 * ⟪r, r⟫ := by
  subst hu hv; exact k17ga_ip3 _ _ _ _ _ _ _ _ _

end C2
end Type08Sp
end Minimality
