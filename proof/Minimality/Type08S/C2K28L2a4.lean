module

public import Minimality.Type08S.C2K28L2a2

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The base view `u0 = m_r (a-d) - m_p (c-d)`, `m_p = (1-α1)pp - β1 s`, `m_r = (1-α1)s - β1 qr`
(`s = ⟪a-d,b-d⟫ = ⟪a-d,c-d⟫` on K6sM). -/
noncomputable def k28l2aU0 (a b c d : ℝ³) (α1 β1 : ℝ) : ℝ³ :=
  ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) • (a - d) -
    ((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) • (c - d)

end C2
end Type08Sp
end Minimality
