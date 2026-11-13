module

public import Minimality.Type08S.Defs08

@[expose] public section

set_option autoImplicit true

/-!
# Group G3: `Named08` and `Touch` for type 08

The named views of a type-08 shape and the touching condition (far triple tie of the named
closings N2, T4), used by the limit theorem `G3p.isRupert_type08_limit_hdn`.  (The scratch
statements `isRupert_type08_limit_norm/_any` of this group are superseded by `G3p` and not kept.)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The far triple tie ("touching") of the named closing N2 (`z b = z c' = z b'` along
`c - a'`) or T4 (`z c = z b' = z c'` along `b - d`) in the labelling `(a, b, c)`. -/
def Touch (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫) ∨
    (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)

end Type08Sp
end Minimality
