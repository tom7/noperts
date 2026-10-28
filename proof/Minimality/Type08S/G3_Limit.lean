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

/-- The named views of type 08: `p - q` for `p, q` in different pairs of the octahedron (the
views of the edge crossings `a' → c`, i.e. N2, up to sign and relabelling), and `p - d`
(the views `d b` of T4/Q).  18 lines.  CHECK against PROOFS §29.0 (doubt D1). -/
def Named08 (a a' b b' c c' d : ℝ³) (u : ℝ³) : Prop :=
  (∃ (i j : Fin 3) (s t : Bool), i ≠ j ∧
    u = (if s then (![a, b, c] i) else (![a', b', c'] i)) -
        (if t then (![a, b, c] j) else (![a', b', c'] j))) ∨
  (∃ (i : Fin 3) (s : Bool), u = (if s then (![a, b, c] i) else (![a', b', c'] i)) - d)

/-- At most two independent depth ties at the view `u`: the seven depths take at least five
distinct values. -/
def FewTies (V : Finset ℝ³) (u : ℝ³) : Prop := 5 ≤ (V.image fun p => ⟪p, u⟫).card

/-- The far triple tie ("touching") of the named closing N2 (`z b = z c' = z b'` along
`c - a'`) or T4 (`z c = z b' = z c'` along `b - d`) in the labelling `(a, b, c)`. -/
def Touch (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫) ∨
    (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)

/-- Touching in some labelling. -/
def TouchAny (a a' b b' c c' d : ℝ³) : Prop :=
  Touch a a' b b' c c' d ∨ Touch b b' a a' c c' d ∨ Touch a a' c c' b b' d ∨
    Touch c c' a a' b b' d ∨ Touch b b' c c' a a' d ∨ Touch c c' b b' a a' d

end Type08Sp
end Minimality
