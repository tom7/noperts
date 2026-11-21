module

public import Minimality.Type16Arc3B
public import Minimality.SilS0XC

@[expose] public section

/-!
# H16G: the generic all-views route for type 16, and the combined arc residual

Copy of `Type29GA` for type 16 (8 facets `fIdx`, 13 edges).  `h16g_seg i j pat` (view `x j - x i`) and
`h16g_lin X Y pat` (view `N_X x N_Y`) are the generic leaves; `H16GenResid T` = no generic leaf applies;
`H16ArcGenResid T = H16ArcResid3 T ∧ H16GenResid T`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H16A
open Minimality.H21 Minimality.H16U Minimality.V2

/-- The 13 edges of type 16 with their two facets. -/
def h16g_E : List (Fin 7 × Fin 7 × Fin 8 × Fin 8) :=
  [(0, 2, 0, 2), (0, 3, 0, 3), (0, 4, 2, 4), (0, 6, 3, 4), (1, 4, 5, 6), (1, 5, 1, 5), (1, 6, 1, 6),
    (2, 4, 2, 7), (2, 5, 0, 7), (3, 5, 0, 1), (3, 6, 1, 3), (4, 5, 5, 7), (4, 6, 4, 6)]

variable {x : Fin 7 → ℝ³}

/-- The type-16 facets as a type-free facet family. -/
noncomputable def h16g_fac (T : Type16 x) : S0xFac 8 fIdx x where
  f := T.ff
  N := T.fN
  hN := ff_hN T
  zero t i h := ff_zero T t i h
  neg t i h := ff_neg T t i h

end H16A
end Minimality
