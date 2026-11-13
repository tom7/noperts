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

def h16g_nb (pat : Fin 8 → Bool) (v : Fin 7) : List (Fin 7) :=
  h16g_E.filterMap fun e =>
    if pat e.2.2.1 != pat e.2.2.2 then
      (if e.1 = v then some e.2.1 else if e.2.1 = v then some e.1 else none)
    else none

def h16g_walk (pat : Fin 8 → Bool) (s : Fin 7) : ℕ → Fin 7 → Fin 7 → List (Fin 7)
  | 0, _, _ => []
  | n + 1, p, c =>
    if c = s then [] else c :: h16g_walk pat s n c (((h16g_nb pat c).filter (· ≠ p)).headD c)

def h16g_cyc (pat : Fin 8 → Bool) : List (Fin 7) :=
  match (List.finRange 7).find? (fun v => !(h16g_nb pat v).isEmpty) with
  | none => []
  | some s => s :: h16g_walk pat s 7 s ((h16g_nb pat s).headD s)

def h16g_k (pat : Fin 8 → Bool) : ℕ := (h16g_cyc pat).length - 3 + 3

instance (pat : Fin 8 → Bool) : NeZero (h16g_k pat) := ⟨by unfold h16g_k; omega⟩

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
