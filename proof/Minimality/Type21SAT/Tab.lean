module

public import Minimality.Type21SAT.Ent3

@[expose] public section

/-!
# L3, part 8: the routes of the tables

A key of the triple table is given by a route `Rt` (data, untrusted); the entry is computed from the route by `Rt.ent`,
and `triRoutes_sound` (B3TriSound) proves `Sg3` of the entry for every route in the list.  The normal table `nlS` and
the facing `fup3` are computed from the key alone.
-/

set_option autoImplicit false

namespace Minimality.H21.SAT

/-- How the sign of the determinant of three edge differences is obtained. -/
inductive Rt where
  | zc
  | zq (T : Nat)
  | fac (T x y o oi : Nat)
  | b4 (T p q r s : Nat) (c : Int)
  | at (v : V) (c : Int)
  deriving DecidableEq, Repr

/-- The three valued entry of a route. -/
def Rt.ent : Rt → S3
  | .zc => zeroS
  | .zq _ => zeroS
  | .fac T x y o oi => if oi == 1 then negS (facS T x y o) else facS T x y o
  | .b4 T p q r _ c => cS (c * -oriv T p q r)
  | .at v c => scaleS c (atomS v)

end Minimality.H21.SAT
