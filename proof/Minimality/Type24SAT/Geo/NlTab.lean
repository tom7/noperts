module

public import Minimality.Type24SAT.Geo.Ent3

@[expose] public section

/-!
# Type 24 stack: the routes of the normal table

Every triple of facets `a < b < c < 9` has a route: an atom (no two of the three share an edge), or a rotation `i` of the
key such that the other two facets share the edge `p q`.  The entry is computed from the route and the key.
-/

set_option autoImplicit false

open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- How the sign of `det3 Na Nb Nc` is obtained. -/
inductive Nr where
  | atom
  | rot (i p q r' s' : Nat)
  deriving DecidableEq, Repr

/-- The three valued entry of a normal route for the key `k`. -/
def Nr.ent (k : Nat × Nat × Nat) : Nr → S3
  | .atom => atomS (V.nv k.1 k.2.1 k.2.2)
  | .rot i p q _ s' =>
    nlS ([k.1, k.2.1, k.2.2].getD ((i + 1) % 3) 0) p q s' ([k.1, k.2.1, k.2.2].getD i 0)

end Minimality.H24.SAT
