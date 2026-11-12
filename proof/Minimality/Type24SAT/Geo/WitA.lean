module

public import Minimality.Type24SAT.Geo.WitRow
public import Minimality.Type24SAT.Geo.Dec

@[expose] public section

/-!
# type 24: witness rows, the row checker
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality Minimality.H21

open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- A packed row is not a witness row, or its witness check passes. -/
def witD (chunks : List (List V)) (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 19 || witOK r.2.1 (r.2.2.map (litOfC chunks))

end Minimality.H24.SAT
