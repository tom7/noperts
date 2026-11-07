module

public import Minimality.Type21SAT.WitRow
public import Minimality.Type21SAT.RowA

@[expose] public section

/-!
# L3, part 20: witness rows of core A, the kernel check
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-- A packed row is not a witness row, or its witness check passes. -/
def witD (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 19 || witOK r.2.1 (r.2.2.map litOfA)

/-- All witness rows of core A pass the check. -/
theorem wchunkAll : (rowsA.all fun ch => ch.all witD) = true := by decide +kernel

end Minimality.H21.SAT
