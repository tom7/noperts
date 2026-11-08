module

public import Minimality.Type16SAT.RowSound

@[expose] public section

/-!
# Type 16, decoding of the packed rows (generic; the data modules are separate)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Digits of a packed row (base 65536, low digit first). -/
def digs : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 65536) :: digs f (n / 65536)

/-- A packed row (at most 128 digits; J8: a type 16 fail row has 71 literals): family + 1, the number `k` of parameters up to the last non-zero one, those `k` parameters, then the literal
codes `2 idx + (1 if negative)`. The parameters are padded with zeros to eight. -/
def decRow (n : Nat) : Nat × List Nat × List Nat :=
  let d := digs 128 n
  let k := d.getD 1 0
  (d.headD 1 - 1, ((d.drop 2).take k ++ List.replicate 8 0).take 8, d.drop (2 + k))

/-- List lookup (structural, for the kernel). -/
def lget {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: as, n, d => match n with | 0 => a | m + 1 => lget as m d

/-- The name of variable number `i` (`i = 0` is the constant true) from name chunks of 200. -/
def nmOf (chunks : List (List V)) (i : Nat) : Lit :=
  match i with
  | 0 => ltrue
  | j + 1 => (true, lget (lget chunks (j / 200) []) (j % 200) V.tru)

/-- The literal of a code. -/
def litOfC (chunks : List (List V)) (c : Nat) : Lit :=
  if c % 2 == 0 then nmOf chunks (c / 2) else (nmOf chunks (c / 2)).neg

/-- A row passes the check, or is a rule (17), witness (19), `T(L,L)` (22), quad relation (23) or unit (26) row. -/
def rowD (chunks : List (List V)) (n : Nat) : Bool :=
  let r := decRow n
  r.1 == 17 || r.1 == 19 || r.1 == 22 || r.1 == 26 || r.1 == 23 || rowOK3 r.1 r.2.1 (r.2.2.map (litOfC chunks))

end Minimality.H16.SAT
