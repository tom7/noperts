module

public import Minimality.Type24SAT.Geo.RowSound

@[expose] public section

/-!
# type 24, decoding of the packed rows (generic; the data modules are separate)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- Digits of a packed row (base 65536, low digit first). -/
def digs : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 65536) :: digs f (n / 65536)

/-- A packed row: family + 1, the number `k` of parameters up to the last non-zero one, those `k` parameters, then the literal
codes `2 idx + (1 if negative)`. The parameters are padded with zeros to eight. -/
def decRow (n : Nat) : Nat × List Nat × List Nat :=
  let d := digs 64 n
  let k := d.getD 1 0
  (d.headD 1 - 1, ((d.drop 2).take k ++ List.replicate 8 0).take 8, d.drop (2 + k))

/-- List lookup (structural, for the kernel). -/
def lget {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: as, n, d => match n with | 0 => a | m + 1 => lget as m d




end Minimality.H24.SAT
