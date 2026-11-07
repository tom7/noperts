module

public import Minimality.Type21SAT.DataA
public import Minimality.Type21SAT.RowSound

@[expose] public section

/-!
# L3, part 15: core A, decoded rows and the kernel check of the non-rule families
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H21.SAT

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

/-- The name chunks of core A (200 names each). -/
def chunksA : List (List V) :=
  [namesA0, namesA1, namesA2, namesA3, namesA4, namesA5, namesA6, namesA7, namesA8, namesA9, namesA10,
   namesA11, namesA12, namesA13, namesA14, namesA15, namesA16, namesA17]

/-- The name of variable number `i` of core A (`i = 0` is the constant true). -/
def nmA (i : Nat) : Lit :=
  match i with
  | 0 => ltrue
  | j + 1 => (true, lget (lget chunksA (j / 200) []) (j % 200) V.tru)

/-- The literal of a code. -/
def litOfA (c : Nat) : Lit := if c % 2 == 0 then nmA (c / 2) else (nmA (c / 2)).neg

/-- The clause of a packed row. -/
def clauseA (n : Nat) : List Lit := (decRow n).2.2.map litOfA

/-- A row passes the check, or is a rule (17), witness (19) or case clause (30) row. -/
def rowD (n : Nat) : Bool :=
  let r := decRow n
  r.1 == 17 || r.1 == 19 || r.1 == 30 || rowOK3 r.1 r.2.1 (r.2.2.map litOfA)

/-- Chunk 0 of core A passes the non-rule check. -/
theorem chunk0 : (rowsA0.all rowD) = true := by decide +kernel

/-- Chunk 1 of core A passes the non-rule check. -/
theorem chunk1 : (rowsA1.all rowD) = true := by decide +kernel

/-- Chunk 2 of core A passes the non-rule check. -/
theorem chunk2 : (rowsA2.all rowD) = true := by decide +kernel

/-- Chunk 3 of core A passes the non-rule check. -/
theorem chunk3 : (rowsA3.all rowD) = true := by decide +kernel

/-- Chunk 4 of core A passes the non-rule check. -/
theorem chunk4 : (rowsA4.all rowD) = true := by decide +kernel

/-- Chunk 5 of core A passes the non-rule check. -/
theorem chunk5 : (rowsA5.all rowD) = true := by decide +kernel

/-- Chunk 6 of core A passes the non-rule check. -/
theorem chunk6 : (rowsA6.all rowD) = true := by decide +kernel

/-- Chunk 7 of core A passes the non-rule check. -/
theorem chunk7 : (rowsA7.all rowD) = true := by decide +kernel

/-- Chunk 8 of core A passes the non-rule check. -/
theorem chunk8 : (rowsA8.all rowD) = true := by decide +kernel

/-- Chunk 9 of core A passes the non-rule check. -/
theorem chunk9 : (rowsA9.all rowD) = true := by decide +kernel

/-- Chunk 10 of core A passes the non-rule check. -/
theorem chunk10 : (rowsA10.all rowD) = true := by decide +kernel

/-- Chunk 11 of core A passes the non-rule check. -/
theorem chunk11 : (rowsA11.all rowD) = true := by decide +kernel

/-- Chunk 12 of core A passes the non-rule check. -/
theorem chunk12 : (rowsA12.all rowD) = true := by decide +kernel

/-- Chunk 13 of core A passes the non-rule check. -/
theorem chunk13 : (rowsA13.all rowD) = true := by decide +kernel


end Minimality.H21.SAT
