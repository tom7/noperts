module

public import Minimality.Type21SAT.DataB
public import Minimality.Type21SAT.RuleA
public import Minimality.Type21SAT.WitRow
public import Minimality.Type21SAT.LexSound

@[expose] public section

/-!
# L3, part 27: core B, decoded rows and the kernel checks

As B3RowA / B3RuleA / B3WitA for core A, plus the lex families (23, 24, 27 definitions, 25 rules) and the four units
(family 30).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-- The name chunks of core B (200 names each). -/
def chunksB : List (List V) :=
  [namesB0, namesB1, namesB2, namesB3, namesB4, namesB5, namesB6, namesB7, namesB8, namesB9, namesB10]

/-- The name of variable number `i` of core B (`i = 0` is the constant true). -/
def nmB (i : Nat) : Lit :=
  match i with
  | 0 => ltrue
  | j + 1 => (true, lget (lget chunksB (j / 200) []) (j % 200) V.tru)

/-- The literal of a code. -/
def litOfB (c : Nat) : Lit := if c % 2 == 0 then nmB (c / 2) else (nmB (c / 2)).neg

/-- The four units of core B: the atoms `fv 3 2 3`, `fv 3 2 5` are zero (`D ∥ H`). -/
def unitsB : List (List Lit) :=
  [[(false, V.fv 3 2 3)], [(false, V.ng (V.fv 3 2 3))], [(false, V.fv 3 2 5)], [(false, V.ng (V.fv 3 2 5))]]

/-- A packed row passes the non-rule check, or is a rule, witness, lex rule or unit row. -/
def rowDB (n : Nat) : Bool :=
  let r := decRow n
  let cl := r.2.2.map litOfB
  r.1 == 17 || r.1 == 19 || r.1 == 25 || r.1 == 30 || rowOK3 r.1 r.2.1 cl || lexDefOK r.1 cl

/-- A packed row is not a rule row, or its rule check passes. -/
def ruleDB (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 17 || ruleOK r.2.1 (r.2.2.map litOfB)

/-- A packed row is not a witness row, or its witness check passes. -/
def witDB (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 19 || witOK r.2.1 (r.2.2.map litOfB)

/-- A packed row is not a lex rule row, or its lex check passes. -/
def lexDB (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 25 || lexOK r.2.1 (r.2.2.map litOfB)

/-- A packed row is not a unit row, or it covers one of the four units. -/
def unitDB (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 30 || anyCov (r.2.2.map litOfB) unitsB

theorem bchunk0 : (rowsB0.all rowDB) = true := by decide +kernel
theorem bchunk1 : (rowsB1.all rowDB) = true := by decide +kernel
theorem bchunk2 : (rowsB2.all rowDB) = true := by decide +kernel
theorem bchunk3 : (rowsB3.all rowDB) = true := by decide +kernel
theorem bchunk4 : (rowsB4.all rowDB) = true := by decide +kernel
theorem bchunk5 : (rowsB5.all rowDB) = true := by decide +kernel
theorem bchunk6 : (rowsB6.all rowDB) = true := by decide +kernel

end Minimality.H21.SAT
