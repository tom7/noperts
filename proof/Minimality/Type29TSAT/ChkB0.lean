module

public import Minimality.Type29TSAT.DataB0
public import Minimality.Type29TSAT.TTop

@[expose] public section

/-!
# L29T, T7: core B0, the kernel checks of all rows and the theorem `rupert_of_coreB0`

Core B0 is the case `b0 = [0134] = 0` (the tie file).  Its only class literal is the zero unit: the gate
`V.gate false p false q` with `p = [0134] > 0`, `q = [0134] < 0` (a `base` literal), true exactly when the bracket vanishes.
Every row of `rowsB0` passes `rowW` (menu rows un-lifted to the existing checks, tie families to the checkers of T3 to T6,
gates over `W`, the unit).  With the unsatisfiability of the numbered clauses (`CoreUnsat rowsB0`, from `ProofB0` via
`LinkB0`), every type 29 shape of the chirality `0 < [0123]` with `[0134] = 0` is Rupert.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29T.SAT
open Minimality.H29.SAT

/-- The class literal of core B0: the bracket `[0134]` is zero. -/
def unitsB0 : List LitW := [(true, W.base (V.gate false (V.br 0 1 3 4) false (V.ng (V.br 0 1 3 4))))]

/-- The row check of core B0. -/
def allDB0 (n : Nat) : Bool := rowW unitsB0 chunksB0 n

/-- Chunk 0 of core B0: all rows pass. -/
theorem chkB00 : (rowsB00.all allDB0) = true := by decide +kernel

/-- Chunk 1 of core B0: all rows pass. -/
theorem chkB01 : (rowsB01.all allDB0) = true := by decide +kernel

/-- Chunk 2 of core B0: all rows pass. -/
theorem chkB02 : (rowsB02.all allDB0) = true := by decide +kernel

/-- Chunk 3 of core B0: all rows pass. -/
theorem chkB03 : (rowsB03.all allDB0) = true := by decide +kernel

/-- Chunk 4 of core B0: all rows pass. -/
theorem chkB04 : (rowsB04.all allDB0) = true := by decide +kernel

/-- Chunk 5 of core B0: all rows pass. -/
theorem chkB05 : (rowsB05.all allDB0) = true := by decide +kernel

/-- Chunk 6 of core B0: all rows pass. -/
theorem chkB06 : (rowsB06.all allDB0) = true := by decide +kernel

/-- Chunk 7 of core B0: all rows pass. -/
theorem chkB07 : (rowsB07.all allDB0) = true := by decide +kernel

/-- Chunk 8 of core B0: all rows pass. -/
theorem chkB08 : (rowsB08.all allDB0) = true := by decide +kernel

/-- Chunk 9 of core B0: all rows pass. -/
theorem chkB09 : (rowsB09.all allDB0) = true := by decide +kernel

/-- Every row of core B0 passes the check. -/
theorem allOKB0 : ∀ ch ∈ rowsB0, ∀ n ∈ ch, allDB0 n = true := by
  intro ch hch n hn
  simp only [rowsB0, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkB00 n hn
  · exact List.all_eq_true.mp chkB01 n hn
  · exact List.all_eq_true.mp chkB02 n hn
  · exact List.all_eq_true.mp chkB03 n hn
  · exact List.all_eq_true.mp chkB04 n hn
  · exact List.all_eq_true.mp chkB05 n hn
  · exact List.all_eq_true.mp chkB06 n hn
  · exact List.all_eq_true.mp chkB07 n hn
  · exact List.all_eq_true.mp chkB08 n hn
  · exact List.all_eq_true.mp chkB09 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literal of core B0 is true of the real data when the bracket `[0134]` vanishes. -/
theorem unitsB0_true (F : S0xFac 9 s0x_S29 x) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) :
    ∀ l ∈ unitsB0, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  simp only [unitsB0, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl
  show evalL (rho (geoF F)) (true, V.gate false (V.br 0 1 3 4) false (V.ng (V.br 0 1 3 4))) = true
  simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]

/-- **Core B0 gives Rupert**: if the numbered clauses of core B0 are unsatisfiable, every type 29 shape with
`0 < [0123]` and `[0134] = 0` is Rupert. -/
theorem rupert_of_coreB0 (hU : CoreUnsat rowsB0) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) :
    IsRupert (univ.image x) :=
  caseW_of_unsat chunksB0 rowsB0 unitsB0 hU allOKB0 F hchir (unitsB0_true F h0)

end Minimality.H29T.SAT
