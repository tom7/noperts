module

public import Minimality.Type29KSAT.DataK1aOB
public import Minimality.Type29KSAT.NfZB
public import Minimality.Type29KSAT.K1CornerOB

@[expose] public section

/-!
# Type 29, class K1a off the obtuse corner `OB6`: core K1aOB, the kernel checks of all rows (dispatcher `rowKs`, class
literals `unitsK1aB` and the clause `clausesOB`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT Minimality.H29K1

/-- The row check of core K1aOB. -/
def allDK1aOB (n : Nat) : Bool := rowKs unitsK1aB clausesOB chunksK1aOB n

/-- Chunk 0 of core K1aOB: all rows pass. -/
theorem chkK1aOB0 : (rowsK1aOB0.all allDK1aOB) = true := by decide +kernel

/-- Chunk 1 of core K1aOB: all rows pass. -/
theorem chkK1aOB1 : (rowsK1aOB1.all allDK1aOB) = true := by decide +kernel

/-- Chunk 2 of core K1aOB: all rows pass. -/
theorem chkK1aOB2 : (rowsK1aOB2.all allDK1aOB) = true := by decide +kernel

/-- Chunk 3 of core K1aOB: all rows pass. -/
theorem chkK1aOB3 : (rowsK1aOB3.all allDK1aOB) = true := by decide +kernel

/-- Chunk 4 of core K1aOB: all rows pass. -/
theorem chkK1aOB4 : (rowsK1aOB4.all allDK1aOB) = true := by decide +kernel

/-- Chunk 5 of core K1aOB: all rows pass. -/
theorem chkK1aOB5 : (rowsK1aOB5.all allDK1aOB) = true := by decide +kernel

/-- Chunk 6 of core K1aOB: all rows pass. -/
theorem chkK1aOB6 : (rowsK1aOB6.all allDK1aOB) = true := by decide +kernel

/-- Chunk 7 of core K1aOB: all rows pass. -/
theorem chkK1aOB7 : (rowsK1aOB7.all allDK1aOB) = true := by decide +kernel

/-- Chunk 8 of core K1aOB: all rows pass. -/
theorem chkK1aOB8 : (rowsK1aOB8.all allDK1aOB) = true := by decide +kernel

/-- Chunk 9 of core K1aOB: all rows pass. -/
theorem chkK1aOB9 : (rowsK1aOB9.all allDK1aOB) = true := by decide +kernel

/-- Every row of core K1aOB passes the check. -/
theorem allOKK1aOB : ∀ ch ∈ rowsK1aOB, ∀ n ∈ ch, allDK1aOB n = true := by
  intro ch hch n hn
  simp only [rowsK1aOB, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkK1aOB0 n hn
  · exact List.all_eq_true.mp chkK1aOB1 n hn
  · exact List.all_eq_true.mp chkK1aOB2 n hn
  · exact List.all_eq_true.mp chkK1aOB3 n hn
  · exact List.all_eq_true.mp chkK1aOB4 n hn
  · exact List.all_eq_true.mp chkK1aOB5 n hn
  · exact List.all_eq_true.mp chkK1aOB6 n hn
  · exact List.all_eq_true.mp chkK1aOB7 n hn
  · exact List.all_eq_true.mp chkK1aOB8 n hn
  · exact List.all_eq_true.mp chkK1aOB9 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core K1aOB gives Rupert**: if the numbered clauses of core K1aOB are unsatisfiable, every type 29 shape with
`0 < [0123]`, `0 < [0134]`, `[0245] < 0`, `[1235] < 0` and an acute face angle at vertex `6` is Rupert. -/
theorem rupert_of_coreK1aOB (hU : CoreUnsat rowsK1aOB) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0))
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hO : ¬ OB6 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksK1aOB rowsK1aOB unitsK1aB clausesOB hU allOKK1aOB F hchir
    (unitsK1aB_true F h0 h1 h2) (clausesOB_true F hO))

end Minimality.H29K.SAT
