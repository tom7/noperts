module

public import Minimality.Type24SAT.K24.DataZpmpm
public import Minimality.Type24SAT.K24.UnitsZpmpm

@[expose] public section

/-!
# Type 24, class zpmpm off the obtuse corner `OB1`: the kernel checks of all rows of core Zpmpm (dispatcher `rowK`, class
literals `unitsZpmpm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Zpmpm. -/
def allDZpmpm (n : Nat) : Bool := rowK unitsZpmpm clauseOB1 chunksZpmpm n

/-- Chunk 0 of core Zpmpm: all rows pass. -/
theorem chkZpmpm0 : (rowsZpmpm0.all allDZpmpm) = true := by decide +kernel

/-- Chunk 1 of core Zpmpm: all rows pass. -/
theorem chkZpmpm1 : (rowsZpmpm1.all allDZpmpm) = true := by decide +kernel

/-- Chunk 2 of core Zpmpm: all rows pass. -/
theorem chkZpmpm2 : (rowsZpmpm2.all allDZpmpm) = true := by decide +kernel

/-- Chunk 3 of core Zpmpm: all rows pass. -/
theorem chkZpmpm3 : (rowsZpmpm3.all allDZpmpm) = true := by decide +kernel

/-- Chunk 4 of core Zpmpm: all rows pass. -/
theorem chkZpmpm4 : (rowsZpmpm4.all allDZpmpm) = true := by decide +kernel

/-- Chunk 5 of core Zpmpm: all rows pass. -/
theorem chkZpmpm5 : (rowsZpmpm5.all allDZpmpm) = true := by decide +kernel

/-- Chunk 6 of core Zpmpm: all rows pass. -/
theorem chkZpmpm6 : (rowsZpmpm6.all allDZpmpm) = true := by decide +kernel

/-- Chunk 7 of core Zpmpm: all rows pass. -/
theorem chkZpmpm7 : (rowsZpmpm7.all allDZpmpm) = true := by decide +kernel

/-- Every row of core Zpmpm passes the check. -/
theorem allOKZpmpm : ∀ ch ∈ rowsZpmpm, ∀ n ∈ ch, allDZpmpm n = true := by
  intro ch hch n hn
  simp only [rowsZpmpm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpmpm0 n hn
  · exact List.all_eq_true.mp chkZpmpm1 n hn
  · exact List.all_eq_true.mp chkZpmpm2 n hn
  · exact List.all_eq_true.mp chkZpmpm3 n hn
  · exact List.all_eq_true.mp chkZpmpm4 n hn
  · exact List.all_eq_true.mp chkZpmpm5 n hn
  · exact List.all_eq_true.mp chkZpmpm6 n hn
  · exact List.all_eq_true.mp chkZpmpm7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Zpmpm gives Rupert**: if the numbered clauses of core Zpmpm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpmpm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpmpm (hU : Minimality.H24.SAT.CoreUnsat rowsZpmpm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksZpmpm rowsZpmpm unitsZpmpm clauseOB1 hU allOKZpmpm F hchir
    (unitsZpmpm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
