module

public import Minimality.Type24SAT.K24.DataZpppm
public import Minimality.Type24SAT.K24.UnitsZpppm

@[expose] public section

/-!
# Type 24, class zpppm off the obtuse corner `OB1`: the kernel checks of all rows of core Zpppm (dispatcher `rowK`, class
literals `unitsZpppm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Zpppm. -/
def allDZpppm (n : Nat) : Bool := rowK unitsZpppm clauseOB1 chunksZpppm n

/-- Chunk 0 of core Zpppm: all rows pass. -/
theorem chkZpppm0 : (rowsZpppm0.all allDZpppm) = true := by decide +kernel

/-- Chunk 1 of core Zpppm: all rows pass. -/
theorem chkZpppm1 : (rowsZpppm1.all allDZpppm) = true := by decide +kernel

/-- Chunk 2 of core Zpppm: all rows pass. -/
theorem chkZpppm2 : (rowsZpppm2.all allDZpppm) = true := by decide +kernel

/-- Chunk 3 of core Zpppm: all rows pass. -/
theorem chkZpppm3 : (rowsZpppm3.all allDZpppm) = true := by decide +kernel

/-- Chunk 4 of core Zpppm: all rows pass. -/
theorem chkZpppm4 : (rowsZpppm4.all allDZpppm) = true := by decide +kernel

/-- Every row of core Zpppm passes the check. -/
theorem allOKZpppm : ∀ ch ∈ rowsZpppm, ∀ n ∈ ch, allDZpppm n = true := by
  intro ch hch n hn
  simp only [rowsZpppm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpppm0 n hn
  · exact List.all_eq_true.mp chkZpppm1 n hn
  · exact List.all_eq_true.mp chkZpppm2 n hn
  · exact List.all_eq_true.mp chkZpppm3 n hn
  · exact List.all_eq_true.mp chkZpppm4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Zpppm gives Rupert**: if the numbered clauses of core Zpppm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpppm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpppm (hU : Minimality.H24.SAT.CoreUnsat rowsZpppm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksZpppm rowsZpppm unitsZpppm clauseOB1 hU allOKZpppm F hchir
    (unitsZpppm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
