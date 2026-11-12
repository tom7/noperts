module

public import Minimality.Type24SAT.K24.DataPpppm
public import Minimality.Type24SAT.K24.UnitsPpppm

@[expose] public section

/-!
# Type 24, class ppppm off the obtuse corner `OB1`: the kernel checks of all rows of core Ppppm (dispatcher `rowK`, class
literals `unitsPpppm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppppm. -/
def allDPpppm (n : Nat) : Bool := rowK unitsPpppm clauseOB1 chunksPpppm n

/-- Chunk 0 of core Ppppm: all rows pass. -/
theorem chkPpppm0 : (rowsPpppm0.all allDPpppm) = true := by decide +kernel

/-- Chunk 1 of core Ppppm: all rows pass. -/
theorem chkPpppm1 : (rowsPpppm1.all allDPpppm) = true := by decide +kernel

/-- Chunk 2 of core Ppppm: all rows pass. -/
theorem chkPpppm2 : (rowsPpppm2.all allDPpppm) = true := by decide +kernel

/-- Chunk 3 of core Ppppm: all rows pass. -/
theorem chkPpppm3 : (rowsPpppm3.all allDPpppm) = true := by decide +kernel

/-- Chunk 4 of core Ppppm: all rows pass. -/
theorem chkPpppm4 : (rowsPpppm4.all allDPpppm) = true := by decide +kernel

/-- Chunk 5 of core Ppppm: all rows pass. -/
theorem chkPpppm5 : (rowsPpppm5.all allDPpppm) = true := by decide +kernel

/-- Chunk 6 of core Ppppm: all rows pass. -/
theorem chkPpppm6 : (rowsPpppm6.all allDPpppm) = true := by decide +kernel

/-- Every row of core Ppppm passes the check. -/
theorem allOKPpppm : ∀ ch ∈ rowsPpppm, ∀ n ∈ ch, allDPpppm n = true := by
  intro ch hch n hn
  simp only [rowsPpppm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpppm0 n hn
  · exact List.all_eq_true.mp chkPpppm1 n hn
  · exact List.all_eq_true.mp chkPpppm2 n hn
  · exact List.all_eq_true.mp chkPpppm3 n hn
  · exact List.all_eq_true.mp chkPpppm4 n hn
  · exact List.all_eq_true.mp chkPpppm5 n hn
  · exact List.all_eq_true.mp chkPpppm6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppppm gives Rupert**: if the numbered clauses of core Ppppm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppppm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpppm (hU : Minimality.H24.SAT.CoreUnsat rowsPpppm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpppm rowsPpppm unitsPpppm clauseOB1 hU allOKPpppm F hchir
    (unitsPpppm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
