module

public import Minimality.Type24SAT.K24.DataPpzpm
public import Minimality.Type24SAT.K24.UnitsPpzpm

@[expose] public section

/-!
# Type 24, class ppzpm off the obtuse corner `OB1`: the kernel checks of all rows of core Ppzpm (dispatcher `rowK`, class
literals `unitsPpzpm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppzpm. -/
def allDPpzpm (n : Nat) : Bool := rowK unitsPpzpm clauseOB1 chunksPpzpm n

/-- Chunk 0 of core Ppzpm: all rows pass. -/
theorem chkPpzpm0 : (rowsPpzpm0.all allDPpzpm) = true := by decide +kernel

/-- Chunk 1 of core Ppzpm: all rows pass. -/
theorem chkPpzpm1 : (rowsPpzpm1.all allDPpzpm) = true := by decide +kernel

/-- Chunk 2 of core Ppzpm: all rows pass. -/
theorem chkPpzpm2 : (rowsPpzpm2.all allDPpzpm) = true := by decide +kernel

/-- Chunk 3 of core Ppzpm: all rows pass. -/
theorem chkPpzpm3 : (rowsPpzpm3.all allDPpzpm) = true := by decide +kernel

/-- Chunk 4 of core Ppzpm: all rows pass. -/
theorem chkPpzpm4 : (rowsPpzpm4.all allDPpzpm) = true := by decide +kernel

/-- Chunk 5 of core Ppzpm: all rows pass. -/
theorem chkPpzpm5 : (rowsPpzpm5.all allDPpzpm) = true := by decide +kernel

/-- Chunk 6 of core Ppzpm: all rows pass. -/
theorem chkPpzpm6 : (rowsPpzpm6.all allDPpzpm) = true := by decide +kernel

/-- Every row of core Ppzpm passes the check. -/
theorem allOKPpzpm : ∀ ch ∈ rowsPpzpm, ∀ n ∈ ch, allDPpzpm n = true := by
  intro ch hch n hn
  simp only [rowsPpzpm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpzpm0 n hn
  · exact List.all_eq_true.mp chkPpzpm1 n hn
  · exact List.all_eq_true.mp chkPpzpm2 n hn
  · exact List.all_eq_true.mp chkPpzpm3 n hn
  · exact List.all_eq_true.mp chkPpzpm4 n hn
  · exact List.all_eq_true.mp chkPpzpm5 n hn
  · exact List.all_eq_true.mp chkPpzpm6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppzpm gives Rupert**: if the numbered clauses of core Ppzpm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppzpm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpzpm (hU : Minimality.H24.SAT.CoreUnsat rowsPpzpm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpzpm rowsPpzpm unitsPpzpm clauseOB1 hU allOKPpzpm F hchir
    (unitsPpzpm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
