module

public import Minimality.Type24SAT.K24.DataPpmpm
public import Minimality.Type24SAT.K24.UnitsPpmpm

@[expose] public section

/-!
# Type 24, class ppmpm off the obtuse corner `OB1`: the kernel checks of all rows of core Ppmpm (dispatcher `rowK`, class
literals `unitsPpmpm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppmpm. -/
def allDPpmpm (n : Nat) : Bool := rowK unitsPpmpm clauseOB1 chunksPpmpm n

/-- Chunk 0 of core Ppmpm: all rows pass. -/
theorem chkPpmpm0 : (rowsPpmpm0.all allDPpmpm) = true := by decide +kernel

/-- Chunk 1 of core Ppmpm: all rows pass. -/
theorem chkPpmpm1 : (rowsPpmpm1.all allDPpmpm) = true := by decide +kernel

/-- Chunk 2 of core Ppmpm: all rows pass. -/
theorem chkPpmpm2 : (rowsPpmpm2.all allDPpmpm) = true := by decide +kernel

/-- Chunk 3 of core Ppmpm: all rows pass. -/
theorem chkPpmpm3 : (rowsPpmpm3.all allDPpmpm) = true := by decide +kernel

/-- Chunk 4 of core Ppmpm: all rows pass. -/
theorem chkPpmpm4 : (rowsPpmpm4.all allDPpmpm) = true := by decide +kernel

/-- Chunk 5 of core Ppmpm: all rows pass. -/
theorem chkPpmpm5 : (rowsPpmpm5.all allDPpmpm) = true := by decide +kernel

/-- Chunk 6 of core Ppmpm: all rows pass. -/
theorem chkPpmpm6 : (rowsPpmpm6.all allDPpmpm) = true := by decide +kernel

/-- Chunk 7 of core Ppmpm: all rows pass. -/
theorem chkPpmpm7 : (rowsPpmpm7.all allDPpmpm) = true := by decide +kernel

/-- Every row of core Ppmpm passes the check. -/
theorem allOKPpmpm : ∀ ch ∈ rowsPpmpm, ∀ n ∈ ch, allDPpmpm n = true := by
  intro ch hch n hn
  simp only [rowsPpmpm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpmpm0 n hn
  · exact List.all_eq_true.mp chkPpmpm1 n hn
  · exact List.all_eq_true.mp chkPpmpm2 n hn
  · exact List.all_eq_true.mp chkPpmpm3 n hn
  · exact List.all_eq_true.mp chkPpmpm4 n hn
  · exact List.all_eq_true.mp chkPpmpm5 n hn
  · exact List.all_eq_true.mp chkPpmpm6 n hn
  · exact List.all_eq_true.mp chkPpmpm7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppmpm gives Rupert**: if the numbered clauses of core Ppmpm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppmpm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpmpm (hU : Minimality.H24.SAT.CoreUnsat rowsPpmpm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpmpm rowsPpmpm unitsPpmpm clauseOB1 hU allOKPpmpm F hchir
    (unitsPpmpm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
