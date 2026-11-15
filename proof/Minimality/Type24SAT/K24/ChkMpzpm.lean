module

public import Minimality.Type24SAT.K24.DataMpzpm
public import Minimality.Type24SAT.K24.UnitsMpzpm

@[expose] public section

/-!
# Type 24, class mpzpm off the obtuse corner `OB1`: the kernel checks of all rows of core Mpzpm (dispatcher `rowK`, class
literals `unitsMpzpm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Mpzpm. -/
def allDMpzpm (n : Nat) : Bool := rowK unitsMpzpm clauseOB1 chunksMpzpm n

/-- Chunk 0 of core Mpzpm: all rows pass. -/
theorem chkMpzpm0 : (rowsMpzpm0.all allDMpzpm) = true := by decide +kernel

/-- Chunk 1 of core Mpzpm: all rows pass. -/
theorem chkMpzpm1 : (rowsMpzpm1.all allDMpzpm) = true := by decide +kernel

/-- Chunk 2 of core Mpzpm: all rows pass. -/
theorem chkMpzpm2 : (rowsMpzpm2.all allDMpzpm) = true := by decide +kernel

/-- Chunk 3 of core Mpzpm: all rows pass. -/
theorem chkMpzpm3 : (rowsMpzpm3.all allDMpzpm) = true := by decide +kernel

/-- Chunk 4 of core Mpzpm: all rows pass. -/
theorem chkMpzpm4 : (rowsMpzpm4.all allDMpzpm) = true := by decide +kernel

/-- Chunk 5 of core Mpzpm: all rows pass. -/
theorem chkMpzpm5 : (rowsMpzpm5.all allDMpzpm) = true := by decide +kernel

/-- Every row of core Mpzpm passes the check. -/
theorem allOKMpzpm : ∀ ch ∈ rowsMpzpm, ∀ n ∈ ch, allDMpzpm n = true := by
  intro ch hch n hn
  simp only [rowsMpzpm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpzpm0 n hn
  · exact List.all_eq_true.mp chkMpzpm1 n hn
  · exact List.all_eq_true.mp chkMpzpm2 n hn
  · exact List.all_eq_true.mp chkMpzpm3 n hn
  · exact List.all_eq_true.mp chkMpzpm4 n hn
  · exact List.all_eq_true.mp chkMpzpm5 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Mpzpm gives Rupert**: if the numbered clauses of core Mpzpm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpzpm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpzpm (hU : Minimality.H24.SAT.CoreUnsat rowsMpzpm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksMpzpm rowsMpzpm unitsMpzpm clauseOB1 hU allOKMpzpm F hchir
    (unitsMpzpm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
