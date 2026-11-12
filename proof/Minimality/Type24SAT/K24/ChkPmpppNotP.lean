module

public import Minimality.Type24SAT.K24.DataPmpppNotP
public import Minimality.Type24SAT.K24.UnitsPmpppNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class pmppp off the obtuse corner `OB1`: the kernel checks of all rows of core PmpppNotP (dispatcher `rowK`, class
literals `unitsPmpppNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PmpppNotP. -/
def allDPmpppNotP (n : Nat) : Bool := rowKs unitsPmpppNotP clausesNotP chunksPmpppNotP n

/-- Chunk 0 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP0 : (rowsPmpppNotP0.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 1 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP1 : (rowsPmpppNotP1.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 2 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP2 : (rowsPmpppNotP2.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 3 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP3 : (rowsPmpppNotP3.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 4 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP4 : (rowsPmpppNotP4.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 5 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP5 : (rowsPmpppNotP5.all allDPmpppNotP) = true := by decide +kernel

/-- Chunk 6 of core PmpppNotP: all rows pass. -/
theorem chkPmpppNotP6 : (rowsPmpppNotP6.all allDPmpppNotP) = true := by decide +kernel

/-- Every row of core PmpppNotP passes the check. -/
theorem allOKPmpppNotP : ∀ ch ∈ rowsPmpppNotP, ∀ n ∈ ch, allDPmpppNotP n = true := by
  intro ch hch n hn
  simp only [rowsPmpppNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPmpppNotP0 n hn
  · exact List.all_eq_true.mp chkPmpppNotP1 n hn
  · exact List.all_eq_true.mp chkPmpppNotP2 n hn
  · exact List.all_eq_true.mp chkPmpppNotP3 n hn
  · exact List.all_eq_true.mp chkPmpppNotP4 n hn
  · exact List.all_eq_true.mp chkPmpppNotP5 n hn
  · exact List.all_eq_true.mp chkPmpppNotP6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PmpppNotP gives Rupert**: if the numbered clauses of core PmpppNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pmpppnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePmpppNotP (hU : Minimality.H24.SAT.CoreUnsat rowsPmpppNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0)
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPmpppNotP rowsPmpppNotP unitsPmpppNotP clausesNotP hU allOKPmpppNotP F hchir
    (unitsPmpppNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
