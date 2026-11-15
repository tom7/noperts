module

public import Minimality.Type24SAT.K24.DataPzpppNotP
public import Minimality.Type24SAT.K24.UnitsPzpppNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class pzppp off the obtuse corner `OB1`: the kernel checks of all rows of core PzpppNotP (dispatcher `rowK`, class
literals `unitsPzpppNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PzpppNotP. -/
def allDPzpppNotP (n : Nat) : Bool := rowKs unitsPzpppNotP clausesNotP chunksPzpppNotP n

/-- Chunk 0 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP0 : (rowsPzpppNotP0.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 1 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP1 : (rowsPzpppNotP1.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 2 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP2 : (rowsPzpppNotP2.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 3 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP3 : (rowsPzpppNotP3.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 4 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP4 : (rowsPzpppNotP4.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 5 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP5 : (rowsPzpppNotP5.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 6 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP6 : (rowsPzpppNotP6.all allDPzpppNotP) = true := by decide +kernel

/-- Chunk 7 of core PzpppNotP: all rows pass. -/
theorem chkPzpppNotP7 : (rowsPzpppNotP7.all allDPzpppNotP) = true := by decide +kernel

/-- Every row of core PzpppNotP passes the check. -/
theorem allOKPzpppNotP : ∀ ch ∈ rowsPzpppNotP, ∀ n ∈ ch, allDPzpppNotP n = true := by
  intro ch hch n hn
  simp only [rowsPzpppNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPzpppNotP0 n hn
  · exact List.all_eq_true.mp chkPzpppNotP1 n hn
  · exact List.all_eq_true.mp chkPzpppNotP2 n hn
  · exact List.all_eq_true.mp chkPzpppNotP3 n hn
  · exact List.all_eq_true.mp chkPzpppNotP4 n hn
  · exact List.all_eq_true.mp chkPzpppNotP5 n hn
  · exact List.all_eq_true.mp chkPzpppNotP6 n hn
  · exact List.all_eq_true.mp chkPzpppNotP7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PzpppNotP gives Rupert**: if the numbered clauses of core PzpppNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pzpppnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePzpppNotP (hU : Minimality.H24.SAT.CoreUnsat rowsPzpppNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) = 0)
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPzpppNotP rowsPzpppNotP unitsPzpppNotP clausesNotP hU allOKPzpppNotP F hchir
    (unitsPzpppNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
