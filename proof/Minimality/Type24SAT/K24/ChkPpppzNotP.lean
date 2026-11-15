module

public import Minimality.Type24SAT.K24.DataPpppzNotP
public import Minimality.Type24SAT.K24.UnitsPpppzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class ppppz off the obtuse corner `OB1`: the kernel checks of all rows of core PpppzNotP (dispatcher `rowK`, class
literals `unitsPpppzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PpppzNotP. -/
def allDPpppzNotP (n : Nat) : Bool := rowKs unitsPpppzNotP clausesNotP chunksPpppzNotP n

/-- Chunk 0 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP0 : (rowsPpppzNotP0.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 1 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP1 : (rowsPpppzNotP1.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 2 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP2 : (rowsPpppzNotP2.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 3 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP3 : (rowsPpppzNotP3.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 4 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP4 : (rowsPpppzNotP4.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 5 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP5 : (rowsPpppzNotP5.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 6 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP6 : (rowsPpppzNotP6.all allDPpppzNotP) = true := by decide +kernel

/-- Chunk 7 of core PpppzNotP: all rows pass. -/
theorem chkPpppzNotP7 : (rowsPpppzNotP7.all allDPpppzNotP) = true := by decide +kernel

/-- Every row of core PpppzNotP passes the check. -/
theorem allOKPpppzNotP : ∀ ch ∈ rowsPpppzNotP, ∀ n ∈ ch, allDPpppzNotP n = true := by
  intro ch hch n hn
  simp only [rowsPpppzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpppzNotP0 n hn
  · exact List.all_eq_true.mp chkPpppzNotP1 n hn
  · exact List.all_eq_true.mp chkPpppzNotP2 n hn
  · exact List.all_eq_true.mp chkPpppzNotP3 n hn
  · exact List.all_eq_true.mp chkPpppzNotP4 n hn
  · exact List.all_eq_true.mp chkPpppzNotP5 n hn
  · exact List.all_eq_true.mp chkPpppzNotP6 n hn
  · exact List.all_eq_true.mp chkPpppzNotP7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PpppzNotP gives Rupert**: if the numbered clauses of core PpppzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppppznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpppzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsPpppzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPpppzNotP rowsPpppzNotP unitsPpppzNotP clausesNotP hU allOKPpppzNotP F hchir
    (unitsPpppzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
