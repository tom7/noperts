module

public import Minimality.Type24SAT.K24.DataPpmpzNotP
public import Minimality.Type24SAT.K24.UnitsPpmpzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class ppmpz off the obtuse corner `OB1`: the kernel checks of all rows of core PpmpzNotP (dispatcher `rowK`, class
literals `unitsPpmpzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PpmpzNotP. -/
def allDPpmpzNotP (n : Nat) : Bool := rowKs unitsPpmpzNotP clausesNotP chunksPpmpzNotP n

/-- Chunk 0 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP0 : (rowsPpmpzNotP0.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 1 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP1 : (rowsPpmpzNotP1.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 2 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP2 : (rowsPpmpzNotP2.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 3 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP3 : (rowsPpmpzNotP3.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 4 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP4 : (rowsPpmpzNotP4.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 5 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP5 : (rowsPpmpzNotP5.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 6 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP6 : (rowsPpmpzNotP6.all allDPpmpzNotP) = true := by decide +kernel

/-- Chunk 7 of core PpmpzNotP: all rows pass. -/
theorem chkPpmpzNotP7 : (rowsPpmpzNotP7.all allDPpmpzNotP) = true := by decide +kernel

/-- Every row of core PpmpzNotP passes the check. -/
theorem allOKPpmpzNotP : ∀ ch ∈ rowsPpmpzNotP, ∀ n ∈ ch, allDPpmpzNotP n = true := by
  intro ch hch n hn
  simp only [rowsPpmpzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpmpzNotP0 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP1 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP2 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP3 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP4 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP5 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP6 n hn
  · exact List.all_eq_true.mp chkPpmpzNotP7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PpmpzNotP gives Rupert**: if the numbered clauses of core PpmpzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppmpznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpmpzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsPpmpzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPpmpzNotP rowsPpmpzNotP unitsPpmpzNotP clausesNotP hU allOKPpmpzNotP F hchir
    (unitsPpmpzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
