module

public import Minimality.Type24SAT.K24.DataZpmpzNotP
public import Minimality.Type24SAT.K24.UnitsZpmpzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class zpmpz off the obtuse corner `OB1`: the kernel checks of all rows of core ZpmpzNotP (dispatcher `rowK`, class
literals `unitsZpmpzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core ZpmpzNotP. -/
def allDZpmpzNotP (n : Nat) : Bool := rowKs unitsZpmpzNotP clausesNotP chunksZpmpzNotP n

/-- Chunk 0 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP0 : (rowsZpmpzNotP0.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 1 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP1 : (rowsZpmpzNotP1.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 2 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP2 : (rowsZpmpzNotP2.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 3 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP3 : (rowsZpmpzNotP3.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 4 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP4 : (rowsZpmpzNotP4.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 5 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP5 : (rowsZpmpzNotP5.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 6 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP6 : (rowsZpmpzNotP6.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 7 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP7 : (rowsZpmpzNotP7.all allDZpmpzNotP) = true := by decide +kernel

/-- Chunk 8 of core ZpmpzNotP: all rows pass. -/
theorem chkZpmpzNotP8 : (rowsZpmpzNotP8.all allDZpmpzNotP) = true := by decide +kernel

/-- Every row of core ZpmpzNotP passes the check. -/
theorem allOKZpmpzNotP : ∀ ch ∈ rowsZpmpzNotP, ∀ n ∈ ch, allDZpmpzNotP n = true := by
  intro ch hch n hn
  simp only [rowsZpmpzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpmpzNotP0 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP1 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP2 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP3 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP4 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP5 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP6 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP7 n hn
  · exact List.all_eq_true.mp chkZpmpzNotP8 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core ZpmpzNotP gives Rupert**: if the numbered clauses of core ZpmpzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpmpznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpmpzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsZpmpzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksZpmpzNotP rowsZpmpzNotP unitsZpmpzNotP clausesNotP hU allOKZpmpzNotP F hchir
    (unitsZpmpzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
