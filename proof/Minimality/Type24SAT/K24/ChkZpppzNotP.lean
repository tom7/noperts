module

public import Minimality.Type24SAT.K24.DataZpppzNotP
public import Minimality.Type24SAT.K24.UnitsZpppzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class zpppz off the obtuse corner `OB1`: the kernel checks of all rows of core ZpppzNotP (dispatcher `rowK`, class
literals `unitsZpppzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core ZpppzNotP. -/
def allDZpppzNotP (n : Nat) : Bool := rowKs unitsZpppzNotP clausesNotP chunksZpppzNotP n

/-- Chunk 0 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP0 : (rowsZpppzNotP0.all allDZpppzNotP) = true := by decide +kernel

/-- Chunk 1 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP1 : (rowsZpppzNotP1.all allDZpppzNotP) = true := by decide +kernel

/-- Chunk 2 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP2 : (rowsZpppzNotP2.all allDZpppzNotP) = true := by decide +kernel

/-- Chunk 3 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP3 : (rowsZpppzNotP3.all allDZpppzNotP) = true := by decide +kernel

/-- Chunk 4 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP4 : (rowsZpppzNotP4.all allDZpppzNotP) = true := by decide +kernel

/-- Chunk 5 of core ZpppzNotP: all rows pass. -/
theorem chkZpppzNotP5 : (rowsZpppzNotP5.all allDZpppzNotP) = true := by decide +kernel

/-- Every row of core ZpppzNotP passes the check. -/
theorem allOKZpppzNotP : ∀ ch ∈ rowsZpppzNotP, ∀ n ∈ ch, allDZpppzNotP n = true := by
  intro ch hch n hn
  simp only [rowsZpppzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpppzNotP0 n hn
  · exact List.all_eq_true.mp chkZpppzNotP1 n hn
  · exact List.all_eq_true.mp chkZpppzNotP2 n hn
  · exact List.all_eq_true.mp chkZpppzNotP3 n hn
  · exact List.all_eq_true.mp chkZpppzNotP4 n hn
  · exact List.all_eq_true.mp chkZpppzNotP5 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core ZpppzNotP gives Rupert**: if the numbered clauses of core ZpppzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpppznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpppzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsZpppzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksZpppzNotP rowsZpppzNotP unitsZpppzNotP clausesNotP hU allOKZpppzNotP F hchir
    (unitsZpppzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
