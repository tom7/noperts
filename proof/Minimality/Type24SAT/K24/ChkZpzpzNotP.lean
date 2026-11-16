module

public import Minimality.Type24SAT.K24.DataZpzpzNotP
public import Minimality.Type24SAT.K24.UnitsZpzpzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class zpzpz off the obtuse corner `OB1`: the kernel checks of all rows of core ZpzpzNotP (dispatcher `rowK`, class
literals `unitsZpzpzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core ZpzpzNotP. -/
def allDZpzpzNotP (n : Nat) : Bool := rowKs unitsZpzpzNotP clausesNotP chunksZpzpzNotP n

/-- Chunk 0 of core ZpzpzNotP: all rows pass. -/
theorem chkZpzpzNotP0 : (rowsZpzpzNotP0.all allDZpzpzNotP) = true := by decide +kernel

/-- Chunk 1 of core ZpzpzNotP: all rows pass. -/
theorem chkZpzpzNotP1 : (rowsZpzpzNotP1.all allDZpzpzNotP) = true := by decide +kernel

/-- Chunk 2 of core ZpzpzNotP: all rows pass. -/
theorem chkZpzpzNotP2 : (rowsZpzpzNotP2.all allDZpzpzNotP) = true := by decide +kernel

/-- Chunk 3 of core ZpzpzNotP: all rows pass. -/
theorem chkZpzpzNotP3 : (rowsZpzpzNotP3.all allDZpzpzNotP) = true := by decide +kernel

/-- Chunk 4 of core ZpzpzNotP: all rows pass. -/
theorem chkZpzpzNotP4 : (rowsZpzpzNotP4.all allDZpzpzNotP) = true := by decide +kernel

/-- Every row of core ZpzpzNotP passes the check. -/
theorem allOKZpzpzNotP : ∀ ch ∈ rowsZpzpzNotP, ∀ n ∈ ch, allDZpzpzNotP n = true := by
  intro ch hch n hn
  simp only [rowsZpzpzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpzpzNotP0 n hn
  · exact List.all_eq_true.mp chkZpzpzNotP1 n hn
  · exact List.all_eq_true.mp chkZpzpzNotP2 n hn
  · exact List.all_eq_true.mp chkZpzpzNotP3 n hn
  · exact List.all_eq_true.mp chkZpzpzNotP4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core ZpzpzNotP gives Rupert**: if the numbered clauses of core ZpzpzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpzpznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpzpzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsZpzpzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksZpzpzNotP rowsZpzpzNotP unitsZpzpzNotP clausesNotP hU allOKZpzpzNotP F hchir
    (unitsZpzpzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
