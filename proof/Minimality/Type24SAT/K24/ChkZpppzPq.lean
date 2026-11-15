module

public import Minimality.Type24SAT.K24.DataZpppzPq
public import Minimality.Type24SAT.K24.UnitsZpppzPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class zpppz off the obtuse corner `OB1`: the kernel checks of all rows of core ZpppzPq (dispatcher `rowK`, class
literals `unitsZpppzPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core ZpppzPq. -/
def allDZpppzPq (n : Nat) : Bool := rowKs unitsZpppzPq clausesPq chunksZpppzPq n

/-- Chunk 0 of core ZpppzPq: all rows pass. -/
theorem chkZpppzPq0 : (rowsZpppzPq0.all allDZpppzPq) = true := by decide +kernel

/-- Chunk 1 of core ZpppzPq: all rows pass. -/
theorem chkZpppzPq1 : (rowsZpppzPq1.all allDZpppzPq) = true := by decide +kernel

/-- Chunk 2 of core ZpppzPq: all rows pass. -/
theorem chkZpppzPq2 : (rowsZpppzPq2.all allDZpppzPq) = true := by decide +kernel

/-- Chunk 3 of core ZpppzPq: all rows pass. -/
theorem chkZpppzPq3 : (rowsZpppzPq3.all allDZpppzPq) = true := by decide +kernel

/-- Chunk 4 of core ZpppzPq: all rows pass. -/
theorem chkZpppzPq4 : (rowsZpppzPq4.all allDZpppzPq) = true := by decide +kernel

/-- Every row of core ZpppzPq passes the check. -/
theorem allOKZpppzPq : ∀ ch ∈ rowsZpppzPq, ∀ n ∈ ch, allDZpppzPq n = true := by
  intro ch hch n hn
  simp only [rowsZpppzPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpppzPq0 n hn
  · exact List.all_eq_true.mp chkZpppzPq1 n hn
  · exact List.all_eq_true.mp chkZpppzPq2 n hn
  · exact List.all_eq_true.mp chkZpppzPq3 n hn
  · exact List.all_eq_true.mp chkZpppzPq4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core ZpppzPq gives Rupert**: if the numbered clauses of core ZpppzPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpppzpq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpppzPq (hU : Minimality.H24.SAT.CoreUnsat rowsZpppzPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksZpppzPq rowsZpppzPq unitsZpppzPq clausesPq hU allOKZpppzPq F hchir
    (unitsZpppzPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
