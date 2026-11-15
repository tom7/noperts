module

public import Minimality.Type24SAT.K24.DataZpmpzPq
public import Minimality.Type24SAT.K24.UnitsZpmpzPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class zpmpz off the obtuse corner `OB1`: the kernel checks of all rows of core ZpmpzPq (dispatcher `rowK`, class
literals `unitsZpmpzPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core ZpmpzPq. -/
def allDZpmpzPq (n : Nat) : Bool := rowKs unitsZpmpzPq clausesPq chunksZpmpzPq n

/-- Chunk 0 of core ZpmpzPq: all rows pass. -/
theorem chkZpmpzPq0 : (rowsZpmpzPq0.all allDZpmpzPq) = true := by decide +kernel

/-- Chunk 1 of core ZpmpzPq: all rows pass. -/
theorem chkZpmpzPq1 : (rowsZpmpzPq1.all allDZpmpzPq) = true := by decide +kernel

/-- Chunk 2 of core ZpmpzPq: all rows pass. -/
theorem chkZpmpzPq2 : (rowsZpmpzPq2.all allDZpmpzPq) = true := by decide +kernel

/-- Chunk 3 of core ZpmpzPq: all rows pass. -/
theorem chkZpmpzPq3 : (rowsZpmpzPq3.all allDZpmpzPq) = true := by decide +kernel

/-- Every row of core ZpmpzPq passes the check. -/
theorem allOKZpmpzPq : ∀ ch ∈ rowsZpmpzPq, ∀ n ∈ ch, allDZpmpzPq n = true := by
  intro ch hch n hn
  simp only [rowsZpmpzPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpmpzPq0 n hn
  · exact List.all_eq_true.mp chkZpmpzPq1 n hn
  · exact List.all_eq_true.mp chkZpmpzPq2 n hn
  · exact List.all_eq_true.mp chkZpmpzPq3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core ZpmpzPq gives Rupert**: if the numbered clauses of core ZpmpzPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpmpzpq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpmpzPq (hU : Minimality.H24.SAT.CoreUnsat rowsZpmpzPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksZpmpzPq rowsZpmpzPq unitsZpmpzPq clausesPq hU allOKZpmpzPq F hchir
    (unitsZpmpzPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
