module

public import Minimality.Type24SAT.K24.DataMpmzmPq
public import Minimality.Type24SAT.K24.UnitsMpmzmPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpmzm off the obtuse corner `OB1`: the kernel checks of all rows of core MpmzmPq (dispatcher `rowK`, class
literals `unitsMpmzmPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpmzmPq. -/
def allDMpmzmPq (n : Nat) : Bool := rowKs unitsMpmzmPq clausesPq chunksMpmzmPq n

/-- Chunk 0 of core MpmzmPq: all rows pass. -/
theorem chkMpmzmPq0 : (rowsMpmzmPq0.all allDMpmzmPq) = true := by decide +kernel

/-- Chunk 1 of core MpmzmPq: all rows pass. -/
theorem chkMpmzmPq1 : (rowsMpmzmPq1.all allDMpmzmPq) = true := by decide +kernel

/-- Chunk 2 of core MpmzmPq: all rows pass. -/
theorem chkMpmzmPq2 : (rowsMpmzmPq2.all allDMpmzmPq) = true := by decide +kernel

/-- Chunk 3 of core MpmzmPq: all rows pass. -/
theorem chkMpmzmPq3 : (rowsMpmzmPq3.all allDMpmzmPq) = true := by decide +kernel

/-- Every row of core MpmzmPq passes the check. -/
theorem allOKMpmzmPq : ∀ ch ∈ rowsMpmzmPq, ∀ n ∈ ch, allDMpmzmPq n = true := by
  intro ch hch n hn
  simp only [rowsMpmzmPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmzmPq0 n hn
  · exact List.all_eq_true.mp chkMpmzmPq1 n hn
  · exact List.all_eq_true.mp chkMpmzmPq2 n hn
  · exact List.all_eq_true.mp chkMpmzmPq3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpmzmPq gives Rupert**: if the numbered clauses of core MpmzmPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmzmpq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmzmPq (hU : Minimality.H24.SAT.CoreUnsat rowsMpmzmPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpmzmPq rowsMpmzmPq unitsMpmzmPq clausesPq hU allOKMpmzmPq F hchir
    (unitsMpmzmPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
