module

public import Minimality.Type24SAT.K24.DataPmpppPq
public import Minimality.Type24SAT.K24.UnitsPmpppPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class pmppp off the obtuse corner `OB1`: the kernel checks of all rows of core PmpppPq (dispatcher `rowK`, class
literals `unitsPmpppPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PmpppPq. -/
def allDPmpppPq (n : Nat) : Bool := rowKs unitsPmpppPq clausesPq chunksPmpppPq n

/-- Chunk 0 of core PmpppPq: all rows pass. -/
theorem chkPmpppPq0 : (rowsPmpppPq0.all allDPmpppPq) = true := by decide +kernel

/-- Chunk 1 of core PmpppPq: all rows pass. -/
theorem chkPmpppPq1 : (rowsPmpppPq1.all allDPmpppPq) = true := by decide +kernel

/-- Chunk 2 of core PmpppPq: all rows pass. -/
theorem chkPmpppPq2 : (rowsPmpppPq2.all allDPmpppPq) = true := by decide +kernel

/-- Chunk 3 of core PmpppPq: all rows pass. -/
theorem chkPmpppPq3 : (rowsPmpppPq3.all allDPmpppPq) = true := by decide +kernel

/-- Every row of core PmpppPq passes the check. -/
theorem allOKPmpppPq : ∀ ch ∈ rowsPmpppPq, ∀ n ∈ ch, allDPmpppPq n = true := by
  intro ch hch n hn
  simp only [rowsPmpppPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPmpppPq0 n hn
  · exact List.all_eq_true.mp chkPmpppPq1 n hn
  · exact List.all_eq_true.mp chkPmpppPq2 n hn
  · exact List.all_eq_true.mp chkPmpppPq3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PmpppPq gives Rupert**: if the numbered clauses of core PmpppPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pmppppq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePmpppPq (hU : Minimality.H24.SAT.CoreUnsat rowsPmpppPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0)
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPmpppPq rowsPmpppPq unitsPmpppPq clausesPq hU allOKPmpppPq F hchir
    (unitsPmpppPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
