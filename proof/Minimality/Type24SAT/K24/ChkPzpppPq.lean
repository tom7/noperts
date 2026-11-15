module

public import Minimality.Type24SAT.K24.DataPzpppPq
public import Minimality.Type24SAT.K24.UnitsPzpppPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class pzppp off the obtuse corner `OB1`: the kernel checks of all rows of core PzpppPq (dispatcher `rowK`, class
literals `unitsPzpppPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PzpppPq. -/
def allDPzpppPq (n : Nat) : Bool := rowKs unitsPzpppPq clausesPq chunksPzpppPq n

/-- Chunk 0 of core PzpppPq: all rows pass. -/
theorem chkPzpppPq0 : (rowsPzpppPq0.all allDPzpppPq) = true := by decide +kernel

/-- Chunk 1 of core PzpppPq: all rows pass. -/
theorem chkPzpppPq1 : (rowsPzpppPq1.all allDPzpppPq) = true := by decide +kernel

/-- Chunk 2 of core PzpppPq: all rows pass. -/
theorem chkPzpppPq2 : (rowsPzpppPq2.all allDPzpppPq) = true := by decide +kernel

/-- Chunk 3 of core PzpppPq: all rows pass. -/
theorem chkPzpppPq3 : (rowsPzpppPq3.all allDPzpppPq) = true := by decide +kernel

/-- Every row of core PzpppPq passes the check. -/
theorem allOKPzpppPq : ∀ ch ∈ rowsPzpppPq, ∀ n ∈ ch, allDPzpppPq n = true := by
  intro ch hch n hn
  simp only [rowsPzpppPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPzpppPq0 n hn
  · exact List.all_eq_true.mp chkPzpppPq1 n hn
  · exact List.all_eq_true.mp chkPzpppPq2 n hn
  · exact List.all_eq_true.mp chkPzpppPq3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PzpppPq gives Rupert**: if the numbered clauses of core PzpppPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pzppppq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePzpppPq (hU : Minimality.H24.SAT.CoreUnsat rowsPzpppPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) = 0)
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPzpppPq rowsPzpppPq unitsPzpppPq clausesPq hU allOKPzpppPq F hchir
    (unitsPzpppPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
