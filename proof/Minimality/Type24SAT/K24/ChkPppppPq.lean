module

public import Minimality.Type24SAT.K24.DataPppppPq
public import Minimality.Type24SAT.K24.UnitsPppppPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class ppppp off the obtuse corner `OB1`: the kernel checks of all rows of core PppppPq (dispatcher `rowK`, class
literals `unitsPppppPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PppppPq. -/
def allDPppppPq (n : Nat) : Bool := rowKs unitsPppppPq clausesPq chunksPppppPq n

/-- Chunk 0 of core PppppPq: all rows pass. -/
theorem chkPppppPq0 : (rowsPppppPq0.all allDPppppPq) = true := by decide +kernel

/-- Chunk 1 of core PppppPq: all rows pass. -/
theorem chkPppppPq1 : (rowsPppppPq1.all allDPppppPq) = true := by decide +kernel

/-- Chunk 2 of core PppppPq: all rows pass. -/
theorem chkPppppPq2 : (rowsPppppPq2.all allDPppppPq) = true := by decide +kernel

/-- Chunk 3 of core PppppPq: all rows pass. -/
theorem chkPppppPq3 : (rowsPppppPq3.all allDPppppPq) = true := by decide +kernel

/-- Chunk 4 of core PppppPq: all rows pass. -/
theorem chkPppppPq4 : (rowsPppppPq4.all allDPppppPq) = true := by decide +kernel

/-- Every row of core PppppPq passes the check. -/
theorem allOKPppppPq : ∀ ch ∈ rowsPppppPq, ∀ n ∈ ch, allDPppppPq n = true := by
  intro ch hch n hn
  simp only [rowsPppppPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPppppPq0 n hn
  · exact List.all_eq_true.mp chkPppppPq1 n hn
  · exact List.all_eq_true.mp chkPppppPq2 n hn
  · exact List.all_eq_true.mp chkPppppPq3 n hn
  · exact List.all_eq_true.mp chkPppppPq4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PppppPq gives Rupert**: if the numbered clauses of core PppppPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppppppq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePppppPq (hU : Minimality.H24.SAT.CoreUnsat rowsPppppPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPppppPq rowsPppppPq unitsPppppPq clausesPq hU allOKPppppPq F hchir
    (unitsPppppPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
