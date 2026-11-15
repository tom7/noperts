module

public import Minimality.Type24SAT.K24.DataMpzpzPq
public import Minimality.Type24SAT.K24.UnitsMpzpzPq
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpzpz off the obtuse corner `OB1`: the kernel checks of all rows of core MpzpzPq (dispatcher `rowK`, class
literals `unitsMpzpzPq` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpzpzPq. -/
def allDMpzpzPq (n : Nat) : Bool := rowKs unitsMpzpzPq clausesPq chunksMpzpzPq n

/-- Chunk 0 of core MpzpzPq: all rows pass. -/
theorem chkMpzpzPq0 : (rowsMpzpzPq0.all allDMpzpzPq) = true := by decide +kernel

/-- Chunk 1 of core MpzpzPq: all rows pass. -/
theorem chkMpzpzPq1 : (rowsMpzpzPq1.all allDMpzpzPq) = true := by decide +kernel

/-- Chunk 2 of core MpzpzPq: all rows pass. -/
theorem chkMpzpzPq2 : (rowsMpzpzPq2.all allDMpzpzPq) = true := by decide +kernel

/-- Chunk 3 of core MpzpzPq: all rows pass. -/
theorem chkMpzpzPq3 : (rowsMpzpzPq3.all allDMpzpzPq) = true := by decide +kernel

/-- Chunk 4 of core MpzpzPq: all rows pass. -/
theorem chkMpzpzPq4 : (rowsMpzpzPq4.all allDMpzpzPq) = true := by decide +kernel

/-- Every row of core MpzpzPq passes the check. -/
theorem allOKMpzpzPq : ∀ ch ∈ rowsMpzpzPq, ∀ n ∈ ch, allDMpzpzPq n = true := by
  intro ch hch n hn
  simp only [rowsMpzpzPq, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpzpzPq0 n hn
  · exact List.all_eq_true.mp chkMpzpzPq1 n hn
  · exact List.all_eq_true.mp chkMpzpzPq2 n hn
  · exact List.all_eq_true.mp chkMpzpzPq3 n hn
  · exact List.all_eq_true.mp chkMpzpzPq4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpzpzPq gives Rupert**: if the numbered clauses of core MpzpzPq are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpzpzpq and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpzpzPq (hU : Minimality.H24.SAT.CoreUnsat rowsMpzpzPq) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpzpzPq rowsMpzpzPq unitsMpzpzPq clausesPq hU allOKMpzpzPq F hchir
    (unitsMpzpzPq_true F hD h0 h1 h2 h3 h4) (clausesPq_true F hO hEG hCI))

end Minimality.H24K.SAT
