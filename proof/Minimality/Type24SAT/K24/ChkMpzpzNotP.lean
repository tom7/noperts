module

public import Minimality.Type24SAT.K24.DataMpzpzNotP
public import Minimality.Type24SAT.K24.UnitsMpzpzNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpzpz off the obtuse corner `OB1`: the kernel checks of all rows of core MpzpzNotP (dispatcher `rowK`, class
literals `unitsMpzpzNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpzpzNotP. -/
def allDMpzpzNotP (n : Nat) : Bool := rowKs unitsMpzpzNotP clausesNotP chunksMpzpzNotP n

/-- Chunk 0 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP0 : (rowsMpzpzNotP0.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 1 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP1 : (rowsMpzpzNotP1.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 2 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP2 : (rowsMpzpzNotP2.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 3 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP3 : (rowsMpzpzNotP3.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 4 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP4 : (rowsMpzpzNotP4.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 5 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP5 : (rowsMpzpzNotP5.all allDMpzpzNotP) = true := by decide +kernel

/-- Chunk 6 of core MpzpzNotP: all rows pass. -/
theorem chkMpzpzNotP6 : (rowsMpzpzNotP6.all allDMpzpzNotP) = true := by decide +kernel

/-- Every row of core MpzpzNotP passes the check. -/
theorem allOKMpzpzNotP : ∀ ch ∈ rowsMpzpzNotP, ∀ n ∈ ch, allDMpzpzNotP n = true := by
  intro ch hch n hn
  simp only [rowsMpzpzNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpzpzNotP0 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP1 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP2 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP3 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP4 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP5 n hn
  · exact List.all_eq_true.mp chkMpzpzNotP6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpzpzNotP gives Rupert**: if the numbered clauses of core MpzpzNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpzpznotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpzpzNotP (hU : Minimality.H24.SAT.CoreUnsat rowsMpzpzNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpzpzNotP rowsMpzpzNotP unitsMpzpzNotP clausesNotP hU allOKMpzpzNotP F hchir
    (unitsMpzpzNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
