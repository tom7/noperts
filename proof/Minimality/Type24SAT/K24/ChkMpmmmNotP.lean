module

public import Minimality.Type24SAT.K24.DataMpmmmNotP
public import Minimality.Type24SAT.K24.UnitsMpmmmNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpmmm off the obtuse corner `OB1`: the kernel checks of all rows of core MpmmmNotP (dispatcher `rowK`, class
literals `unitsMpmmmNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpmmmNotP. -/
def allDMpmmmNotP (n : Nat) : Bool := rowKs unitsMpmmmNotP clausesNotP chunksMpmmmNotP n

/-- Chunk 0 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP0 : (rowsMpmmmNotP0.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 1 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP1 : (rowsMpmmmNotP1.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 2 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP2 : (rowsMpmmmNotP2.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 3 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP3 : (rowsMpmmmNotP3.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 4 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP4 : (rowsMpmmmNotP4.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 5 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP5 : (rowsMpmmmNotP5.all allDMpmmmNotP) = true := by decide +kernel

/-- Chunk 6 of core MpmmmNotP: all rows pass. -/
theorem chkMpmmmNotP6 : (rowsMpmmmNotP6.all allDMpmmmNotP) = true := by decide +kernel

/-- Every row of core MpmmmNotP passes the check. -/
theorem allOKMpmmmNotP : ∀ ch ∈ rowsMpmmmNotP, ∀ n ∈ ch, allDMpmmmNotP n = true := by
  intro ch hch n hn
  simp only [rowsMpmmmNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmmmNotP0 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP1 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP2 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP3 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP4 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP5 n hn
  · exact List.all_eq_true.mp chkMpmmmNotP6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpmmmNotP gives Rupert**: if the numbered clauses of core MpmmmNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmmmnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmmmNotP (hU : Minimality.H24.SAT.CoreUnsat rowsMpmmmNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpmmmNotP rowsMpmmmNotP unitsMpmmmNotP clausesNotP hU allOKMpmmmNotP F hchir
    (unitsMpmmmNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
