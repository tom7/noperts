module

public import Minimality.Type24SAT.K24.DataMpmzmNotP
public import Minimality.Type24SAT.K24.UnitsMpmzmNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpmzm off the obtuse corner `OB1`: the kernel checks of all rows of core MpmzmNotP (dispatcher `rowK`, class
literals `unitsMpmzmNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpmzmNotP. -/
def allDMpmzmNotP (n : Nat) : Bool := rowKs unitsMpmzmNotP clausesNotP chunksMpmzmNotP n

/-- Chunk 0 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP0 : (rowsMpmzmNotP0.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 1 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP1 : (rowsMpmzmNotP1.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 2 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP2 : (rowsMpmzmNotP2.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 3 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP3 : (rowsMpmzmNotP3.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 4 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP4 : (rowsMpmzmNotP4.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 5 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP5 : (rowsMpmzmNotP5.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 6 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP6 : (rowsMpmzmNotP6.all allDMpmzmNotP) = true := by decide +kernel

/-- Chunk 7 of core MpmzmNotP: all rows pass. -/
theorem chkMpmzmNotP7 : (rowsMpmzmNotP7.all allDMpmzmNotP) = true := by decide +kernel

/-- Every row of core MpmzmNotP passes the check. -/
theorem allOKMpmzmNotP : ∀ ch ∈ rowsMpmzmNotP, ∀ n ∈ ch, allDMpmzmNotP n = true := by
  intro ch hch n hn
  simp only [rowsMpmzmNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmzmNotP0 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP1 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP2 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP3 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP4 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP5 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP6 n hn
  · exact List.all_eq_true.mp chkMpmzmNotP7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpmzmNotP gives Rupert**: if the numbered clauses of core MpmzmNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmzmnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmzmNotP (hU : Minimality.H24.SAT.CoreUnsat rowsMpmzmNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpmzmNotP rowsMpmzmNotP unitsMpmzmNotP clausesNotP hU allOKMpmzmNotP F hchir
    (unitsMpmzmNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
