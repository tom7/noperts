module

public import Minimality.Type24SAT.K24.DataMpmpmNotP
public import Minimality.Type24SAT.K24.UnitsMpmpmNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpmpm off the obtuse corner `OB1`: the kernel checks of all rows of core MpmpmNotP (dispatcher `rowK`, class
literals `unitsMpmpmNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpmpmNotP. -/
def allDMpmpmNotP (n : Nat) : Bool := rowKs unitsMpmpmNotP clausesNotP chunksMpmpmNotP n

/-- Chunk 0 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP0 : (rowsMpmpmNotP0.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 1 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP1 : (rowsMpmpmNotP1.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 2 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP2 : (rowsMpmpmNotP2.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 3 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP3 : (rowsMpmpmNotP3.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 4 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP4 : (rowsMpmpmNotP4.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 5 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP5 : (rowsMpmpmNotP5.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 6 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP6 : (rowsMpmpmNotP6.all allDMpmpmNotP) = true := by decide +kernel

/-- Chunk 7 of core MpmpmNotP: all rows pass. -/
theorem chkMpmpmNotP7 : (rowsMpmpmNotP7.all allDMpmpmNotP) = true := by decide +kernel

/-- Every row of core MpmpmNotP passes the check. -/
theorem allOKMpmpmNotP : ∀ ch ∈ rowsMpmpmNotP, ∀ n ∈ ch, allDMpmpmNotP n = true := by
  intro ch hch n hn
  simp only [rowsMpmpmNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmpmNotP0 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP1 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP2 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP3 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP4 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP5 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP6 n hn
  · exact List.all_eq_true.mp chkMpmpmNotP7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpmpmNotP gives Rupert**: if the numbered clauses of core MpmpmNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmpmnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmpmNotP (hU : Minimality.H24.SAT.CoreUnsat rowsMpmpmNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpmpmNotP rowsMpmpmNotP unitsMpmpmNotP clausesNotP hU allOKMpmpmNotP F hchir
    (unitsMpmpmNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
