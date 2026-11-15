module

public import Minimality.Type24SAT.K24.DataZpmzm
public import Minimality.Type24SAT.K24.UnitsZpmzm

@[expose] public section

/-!
# Type 24, class zpmzm off the obtuse corner `OB1`: the kernel checks of all rows of core Zpmzm (dispatcher `rowK`, class
literals `unitsZpmzm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Zpmzm. -/
def allDZpmzm (n : Nat) : Bool := rowK unitsZpmzm clauseOB1 chunksZpmzm n

/-- Chunk 0 of core Zpmzm: all rows pass. -/
theorem chkZpmzm0 : (rowsZpmzm0.all allDZpmzm) = true := by decide +kernel

/-- Chunk 1 of core Zpmzm: all rows pass. -/
theorem chkZpmzm1 : (rowsZpmzm1.all allDZpmzm) = true := by decide +kernel

/-- Chunk 2 of core Zpmzm: all rows pass. -/
theorem chkZpmzm2 : (rowsZpmzm2.all allDZpmzm) = true := by decide +kernel

/-- Chunk 3 of core Zpmzm: all rows pass. -/
theorem chkZpmzm3 : (rowsZpmzm3.all allDZpmzm) = true := by decide +kernel

/-- Chunk 4 of core Zpmzm: all rows pass. -/
theorem chkZpmzm4 : (rowsZpmzm4.all allDZpmzm) = true := by decide +kernel

/-- Chunk 5 of core Zpmzm: all rows pass. -/
theorem chkZpmzm5 : (rowsZpmzm5.all allDZpmzm) = true := by decide +kernel

/-- Chunk 6 of core Zpmzm: all rows pass. -/
theorem chkZpmzm6 : (rowsZpmzm6.all allDZpmzm) = true := by decide +kernel

/-- Chunk 7 of core Zpmzm: all rows pass. -/
theorem chkZpmzm7 : (rowsZpmzm7.all allDZpmzm) = true := by decide +kernel

/-- Every row of core Zpmzm passes the check. -/
theorem allOKZpmzm : ∀ ch ∈ rowsZpmzm, ∀ n ∈ ch, allDZpmzm n = true := by
  intro ch hch n hn
  simp only [rowsZpmzm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpmzm0 n hn
  · exact List.all_eq_true.mp chkZpmzm1 n hn
  · exact List.all_eq_true.mp chkZpmzm2 n hn
  · exact List.all_eq_true.mp chkZpmzm3 n hn
  · exact List.all_eq_true.mp chkZpmzm4 n hn
  · exact List.all_eq_true.mp chkZpmzm5 n hn
  · exact List.all_eq_true.mp chkZpmzm6 n hn
  · exact List.all_eq_true.mp chkZpmzm7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Zpmzm gives Rupert**: if the numbered clauses of core Zpmzm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpmzm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpmzm (hU : Minimality.H24.SAT.CoreUnsat rowsZpmzm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0)
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksZpmzm rowsZpmzm unitsZpmzm clauseOB1 hU allOKZpmzm F hchir
    (unitsZpmzm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
