module

public import Minimality.Type24SAT.K24.DataPpmmm
public import Minimality.Type24SAT.K24.UnitsPpmmm

@[expose] public section

/-!
# Type 24, class ppmmm off the obtuse corner `OB1`: the kernel checks of all rows of core Ppmmm (dispatcher `rowK`, class
literals `unitsPpmmm` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppmmm. -/
def allDPpmmm (n : Nat) : Bool := rowK unitsPpmmm clauseOB1 chunksPpmmm n

/-- Chunk 0 of core Ppmmm: all rows pass. -/
theorem chkPpmmm0 : (rowsPpmmm0.all allDPpmmm) = true := by decide +kernel

/-- Chunk 1 of core Ppmmm: all rows pass. -/
theorem chkPpmmm1 : (rowsPpmmm1.all allDPpmmm) = true := by decide +kernel

/-- Chunk 2 of core Ppmmm: all rows pass. -/
theorem chkPpmmm2 : (rowsPpmmm2.all allDPpmmm) = true := by decide +kernel

/-- Chunk 3 of core Ppmmm: all rows pass. -/
theorem chkPpmmm3 : (rowsPpmmm3.all allDPpmmm) = true := by decide +kernel

/-- Chunk 4 of core Ppmmm: all rows pass. -/
theorem chkPpmmm4 : (rowsPpmmm4.all allDPpmmm) = true := by decide +kernel

/-- Chunk 5 of core Ppmmm: all rows pass. -/
theorem chkPpmmm5 : (rowsPpmmm5.all allDPpmmm) = true := by decide +kernel

/-- Chunk 6 of core Ppmmm: all rows pass. -/
theorem chkPpmmm6 : (rowsPpmmm6.all allDPpmmm) = true := by decide +kernel

/-- Chunk 7 of core Ppmmm: all rows pass. -/
theorem chkPpmmm7 : (rowsPpmmm7.all allDPpmmm) = true := by decide +kernel

/-- Every row of core Ppmmm passes the check. -/
theorem allOKPpmmm : ∀ ch ∈ rowsPpmmm, ∀ n ∈ ch, allDPpmmm n = true := by
  intro ch hch n hn
  simp only [rowsPpmmm, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpmmm0 n hn
  · exact List.all_eq_true.mp chkPpmmm1 n hn
  · exact List.all_eq_true.mp chkPpmmm2 n hn
  · exact List.all_eq_true.mp chkPpmmm3 n hn
  · exact List.all_eq_true.mp chkPpmmm4 n hn
  · exact List.all_eq_true.mp chkPpmmm5 n hn
  · exact List.all_eq_true.mp chkPpmmm6 n hn
  · exact List.all_eq_true.mp chkPpmmm7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppmmm gives Rupert**: if the numbered clauses of core Ppmmm are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppmmm and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpmmm (hU : Minimality.H24.SAT.CoreUnsat rowsPpmmm) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1)) (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0) (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0) (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpmmm rowsPpmmm unitsPpmmm clauseOB1 hU allOKPpmmm F hchir
    (unitsPpmmm_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
