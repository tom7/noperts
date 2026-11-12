module

public import Minimality.Type24SAT.K24.DataMpmpp
public import Minimality.Type24SAT.K24.UnitsMpmpp

@[expose] public section

/-!
# Type 24, class mpmpp off the obtuse corner `OB1`: the kernel checks of all rows of core Mpmpp (dispatcher `rowK`, class
literals `unitsMpmpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Mpmpp. -/
def allDMpmpp (n : Nat) : Bool := rowK unitsMpmpp clauseOB1 chunksMpmpp n

/-- Chunk 0 of core Mpmpp: all rows pass. -/
theorem chkMpmpp0 : (rowsMpmpp0.all allDMpmpp) = true := by decide +kernel

/-- Chunk 1 of core Mpmpp: all rows pass. -/
theorem chkMpmpp1 : (rowsMpmpp1.all allDMpmpp) = true := by decide +kernel

/-- Chunk 2 of core Mpmpp: all rows pass. -/
theorem chkMpmpp2 : (rowsMpmpp2.all allDMpmpp) = true := by decide +kernel

/-- Chunk 3 of core Mpmpp: all rows pass. -/
theorem chkMpmpp3 : (rowsMpmpp3.all allDMpmpp) = true := by decide +kernel

/-- Chunk 4 of core Mpmpp: all rows pass. -/
theorem chkMpmpp4 : (rowsMpmpp4.all allDMpmpp) = true := by decide +kernel

/-- Chunk 5 of core Mpmpp: all rows pass. -/
theorem chkMpmpp5 : (rowsMpmpp5.all allDMpmpp) = true := by decide +kernel

/-- Chunk 6 of core Mpmpp: all rows pass. -/
theorem chkMpmpp6 : (rowsMpmpp6.all allDMpmpp) = true := by decide +kernel

/-- Chunk 7 of core Mpmpp: all rows pass. -/
theorem chkMpmpp7 : (rowsMpmpp7.all allDMpmpp) = true := by decide +kernel

/-- Every row of core Mpmpp passes the check. -/
theorem allOKMpmpp : ∀ ch ∈ rowsMpmpp, ∀ n ∈ ch, allDMpmpp n = true := by
  intro ch hch n hn
  simp only [rowsMpmpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmpp0 n hn
  · exact List.all_eq_true.mp chkMpmpp1 n hn
  · exact List.all_eq_true.mp chkMpmpp2 n hn
  · exact List.all_eq_true.mp chkMpmpp3 n hn
  · exact List.all_eq_true.mp chkMpmpp4 n hn
  · exact List.all_eq_true.mp chkMpmpp5 n hn
  · exact List.all_eq_true.mp chkMpmpp6 n hn
  · exact List.all_eq_true.mp chkMpmpp7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Mpmpp gives Rupert**: if the numbered clauses of core Mpmpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmpp (hU : Minimality.H24.SAT.CoreUnsat rowsMpmpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksMpmpp rowsMpmpp unitsMpmpp clauseOB1 hU allOKMpmpp F hchir
    (unitsMpmpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
