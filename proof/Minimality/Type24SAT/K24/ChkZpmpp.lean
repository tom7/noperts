module

public import Minimality.Type24SAT.K24.DataZpmpp
public import Minimality.Type24SAT.K24.UnitsZpmpp

@[expose] public section

/-!
# Type 24, class zpmpp off the obtuse corner `OB1`: the kernel checks of all rows of core Zpmpp (dispatcher `rowK`, class
literals `unitsZpmpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Zpmpp. -/
def allDZpmpp (n : Nat) : Bool := rowK unitsZpmpp clauseOB1 chunksZpmpp n

/-- Chunk 0 of core Zpmpp: all rows pass. -/
theorem chkZpmpp0 : (rowsZpmpp0.all allDZpmpp) = true := by decide +kernel

/-- Chunk 1 of core Zpmpp: all rows pass. -/
theorem chkZpmpp1 : (rowsZpmpp1.all allDZpmpp) = true := by decide +kernel

/-- Chunk 2 of core Zpmpp: all rows pass. -/
theorem chkZpmpp2 : (rowsZpmpp2.all allDZpmpp) = true := by decide +kernel

/-- Chunk 3 of core Zpmpp: all rows pass. -/
theorem chkZpmpp3 : (rowsZpmpp3.all allDZpmpp) = true := by decide +kernel

/-- Chunk 4 of core Zpmpp: all rows pass. -/
theorem chkZpmpp4 : (rowsZpmpp4.all allDZpmpp) = true := by decide +kernel

/-- Chunk 5 of core Zpmpp: all rows pass. -/
theorem chkZpmpp5 : (rowsZpmpp5.all allDZpmpp) = true := by decide +kernel

/-- Chunk 6 of core Zpmpp: all rows pass. -/
theorem chkZpmpp6 : (rowsZpmpp6.all allDZpmpp) = true := by decide +kernel

/-- Chunk 7 of core Zpmpp: all rows pass. -/
theorem chkZpmpp7 : (rowsZpmpp7.all allDZpmpp) = true := by decide +kernel

/-- Every row of core Zpmpp passes the check. -/
theorem allOKZpmpp : ∀ ch ∈ rowsZpmpp, ∀ n ∈ ch, allDZpmpp n = true := by
  intro ch hch n hn
  simp only [rowsZpmpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZpmpp0 n hn
  · exact List.all_eq_true.mp chkZpmpp1 n hn
  · exact List.all_eq_true.mp chkZpmpp2 n hn
  · exact List.all_eq_true.mp chkZpmpp3 n hn
  · exact List.all_eq_true.mp chkZpmpp4 n hn
  · exact List.all_eq_true.mp chkZpmpp5 n hn
  · exact List.all_eq_true.mp chkZpmpp6 n hn
  · exact List.all_eq_true.mp chkZpmpp7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Zpmpp gives Rupert**: if the numbered clauses of core Zpmpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class zpmpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreZpmpp (hU : Minimality.H24.SAT.CoreUnsat rowsZpmpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksZpmpp rowsZpmpp unitsZpmpp clauseOB1 hU allOKZpmpp F hchir
    (unitsZpmpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
