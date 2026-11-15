module

public import Minimality.Type24SAT.K24.DataPzzpp
public import Minimality.Type24SAT.K24.UnitsPzzpp

@[expose] public section

/-!
# Type 24, class pzzpp off the obtuse corner `OB1`: the kernel checks of all rows of core Pzzpp (dispatcher `rowK`, class
literals `unitsPzzpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Pzzpp. -/
def allDPzzpp (n : Nat) : Bool := rowK unitsPzzpp clauseOB1 chunksPzzpp n

/-- Chunk 0 of core Pzzpp: all rows pass. -/
theorem chkPzzpp0 : (rowsPzzpp0.all allDPzzpp) = true := by decide +kernel

/-- Chunk 1 of core Pzzpp: all rows pass. -/
theorem chkPzzpp1 : (rowsPzzpp1.all allDPzzpp) = true := by decide +kernel

/-- Chunk 2 of core Pzzpp: all rows pass. -/
theorem chkPzzpp2 : (rowsPzzpp2.all allDPzzpp) = true := by decide +kernel

/-- Chunk 3 of core Pzzpp: all rows pass. -/
theorem chkPzzpp3 : (rowsPzzpp3.all allDPzzpp) = true := by decide +kernel

/-- Chunk 4 of core Pzzpp: all rows pass. -/
theorem chkPzzpp4 : (rowsPzzpp4.all allDPzzpp) = true := by decide +kernel

/-- Chunk 5 of core Pzzpp: all rows pass. -/
theorem chkPzzpp5 : (rowsPzzpp5.all allDPzzpp) = true := by decide +kernel

/-- Chunk 6 of core Pzzpp: all rows pass. -/
theorem chkPzzpp6 : (rowsPzzpp6.all allDPzzpp) = true := by decide +kernel

/-- Chunk 7 of core Pzzpp: all rows pass. -/
theorem chkPzzpp7 : (rowsPzzpp7.all allDPzzpp) = true := by decide +kernel

/-- Chunk 8 of core Pzzpp: all rows pass. -/
theorem chkPzzpp8 : (rowsPzzpp8.all allDPzzpp) = true := by decide +kernel

/-- Every row of core Pzzpp passes the check. -/
theorem allOKPzzpp : ∀ ch ∈ rowsPzzpp, ∀ n ∈ ch, allDPzzpp n = true := by
  intro ch hch n hn
  simp only [rowsPzzpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPzzpp0 n hn
  · exact List.all_eq_true.mp chkPzzpp1 n hn
  · exact List.all_eq_true.mp chkPzzpp2 n hn
  · exact List.all_eq_true.mp chkPzzpp3 n hn
  · exact List.all_eq_true.mp chkPzzpp4 n hn
  · exact List.all_eq_true.mp chkPzzpp5 n hn
  · exact List.all_eq_true.mp chkPzzpp6 n hn
  · exact List.all_eq_true.mp chkPzzpp7 n hn
  · exact List.all_eq_true.mp chkPzzpp8 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Pzzpp gives Rupert**: if the numbered clauses of core Pzzpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pzzpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePzzpp (hU : Minimality.H24.SAT.CoreUnsat rowsPzzpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) = 0)
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPzzpp rowsPzzpp unitsPzzpp clauseOB1 hU allOKPzzpp F hchir
    (unitsPzzpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
