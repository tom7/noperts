module

public import Minimality.Type24SAT.K24.DataPmmpp
public import Minimality.Type24SAT.K24.UnitsPmmpp

@[expose] public section

/-!
# Type 24, class pmmpp off the obtuse corner `OB1`: the kernel checks of all rows of core Pmmpp (dispatcher `rowK`, class
literals `unitsPmmpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Pmmpp. -/
def allDPmmpp (n : Nat) : Bool := rowK unitsPmmpp clauseOB1 chunksPmmpp n

/-- Chunk 0 of core Pmmpp: all rows pass. -/
theorem chkPmmpp0 : (rowsPmmpp0.all allDPmmpp) = true := by decide +kernel

/-- Chunk 1 of core Pmmpp: all rows pass. -/
theorem chkPmmpp1 : (rowsPmmpp1.all allDPmmpp) = true := by decide +kernel

/-- Chunk 2 of core Pmmpp: all rows pass. -/
theorem chkPmmpp2 : (rowsPmmpp2.all allDPmmpp) = true := by decide +kernel

/-- Chunk 3 of core Pmmpp: all rows pass. -/
theorem chkPmmpp3 : (rowsPmmpp3.all allDPmmpp) = true := by decide +kernel

/-- Chunk 4 of core Pmmpp: all rows pass. -/
theorem chkPmmpp4 : (rowsPmmpp4.all allDPmmpp) = true := by decide +kernel

/-- Chunk 5 of core Pmmpp: all rows pass. -/
theorem chkPmmpp5 : (rowsPmmpp5.all allDPmmpp) = true := by decide +kernel

/-- Chunk 6 of core Pmmpp: all rows pass. -/
theorem chkPmmpp6 : (rowsPmmpp6.all allDPmmpp) = true := by decide +kernel

/-- Every row of core Pmmpp passes the check. -/
theorem allOKPmmpp : ∀ ch ∈ rowsPmmpp, ∀ n ∈ ch, allDPmmpp n = true := by
  intro ch hch n hn
  simp only [rowsPmmpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPmmpp0 n hn
  · exact List.all_eq_true.mp chkPmmpp1 n hn
  · exact List.all_eq_true.mp chkPmmpp2 n hn
  · exact List.all_eq_true.mp chkPmmpp3 n hn
  · exact List.all_eq_true.mp chkPmmpp4 n hn
  · exact List.all_eq_true.mp chkPmmpp5 n hn
  · exact List.all_eq_true.mp chkPmmpp6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Pmmpp gives Rupert**: if the numbered clauses of core Pmmpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pmmpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePmmpp (hU : Minimality.H24.SAT.CoreUnsat rowsPmmpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0)
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPmmpp rowsPmmpp unitsPmmpp clauseOB1 hU allOKPmmpp F hchir
    (unitsPmmpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
