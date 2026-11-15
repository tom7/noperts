module

public import Minimality.Type24SAT.K24.DataPmzpp
public import Minimality.Type24SAT.K24.UnitsPmzpp

@[expose] public section

/-!
# Type 24, class pmzpp off the obtuse corner `OB1`: the kernel checks of all rows of core Pmzpp (dispatcher `rowK`, class
literals `unitsPmzpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Pmzpp. -/
def allDPmzpp (n : Nat) : Bool := rowK unitsPmzpp clauseOB1 chunksPmzpp n

/-- Chunk 0 of core Pmzpp: all rows pass. -/
theorem chkPmzpp0 : (rowsPmzpp0.all allDPmzpp) = true := by decide +kernel

/-- Chunk 1 of core Pmzpp: all rows pass. -/
theorem chkPmzpp1 : (rowsPmzpp1.all allDPmzpp) = true := by decide +kernel

/-- Chunk 2 of core Pmzpp: all rows pass. -/
theorem chkPmzpp2 : (rowsPmzpp2.all allDPmzpp) = true := by decide +kernel

/-- Chunk 3 of core Pmzpp: all rows pass. -/
theorem chkPmzpp3 : (rowsPmzpp3.all allDPmzpp) = true := by decide +kernel

/-- Chunk 4 of core Pmzpp: all rows pass. -/
theorem chkPmzpp4 : (rowsPmzpp4.all allDPmzpp) = true := by decide +kernel

/-- Chunk 5 of core Pmzpp: all rows pass. -/
theorem chkPmzpp5 : (rowsPmzpp5.all allDPmzpp) = true := by decide +kernel

/-- Chunk 6 of core Pmzpp: all rows pass. -/
theorem chkPmzpp6 : (rowsPmzpp6.all allDPmzpp) = true := by decide +kernel

/-- Every row of core Pmzpp passes the check. -/
theorem allOKPmzpp : ∀ ch ∈ rowsPmzpp, ∀ n ∈ ch, allDPmzpp n = true := by
  intro ch hch n hn
  simp only [rowsPmzpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPmzpp0 n hn
  · exact List.all_eq_true.mp chkPmzpp1 n hn
  · exact List.all_eq_true.mp chkPmzpp2 n hn
  · exact List.all_eq_true.mp chkPmzpp3 n hn
  · exact List.all_eq_true.mp chkPmzpp4 n hn
  · exact List.all_eq_true.mp chkPmzpp5 n hn
  · exact List.all_eq_true.mp chkPmzpp6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Pmzpp gives Rupert**: if the numbered clauses of core Pmzpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pmzpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePmzpp (hU : Minimality.H24.SAT.CoreUnsat rowsPmzpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0)
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPmzpp rowsPmzpp unitsPmzpp clauseOB1 hU allOKPmzpp F hchir
    (unitsPmzpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
