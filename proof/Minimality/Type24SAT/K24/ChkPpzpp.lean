module

public import Minimality.Type24SAT.K24.DataPpzpp
public import Minimality.Type24SAT.K24.UnitsPpzpp

@[expose] public section

/-!
# Type 24, class ppzpp off the obtuse corner `OB1`: the kernel checks of all rows of core Ppzpp (dispatcher `rowK`, class
literals `unitsPpzpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppzpp. -/
def allDPpzpp (n : Nat) : Bool := rowK unitsPpzpp clauseOB1 chunksPpzpp n

/-- Chunk 0 of core Ppzpp: all rows pass. -/
theorem chkPpzpp0 : (rowsPpzpp0.all allDPpzpp) = true := by decide +kernel

/-- Chunk 1 of core Ppzpp: all rows pass. -/
theorem chkPpzpp1 : (rowsPpzpp1.all allDPpzpp) = true := by decide +kernel

/-- Chunk 2 of core Ppzpp: all rows pass. -/
theorem chkPpzpp2 : (rowsPpzpp2.all allDPpzpp) = true := by decide +kernel

/-- Chunk 3 of core Ppzpp: all rows pass. -/
theorem chkPpzpp3 : (rowsPpzpp3.all allDPpzpp) = true := by decide +kernel

/-- Chunk 4 of core Ppzpp: all rows pass. -/
theorem chkPpzpp4 : (rowsPpzpp4.all allDPpzpp) = true := by decide +kernel

/-- Chunk 5 of core Ppzpp: all rows pass. -/
theorem chkPpzpp5 : (rowsPpzpp5.all allDPpzpp) = true := by decide +kernel

/-- Chunk 6 of core Ppzpp: all rows pass. -/
theorem chkPpzpp6 : (rowsPpzpp6.all allDPpzpp) = true := by decide +kernel

/-- Chunk 7 of core Ppzpp: all rows pass. -/
theorem chkPpzpp7 : (rowsPpzpp7.all allDPpzpp) = true := by decide +kernel

/-- Every row of core Ppzpp passes the check. -/
theorem allOKPpzpp : ∀ ch ∈ rowsPpzpp, ∀ n ∈ ch, allDPpzpp n = true := by
  intro ch hch n hn
  simp only [rowsPpzpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpzpp0 n hn
  · exact List.all_eq_true.mp chkPpzpp1 n hn
  · exact List.all_eq_true.mp chkPpzpp2 n hn
  · exact List.all_eq_true.mp chkPpzpp3 n hn
  · exact List.all_eq_true.mp chkPpzpp4 n hn
  · exact List.all_eq_true.mp chkPpzpp5 n hn
  · exact List.all_eq_true.mp chkPpzpp6 n hn
  · exact List.all_eq_true.mp chkPpzpp7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppzpp gives Rupert**: if the numbered clauses of core Ppzpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppzpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpzpp (hU : Minimality.H24.SAT.CoreUnsat rowsPpzpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpzpp rowsPpzpp unitsPpzpp clauseOB1 hU allOKPpzpp F hchir
    (unitsPpzpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
