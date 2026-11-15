module

public import Minimality.Type24SAT.K24.DataMpzpp
public import Minimality.Type24SAT.K24.UnitsMpzpp

@[expose] public section

/-!
# Type 24, class mpzpp off the obtuse corner `OB1`: the kernel checks of all rows of core Mpzpp (dispatcher `rowK`, class
literals `unitsMpzpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Mpzpp. -/
def allDMpzpp (n : Nat) : Bool := rowK unitsMpzpp clauseOB1 chunksMpzpp n

/-- Chunk 0 of core Mpzpp: all rows pass. -/
theorem chkMpzpp0 : (rowsMpzpp0.all allDMpzpp) = true := by decide +kernel

/-- Chunk 1 of core Mpzpp: all rows pass. -/
theorem chkMpzpp1 : (rowsMpzpp1.all allDMpzpp) = true := by decide +kernel

/-- Chunk 2 of core Mpzpp: all rows pass. -/
theorem chkMpzpp2 : (rowsMpzpp2.all allDMpzpp) = true := by decide +kernel

/-- Chunk 3 of core Mpzpp: all rows pass. -/
theorem chkMpzpp3 : (rowsMpzpp3.all allDMpzpp) = true := by decide +kernel

/-- Chunk 4 of core Mpzpp: all rows pass. -/
theorem chkMpzpp4 : (rowsMpzpp4.all allDMpzpp) = true := by decide +kernel

/-- Chunk 5 of core Mpzpp: all rows pass. -/
theorem chkMpzpp5 : (rowsMpzpp5.all allDMpzpp) = true := by decide +kernel

/-- Every row of core Mpzpp passes the check. -/
theorem allOKMpzpp : ∀ ch ∈ rowsMpzpp, ∀ n ∈ ch, allDMpzpp n = true := by
  intro ch hch n hn
  simp only [rowsMpzpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpzpp0 n hn
  · exact List.all_eq_true.mp chkMpzpp1 n hn
  · exact List.all_eq_true.mp chkMpzpp2 n hn
  · exact List.all_eq_true.mp chkMpzpp3 n hn
  · exact List.all_eq_true.mp chkMpzpp4 n hn
  · exact List.all_eq_true.mp chkMpzpp5 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Mpzpp gives Rupert**: if the numbered clauses of core Mpzpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpzpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpzpp (hU : Minimality.H24.SAT.CoreUnsat rowsMpzpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksMpzpp rowsMpzpp unitsMpzpp clauseOB1 hU allOKMpzpp F hchir
    (unitsMpzpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
