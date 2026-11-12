module

public import Minimality.Type24SAT.K24.DataPpmpp
public import Minimality.Type24SAT.K24.UnitsPpmpp

@[expose] public section

/-!
# Type 24, class ppmpp off the obtuse corner `OB1`: the kernel checks of all rows of core Ppmpp (dispatcher `rowK`, class
literals `unitsPpmpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Ppmpp. -/
def allDPpmpp (n : Nat) : Bool := rowK unitsPpmpp clauseOB1 chunksPpmpp n

/-- Chunk 0 of core Ppmpp: all rows pass. -/
theorem chkPpmpp0 : (rowsPpmpp0.all allDPpmpp) = true := by decide +kernel

/-- Chunk 1 of core Ppmpp: all rows pass. -/
theorem chkPpmpp1 : (rowsPpmpp1.all allDPpmpp) = true := by decide +kernel

/-- Chunk 2 of core Ppmpp: all rows pass. -/
theorem chkPpmpp2 : (rowsPpmpp2.all allDPpmpp) = true := by decide +kernel

/-- Chunk 3 of core Ppmpp: all rows pass. -/
theorem chkPpmpp3 : (rowsPpmpp3.all allDPpmpp) = true := by decide +kernel

/-- Chunk 4 of core Ppmpp: all rows pass. -/
theorem chkPpmpp4 : (rowsPpmpp4.all allDPpmpp) = true := by decide +kernel

/-- Chunk 5 of core Ppmpp: all rows pass. -/
theorem chkPpmpp5 : (rowsPpmpp5.all allDPpmpp) = true := by decide +kernel

/-- Chunk 6 of core Ppmpp: all rows pass. -/
theorem chkPpmpp6 : (rowsPpmpp6.all allDPpmpp) = true := by decide +kernel

/-- Chunk 7 of core Ppmpp: all rows pass. -/
theorem chkPpmpp7 : (rowsPpmpp7.all allDPpmpp) = true := by decide +kernel

/-- Every row of core Ppmpp passes the check. -/
theorem allOKPpmpp : ∀ ch ∈ rowsPpmpp, ∀ n ∈ ch, allDPpmpp n = true := by
  intro ch hch n hn
  simp only [rowsPpmpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpmpp0 n hn
  · exact List.all_eq_true.mp chkPpmpp1 n hn
  · exact List.all_eq_true.mp chkPpmpp2 n hn
  · exact List.all_eq_true.mp chkPpmpp3 n hn
  · exact List.all_eq_true.mp chkPpmpp4 n hn
  · exact List.all_eq_true.mp chkPpmpp5 n hn
  · exact List.all_eq_true.mp chkPpmpp6 n hn
  · exact List.all_eq_true.mp chkPpmpp7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Ppmpp gives Rupert**: if the numbered clauses of core Ppmpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppmpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpmpp (hU : Minimality.H24.SAT.CoreUnsat rowsPpmpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPpmpp rowsPpmpp unitsPpmpp clauseOB1 hU allOKPpmpp F hchir
    (unitsPpmpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
