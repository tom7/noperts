module

public import Minimality.Type24SAT.K24.DataPzmpp
public import Minimality.Type24SAT.K24.UnitsPzmpp

@[expose] public section

/-!
# Type 24, class pzmpp off the obtuse corner `OB1`: the kernel checks of all rows of core Pzmpp (dispatcher `rowK`, class
literals `unitsPzmpp` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core Pzmpp. -/
def allDPzmpp (n : Nat) : Bool := rowK unitsPzmpp clauseOB1 chunksPzmpp n

/-- Chunk 0 of core Pzmpp: all rows pass. -/
theorem chkPzmpp0 : (rowsPzmpp0.all allDPzmpp) = true := by decide +kernel

/-- Chunk 1 of core Pzmpp: all rows pass. -/
theorem chkPzmpp1 : (rowsPzmpp1.all allDPzmpp) = true := by decide +kernel

/-- Chunk 2 of core Pzmpp: all rows pass. -/
theorem chkPzmpp2 : (rowsPzmpp2.all allDPzmpp) = true := by decide +kernel

/-- Chunk 3 of core Pzmpp: all rows pass. -/
theorem chkPzmpp3 : (rowsPzmpp3.all allDPzmpp) = true := by decide +kernel

/-- Chunk 4 of core Pzmpp: all rows pass. -/
theorem chkPzmpp4 : (rowsPzmpp4.all allDPzmpp) = true := by decide +kernel

/-- Chunk 5 of core Pzmpp: all rows pass. -/
theorem chkPzmpp5 : (rowsPzmpp5.all allDPzmpp) = true := by decide +kernel

/-- Chunk 6 of core Pzmpp: all rows pass. -/
theorem chkPzmpp6 : (rowsPzmpp6.all allDPzmpp) = true := by decide +kernel

/-- Chunk 7 of core Pzmpp: all rows pass. -/
theorem chkPzmpp7 : (rowsPzmpp7.all allDPzmpp) = true := by decide +kernel

/-- Every row of core Pzmpp passes the check. -/
theorem allOKPzmpp : ∀ ch ∈ rowsPzmpp, ∀ n ∈ ch, allDPzmpp n = true := by
  intro ch hch n hn
  simp only [rowsPzmpp, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPzmpp0 n hn
  · exact List.all_eq_true.mp chkPzmpp1 n hn
  · exact List.all_eq_true.mp chkPzmpp2 n hn
  · exact List.all_eq_true.mp chkPzmpp3 n hn
  · exact List.all_eq_true.mp chkPzmpp4 n hn
  · exact List.all_eq_true.mp chkPzmpp5 n hn
  · exact List.all_eq_true.mp chkPzmpp6 n hn
  · exact List.all_eq_true.mp chkPzmpp7 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core Pzmpp gives Rupert**: if the numbered clauses of core Pzmpp are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pzmpp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePzmpp (hU : Minimality.H24.SAT.CoreUnsat rowsPzmpp) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) = 0)
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseK_of_unsat chunksPzmpp rowsPzmpp unitsPzmpp clauseOB1 hU allOKPzmpp F hchir
    (unitsPzmpp_true F h0 h1 h2 h3 h4) (clauseOB1_true F hO))

end Minimality.H24K.SAT
