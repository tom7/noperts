module

public import Minimality.Type24SAT.K24.DataPpppzDw
public import Minimality.Type24SAT.K24.UnitsPpppzDw
public import Minimality.Type24SAT.K24.CasesWall

@[expose] public section

/-!
# Type 24, class ppppz off the obtuse corner `OB1`: the kernel checks of all rows of core PpppzDw (dispatcher `rowK`, class
literals `unitsPpppzDw` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PpppzDw. -/
def allDPpppzDw (n : Nat) : Bool := rowKs unitsPpppzDw clausesNotP chunksPpppzDw n

/-- Chunk 0 of core PpppzDw: all rows pass. -/
theorem chkPpppzDw0 : (rowsPpppzDw0.all allDPpppzDw) = true := by decide +kernel

/-- Chunk 1 of core PpppzDw: all rows pass. -/
theorem chkPpppzDw1 : (rowsPpppzDw1.all allDPpppzDw) = true := by decide +kernel

/-- Chunk 2 of core PpppzDw: all rows pass. -/
theorem chkPpppzDw2 : (rowsPpppzDw2.all allDPpppzDw) = true := by decide +kernel

/-- Chunk 3 of core PpppzDw: all rows pass. -/
theorem chkPpppzDw3 : (rowsPpppzDw3.all allDPpppzDw) = true := by decide +kernel

/-- Chunk 4 of core PpppzDw: all rows pass. -/
theorem chkPpppzDw4 : (rowsPpppzDw4.all allDPpppzDw) = true := by decide +kernel

/-- Every row of core PpppzDw passes the check. -/
theorem allOKPpppzDw : ∀ ch ∈ rowsPpppzDw, ∀ n ∈ ch, allDPpppzDw n = true := by
  intro ch hch n hn
  simp only [rowsPpppzDw, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpppzDw0 n hn
  · exact List.all_eq_true.mp chkPpppzDw1 n hn
  · exact List.all_eq_true.mp chkPpppzDw2 n hn
  · exact List.all_eq_true.mp chkPpppzDw3 n hn
  · exact List.all_eq_true.mp chkPpppzDw4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PpppzDw gives Rupert**: if the numbered clauses of core PpppzDw are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppppzdw and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpppzDw (hU : Minimality.H24.SAT.CoreUnsat rowsPpppzDw) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    (hW : Minimality.H24K.SAT.WallHyp F) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPpppzDw rowsPpppzDw unitsPpppzDw clausesNotP hU allOKPpppzDw F hchir
    (unitsPpppzDw_true F hW h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
