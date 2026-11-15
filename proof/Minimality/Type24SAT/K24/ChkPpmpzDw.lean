module

public import Minimality.Type24SAT.K24.DataPpmpzDw
public import Minimality.Type24SAT.K24.UnitsPpmpzDw
public import Minimality.Type24SAT.K24.CasesWall

@[expose] public section

/-!
# Type 24, class ppmpz off the obtuse corner `OB1`: the kernel checks of all rows of core PpmpzDw (dispatcher `rowK`, class
literals `unitsPpmpzDw` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PpmpzDw. -/
def allDPpmpzDw (n : Nat) : Bool := rowKs unitsPpmpzDw clausesNotP chunksPpmpzDw n

/-- Chunk 0 of core PpmpzDw: all rows pass. -/
theorem chkPpmpzDw0 : (rowsPpmpzDw0.all allDPpmpzDw) = true := by decide +kernel

/-- Chunk 1 of core PpmpzDw: all rows pass. -/
theorem chkPpmpzDw1 : (rowsPpmpzDw1.all allDPpmpzDw) = true := by decide +kernel

/-- Chunk 2 of core PpmpzDw: all rows pass. -/
theorem chkPpmpzDw2 : (rowsPpmpzDw2.all allDPpmpzDw) = true := by decide +kernel

/-- Chunk 3 of core PpmpzDw: all rows pass. -/
theorem chkPpmpzDw3 : (rowsPpmpzDw3.all allDPpmpzDw) = true := by decide +kernel

/-- Every row of core PpmpzDw passes the check. -/
theorem allOKPpmpzDw : ∀ ch ∈ rowsPpmpzDw, ∀ n ∈ ch, allDPpmpzDw n = true := by
  intro ch hch n hn
  simp only [rowsPpmpzDw, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPpmpzDw0 n hn
  · exact List.all_eq_true.mp chkPpmpzDw1 n hn
  · exact List.all_eq_true.mp chkPpmpzDw2 n hn
  · exact List.all_eq_true.mp chkPpmpzDw3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PpmpzDw gives Rupert**: if the numbered clauses of core PpmpzDw are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class ppmpzdw and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePpmpzDw (hU : Minimality.H24.SAT.CoreUnsat rowsPpmpzDw) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    (hW : Minimality.H24K.SAT.WallHyp F) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPpmpzDw rowsPpmpzDw unitsPpmpzDw clausesNotP hU allOKPpmpzDw F hchir
    (unitsPpmpzDw_true F hW h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
