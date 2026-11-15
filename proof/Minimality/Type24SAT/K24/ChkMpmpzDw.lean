module

public import Minimality.Type24SAT.K24.DataMpmpzDw
public import Minimality.Type24SAT.K24.UnitsMpmpzDw
public import Minimality.Type24SAT.K24.CasesWall

@[expose] public section

/-!
# Type 24, class mpmpz off the obtuse corner `OB1`: the kernel checks of all rows of core MpmpzDw (dispatcher `rowK`, class
literals `unitsMpmpzDw` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core MpmpzDw. -/
def allDMpmpzDw (n : Nat) : Bool := rowKs unitsMpmpzDw clausesNotP chunksMpmpzDw n

/-- Chunk 0 of core MpmpzDw: all rows pass. -/
theorem chkMpmpzDw0 : (rowsMpmpzDw0.all allDMpmpzDw) = true := by decide +kernel

/-- Chunk 1 of core MpmpzDw: all rows pass. -/
theorem chkMpmpzDw1 : (rowsMpmpzDw1.all allDMpmpzDw) = true := by decide +kernel

/-- Chunk 2 of core MpmpzDw: all rows pass. -/
theorem chkMpmpzDw2 : (rowsMpmpzDw2.all allDMpmpzDw) = true := by decide +kernel

/-- Chunk 3 of core MpmpzDw: all rows pass. -/
theorem chkMpmpzDw3 : (rowsMpmpzDw3.all allDMpmpzDw) = true := by decide +kernel

/-- Every row of core MpmpzDw passes the check. -/
theorem allOKMpmpzDw : ∀ ch ∈ rowsMpmpzDw, ∀ n ∈ ch, allDMpmpzDw n = true := by
  intro ch hch n hn
  simp only [rowsMpmpzDw, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMpmpzDw0 n hn
  · exact List.all_eq_true.mp chkMpmpzDw1 n hn
  · exact List.all_eq_true.mp chkMpmpzDw2 n hn
  · exact List.all_eq_true.mp chkMpmpzDw3 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core MpmpzDw gives Rupert**: if the numbered clauses of core MpmpzDw are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class mpmpzdw and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_coreMpmpzDw (hU : Minimality.H24.SAT.CoreUnsat rowsMpmpzDw) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = 0)
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0))
    (hW : Minimality.H24K.SAT.WallHyp F) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksMpmpzDw rowsMpmpzDw unitsMpmpzDw clausesNotP hU allOKMpmpzDw F hchir
    (unitsMpmpzDw_true F hW h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
