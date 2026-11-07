module

public import Minimality.Type29TSAT.DataV0
public import Minimality.Type29SAT.Top

@[expose] public section

/-!
# Type 29, core V0: the kernel checks of all rows and the theorem `rupert_of_coreV0`

Core V0 is the case `[0245] = 0` (`V = 0`).  Its only class literal is the zero unit: the gate `V.gate false p false q` with
`p = [0245] > 0` and `q = [0245] < 0`, true exactly when the bracket vanishes.  Every row of `rowsV0` passes the row check
(families 8, 11 to 16, 20, 21), the rule check (17), the witness check (19), the `T(L,L)` check (22), the quad relation
check (23) and the unit check (26).  Together with the unsatisfiability of the numbered clauses (`CoreUnsat rowsV0`), every
shape of the class is Rupert.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The class literal of core V0: the bracket `[0245]` is zero. -/
def unitsV0 : List Lit := [(true, V.gate false (V.br 0 2 4 5) false (V.ng (V.br 0 2 4 5)))]

/-- All six row checks. -/
def allDV0 (n : Nat) : Bool :=
  rowD chunksV0 n && ruleD chunksV0 n && witD chunksV0 n && tllD chunksV0 n && unitD unitsV0 chunksV0 n && krelD chunksV0 n

/-- Chunk 0 of core V0: all six row checks pass. -/
theorem chkV00 : (rowsV00.all allDV0) = true := by decide +kernel

/-- Chunk 1 of core V0: all six row checks pass. -/
theorem chkV01 : (rowsV01.all allDV0) = true := by decide +kernel

/-- Chunk 2 of core V0: all six row checks pass. -/
theorem chkV02 : (rowsV02.all allDV0) = true := by decide +kernel

/-- Chunk 3 of core V0: all six row checks pass. -/
theorem chkV03 : (rowsV03.all allDV0) = true := by decide +kernel

/-- Chunk 4 of core V0: all six row checks pass. -/
theorem chkV04 : (rowsV04.all allDV0) = true := by decide +kernel

/-- Chunk 5 of core V0: all six row checks pass. -/
theorem chkV05 : (rowsV05.all allDV0) = true := by decide +kernel

/-- Chunk 6 of core V0: all six row checks pass. -/
theorem chkV06 : (rowsV06.all allDV0) = true := by decide +kernel

/-- Chunk 7 of core V0: all six row checks pass. -/
theorem chkV07 : (rowsV07.all allDV0) = true := by decide +kernel

/-- Chunk 8 of core V0: all six row checks pass. -/
theorem chkV08 : (rowsV08.all allDV0) = true := by decide +kernel

/-- Chunk 9 of core V0: all six row checks pass. -/
theorem chkV09 : (rowsV09.all allDV0) = true := by decide +kernel

/-- Every row of core V0 passes all six checks. -/
theorem allOKV0 : ∀ ch ∈ rowsV0, ∀ n ∈ ch, allDV0 n = true := by
  intro ch hch n hn
  simp only [rowsV0, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkV00 n hn
  · exact List.all_eq_true.mp chkV01 n hn
  · exact List.all_eq_true.mp chkV02 n hn
  · exact List.all_eq_true.mp chkV03 n hn
  · exact List.all_eq_true.mp chkV04 n hn
  · exact List.all_eq_true.mp chkV05 n hn
  · exact List.all_eq_true.mp chkV06 n hn
  · exact List.all_eq_true.mp chkV07 n hn
  · exact List.all_eq_true.mp chkV08 n hn
  · exact List.all_eq_true.mp chkV09 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literal of core V0 is true of the real data when the bracket `[0245]` vanishes. -/
theorem unitsV0_true (F : S0xFac 9 s0x_S29 x) (h0 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) = 0) :
    ∀ l ∈ unitsV0, evalL (rho (geoF F)) l = true := by
  intro l hl
  have e : ∀ i < 7, (geoF F).x i = x (Fin.ofNat 7 i) := fun i _ => rfl
  simp only [unitsV0, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl
  simp [evalL, rho, Geo.atom, e, h0]

/-- **Core V0 gives Rupert**: if the numbered clauses of core V0 are unsatisfiable, every type 29 shape with
`0 < [0123]` and `[0245] = 0` is Rupert. -/
theorem rupert_of_coreV0 (hU : CoreUnsat rowsV0) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) = 0) :
    IsRupert (univ.image x) := by
  refine case_of_unsat chunksV0 rowsV0 unitsV0 hU ?_ F hchir (unitsV0_true F h0)
  intro ch hch n hn
  have := allOKV0 ch hch n hn
  simp only [allDV0, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Minimality.H29.SAT
