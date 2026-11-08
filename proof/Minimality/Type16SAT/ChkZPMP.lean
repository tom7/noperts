module

public import Minimality.Type16SAT.DataZPMP
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W

@[expose] public section

/-!
# Type 16, J7: core ZPMP, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsZPMP`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core ZPMP. -/
def allDZPMP (n : Nat) : Bool := rowS unitsZPMP chunksZPMP n

/-- Chunk 0 of core ZPMP: all rows pass. -/
theorem chkZPMP0 : (rowsZPMP0.all allDZPMP) = true := by decide +kernel

/-- Chunk 1 of core ZPMP: all rows pass. -/
theorem chkZPMP1 : (rowsZPMP1.all allDZPMP) = true := by decide +kernel

/-- Chunk 2 of core ZPMP: all rows pass. -/
theorem chkZPMP2 : (rowsZPMP2.all allDZPMP) = true := by decide +kernel

/-- Chunk 3 of core ZPMP: all rows pass. -/
theorem chkZPMP3 : (rowsZPMP3.all allDZPMP) = true := by decide +kernel

/-- Chunk 4 of core ZPMP: all rows pass. -/
theorem chkZPMP4 : (rowsZPMP4.all allDZPMP) = true := by decide +kernel

/-- Chunk 5 of core ZPMP: all rows pass. -/
theorem chkZPMP5 : (rowsZPMP5.all allDZPMP) = true := by decide +kernel

/-- Chunk 6 of core ZPMP: all rows pass. -/
theorem chkZPMP6 : (rowsZPMP6.all allDZPMP) = true := by decide +kernel

/-- Chunk 7 of core ZPMP: all rows pass. -/
theorem chkZPMP7 : (rowsZPMP7.all allDZPMP) = true := by decide +kernel

/-- Chunk 8 of core ZPMP: all rows pass. -/
theorem chkZPMP8 : (rowsZPMP8.all allDZPMP) = true := by decide +kernel

/-- Chunk 9 of core ZPMP: all rows pass. -/
theorem chkZPMP9 : (rowsZPMP9.all allDZPMP) = true := by decide +kernel

/-- Chunk 10 of core ZPMP: all rows pass. -/
theorem chkZPMP10 : (rowsZPMP10.all allDZPMP) = true := by decide +kernel

/-- Chunk 11 of core ZPMP: all rows pass. -/
theorem chkZPMP11 : (rowsZPMP11.all allDZPMP) = true := by decide +kernel

/-- Every row of core ZPMP passes the check. -/
theorem allOKZPMP : ∀ ch ∈ rowsZPMP, ∀ n ∈ ch, allDZPMP n = true := by
  intro ch hch n hn
  simp only [rowsZPMP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZPMP0 n hn
  · exact List.all_eq_true.mp chkZPMP1 n hn
  · exact List.all_eq_true.mp chkZPMP2 n hn
  · exact List.all_eq_true.mp chkZPMP3 n hn
  · exact List.all_eq_true.mp chkZPMP4 n hn
  · exact List.all_eq_true.mp chkZPMP5 n hn
  · exact List.all_eq_true.mp chkZPMP6 n hn
  · exact List.all_eq_true.mp chkZPMP7 n hn
  · exact List.all_eq_true.mp chkZPMP8 n hn
  · exact List.all_eq_true.mp chkZPMP9 n hn
  · exact List.all_eq_true.mp chkZPMP10 n hn
  · exact List.all_eq_true.mp chkZPMP11 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core ZPMP are true when the four class brackets have the signs `0+-+`. -/
theorem unitsZPMP_true (F : S0xFac 8 V2.fIdx x) (h0 : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = 0) (h1 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsZPMP, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsZPMP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 2 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core ZPMP gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataZPMP (hU : CoreUnsat rowsZPMP) : Core16W 0 1 (-1) 1 := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksZPMP rowsZPMP unitsZPMP hU allOKZPMP F hC
    (unitsZPMP_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
