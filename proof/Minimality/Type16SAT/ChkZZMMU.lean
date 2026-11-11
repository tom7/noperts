module

public import Minimality.Type16SAT.DataZZMMU
public import Minimality.Type16SAT.KDecK16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.Cls16C

@[expose] public section

/-!
# Type 16, J7: core ZZMMU, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsZZMMU`, class clause `clauseZZMMU`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core ZZMMU. -/
def allDZZMMU (n : Nat) : Bool := rowSK unitsZZMMU clauseZZMMU chunksZZMMU n

/-- Chunk 0 of core ZZMMU: all rows pass. -/
theorem chkZZMMU0 : (rowsZZMMU0.all allDZZMMU) = true := by decide +kernel

/-- Chunk 1 of core ZZMMU: all rows pass. -/
theorem chkZZMMU1 : (rowsZZMMU1.all allDZZMMU) = true := by decide +kernel

/-- Chunk 2 of core ZZMMU: all rows pass. -/
theorem chkZZMMU2 : (rowsZZMMU2.all allDZZMMU) = true := by decide +kernel

/-- Chunk 3 of core ZZMMU: all rows pass. -/
theorem chkZZMMU3 : (rowsZZMMU3.all allDZZMMU) = true := by decide +kernel

/-- Chunk 4 of core ZZMMU: all rows pass. -/
theorem chkZZMMU4 : (rowsZZMMU4.all allDZZMMU) = true := by decide +kernel

/-- Chunk 5 of core ZZMMU: all rows pass. -/
theorem chkZZMMU5 : (rowsZZMMU5.all allDZZMMU) = true := by decide +kernel

/-- Chunk 6 of core ZZMMU: all rows pass. -/
theorem chkZZMMU6 : (rowsZZMMU6.all allDZZMMU) = true := by decide +kernel

/-- Chunk 7 of core ZZMMU: all rows pass. -/
theorem chkZZMMU7 : (rowsZZMMU7.all allDZZMMU) = true := by decide +kernel

/-- Chunk 8 of core ZZMMU: all rows pass. -/
theorem chkZZMMU8 : (rowsZZMMU8.all allDZZMMU) = true := by decide +kernel

/-- Chunk 9 of core ZZMMU: all rows pass. -/
theorem chkZZMMU9 : (rowsZZMMU9.all allDZZMMU) = true := by decide +kernel

/-- Chunk 10 of core ZZMMU: all rows pass. -/
theorem chkZZMMU10 : (rowsZZMMU10.all allDZZMMU) = true := by decide +kernel

/-- Chunk 11 of core ZZMMU: all rows pass. -/
theorem chkZZMMU11 : (rowsZZMMU11.all allDZZMMU) = true := by decide +kernel

/-- Chunk 12 of core ZZMMU: all rows pass. -/
theorem chkZZMMU12 : (rowsZZMMU12.all allDZZMMU) = true := by decide +kernel

/-- Every row of core ZZMMU passes the check. -/
theorem allOKZZMMU : ∀ ch ∈ rowsZZMMU, ∀ n ∈ ch, allDZZMMU n = true := by
  intro ch hch n hn
  simp only [rowsZZMMU, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZZMMU0 n hn
  · exact List.all_eq_true.mp chkZZMMU1 n hn
  · exact List.all_eq_true.mp chkZZMMU2 n hn
  · exact List.all_eq_true.mp chkZZMMU3 n hn
  · exact List.all_eq_true.mp chkZZMMU4 n hn
  · exact List.all_eq_true.mp chkZZMMU5 n hn
  · exact List.all_eq_true.mp chkZZMMU6 n hn
  · exact List.all_eq_true.mp chkZZMMU7 n hn
  · exact List.all_eq_true.mp chkZZMMU8 n hn
  · exact List.all_eq_true.mp chkZZMMU9 n hn
  · exact List.all_eq_true.mp chkZZMMU10 n hn
  · exact List.all_eq_true.mp chkZZMMU11 n hn
  · exact List.all_eq_true.mp chkZZMMU12 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core ZZMMU are true when the four class brackets have the signs `00--`. -/
theorem unitsZZMMU_true (F : S0xFac 8 V2.fIdx x) (h0 : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = 0) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsZZMMU, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsZZMMU, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 2 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]


/-- The case clause of core ZZMMU holds when `CaseT16 x` (`x 1 - x 6` is not orthogonal to both `x 0 - x 3` and `x 0 - x 6`). -/
theorem clauseZZMMU_true (F : S0xFac 8 V2.fIdx x) (h : CaseT16 x) : HoldsW (rhoW (geoF F)) clauseZZMMU := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v2 : (geoF F).vv 2 = x 0 - x 3 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e3]
  have v5 : (geoF F).vv 5 = x 0 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e6]
  have v10 : (geoF F).vv 10 = x 1 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e1, e6]
  rcases h with h | h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 2 10)), by simp [clauseZZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
    · refine ⟨(true, W.base (V.tp 2 10)), by simp [clauseZZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 5 10)), by simp [clauseZZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h
    · refine ⟨(true, W.base (V.tp 5 10)), by simp [clauseZZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h

/-- **Core ZZMMU gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16TW`. -/
theorem rupert_of_core_dataZZMMU (hU : CoreUnsat rowsZZMMU) : Core16TW 0 0 (-1) (-1) := by
  intro y F hC h1 h2 h3 h4 hA
  exact caseSK_of_unsat chunksZZMMU rowsZZMMU unitsZZMMU clauseZZMMU hU allOKZZMMU F hC
    (unitsZZMMU_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)) (clauseZZMMU_true F hA)

end Minimality.H16K.SAT
