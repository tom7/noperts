module

public import Minimality.Type16SAT.DataMZMMU
public import Minimality.Type16SAT.KDecK16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.Cls16C

@[expose] public section

/-!
# Type 16, J7: core MZMMU, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsMZMMU`, class clause `clauseMZMMU`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core MZMMU. -/
def allDMZMMU (n : Nat) : Bool := rowSK unitsMZMMU clauseMZMMU chunksMZMMU n

/-- Chunk 0 of core MZMMU: all rows pass. -/
theorem chkMZMMU0 : (rowsMZMMU0.all allDMZMMU) = true := by decide +kernel

/-- Chunk 1 of core MZMMU: all rows pass. -/
theorem chkMZMMU1 : (rowsMZMMU1.all allDMZMMU) = true := by decide +kernel

/-- Chunk 2 of core MZMMU: all rows pass. -/
theorem chkMZMMU2 : (rowsMZMMU2.all allDMZMMU) = true := by decide +kernel

/-- Chunk 3 of core MZMMU: all rows pass. -/
theorem chkMZMMU3 : (rowsMZMMU3.all allDMZMMU) = true := by decide +kernel

/-- Chunk 4 of core MZMMU: all rows pass. -/
theorem chkMZMMU4 : (rowsMZMMU4.all allDMZMMU) = true := by decide +kernel

/-- Chunk 5 of core MZMMU: all rows pass. -/
theorem chkMZMMU5 : (rowsMZMMU5.all allDMZMMU) = true := by decide +kernel

/-- Chunk 6 of core MZMMU: all rows pass. -/
theorem chkMZMMU6 : (rowsMZMMU6.all allDMZMMU) = true := by decide +kernel

/-- Chunk 7 of core MZMMU: all rows pass. -/
theorem chkMZMMU7 : (rowsMZMMU7.all allDMZMMU) = true := by decide +kernel

/-- Chunk 8 of core MZMMU: all rows pass. -/
theorem chkMZMMU8 : (rowsMZMMU8.all allDMZMMU) = true := by decide +kernel

/-- Chunk 9 of core MZMMU: all rows pass. -/
theorem chkMZMMU9 : (rowsMZMMU9.all allDMZMMU) = true := by decide +kernel

/-- Chunk 10 of core MZMMU: all rows pass. -/
theorem chkMZMMU10 : (rowsMZMMU10.all allDMZMMU) = true := by decide +kernel

/-- Chunk 11 of core MZMMU: all rows pass. -/
theorem chkMZMMU11 : (rowsMZMMU11.all allDMZMMU) = true := by decide +kernel

/-- Every row of core MZMMU passes the check. -/
theorem allOKMZMMU : ∀ ch ∈ rowsMZMMU, ∀ n ∈ ch, allDMZMMU n = true := by
  intro ch hch n hn
  simp only [rowsMZMMU, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkMZMMU0 n hn
  · exact List.all_eq_true.mp chkMZMMU1 n hn
  · exact List.all_eq_true.mp chkMZMMU2 n hn
  · exact List.all_eq_true.mp chkMZMMU3 n hn
  · exact List.all_eq_true.mp chkMZMMU4 n hn
  · exact List.all_eq_true.mp chkMZMMU5 n hn
  · exact List.all_eq_true.mp chkMZMMU6 n hn
  · exact List.all_eq_true.mp chkMZMMU7 n hn
  · exact List.all_eq_true.mp chkMZMMU8 n hn
  · exact List.all_eq_true.mp chkMZMMU9 n hn
  · exact List.all_eq_true.mp chkMZMMU10 n hn
  · exact List.all_eq_true.mp chkMZMMU11 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core MZMMU are true when the four class brackets have the signs `-0--`. -/
theorem unitsMZMMU_true (F : S0xFac 8 V2.fIdx x) (h0 : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsMZMMU, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsMZMMU, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 0 1 2 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]


/-- The case clause of core MZMMU holds when `CaseT16 x` (`x 1 - x 6` is not orthogonal to both `x 0 - x 3` and `x 0 - x 6`). -/
theorem clauseMZMMU_true (F : S0xFac 8 V2.fIdx x) (h : CaseT16 x) : HoldsW (rhoW (geoF F)) clauseMZMMU := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v2 : (geoF F).vv 2 = x 0 - x 3 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e3]
  have v5 : (geoF F).vv 5 = x 0 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e6]
  have v10 : (geoF F).vv 10 = x 1 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e1, e6]
  rcases h with h | h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 2 10)), by simp [clauseMZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
    · refine ⟨(true, W.base (V.tp 2 10)), by simp [clauseMZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 5 10)), by simp [clauseMZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h
    · refine ⟨(true, W.base (V.tp 5 10)), by simp [clauseMZMMU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h

/-- **Core MZMMU gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16TW`. -/
theorem rupert_of_core_dataMZMMU (hU : CoreUnsat rowsMZMMU) : Core16TW (-1) 0 (-1) (-1) := by
  intro y F hC h1 h2 h3 h4 hA
  exact caseSK_of_unsat chunksMZMMU rowsMZMMU unitsMZMMU clauseMZMMU hU allOKMZMMU F hC
    (unitsMZMMU_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)) (clauseMZMMU_true F hA)

end Minimality.H16K.SAT
