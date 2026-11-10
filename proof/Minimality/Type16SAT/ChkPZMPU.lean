module

public import Minimality.Type16SAT.DataPZMPU
public import Minimality.Type16SAT.KDecK16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.Cls16C

@[expose] public section

/-!
# Type 16, J7: core PZMPU, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsPZMPU`, class clause `clausePZMPU`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PZMPU. -/
def allDPZMPU (n : Nat) : Bool := rowSK unitsPZMPU clausePZMPU chunksPZMPU n

/-- Chunk 0 of core PZMPU: all rows pass. -/
theorem chkPZMPU0 : (rowsPZMPU0.all allDPZMPU) = true := by decide +kernel

/-- Chunk 1 of core PZMPU: all rows pass. -/
theorem chkPZMPU1 : (rowsPZMPU1.all allDPZMPU) = true := by decide +kernel

/-- Chunk 2 of core PZMPU: all rows pass. -/
theorem chkPZMPU2 : (rowsPZMPU2.all allDPZMPU) = true := by decide +kernel

/-- Chunk 3 of core PZMPU: all rows pass. -/
theorem chkPZMPU3 : (rowsPZMPU3.all allDPZMPU) = true := by decide +kernel

/-- Chunk 4 of core PZMPU: all rows pass. -/
theorem chkPZMPU4 : (rowsPZMPU4.all allDPZMPU) = true := by decide +kernel

/-- Chunk 5 of core PZMPU: all rows pass. -/
theorem chkPZMPU5 : (rowsPZMPU5.all allDPZMPU) = true := by decide +kernel

/-- Chunk 6 of core PZMPU: all rows pass. -/
theorem chkPZMPU6 : (rowsPZMPU6.all allDPZMPU) = true := by decide +kernel

/-- Chunk 7 of core PZMPU: all rows pass. -/
theorem chkPZMPU7 : (rowsPZMPU7.all allDPZMPU) = true := by decide +kernel

/-- Chunk 8 of core PZMPU: all rows pass. -/
theorem chkPZMPU8 : (rowsPZMPU8.all allDPZMPU) = true := by decide +kernel

/-- Chunk 9 of core PZMPU: all rows pass. -/
theorem chkPZMPU9 : (rowsPZMPU9.all allDPZMPU) = true := by decide +kernel

/-- Chunk 10 of core PZMPU: all rows pass. -/
theorem chkPZMPU10 : (rowsPZMPU10.all allDPZMPU) = true := by decide +kernel

/-- Every row of core PZMPU passes the check. -/
theorem allOKPZMPU : ∀ ch ∈ rowsPZMPU, ∀ n ∈ ch, allDPZMPU n = true := by
  intro ch hch n hn
  simp only [rowsPZMPU, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPZMPU0 n hn
  · exact List.all_eq_true.mp chkPZMPU1 n hn
  · exact List.all_eq_true.mp chkPZMPU2 n hn
  · exact List.all_eq_true.mp chkPZMPU3 n hn
  · exact List.all_eq_true.mp chkPZMPU4 n hn
  · exact List.all_eq_true.mp chkPZMPU5 n hn
  · exact List.all_eq_true.mp chkPZMPU6 n hn
  · exact List.all_eq_true.mp chkPZMPU7 n hn
  · exact List.all_eq_true.mp chkPZMPU8 n hn
  · exact List.all_eq_true.mp chkPZMPU9 n hn
  · exact List.all_eq_true.mp chkPZMPU10 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PZMPU are true when the four class brackets have the signs `+0-+`. -/
theorem unitsPZMPU_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsPZMPU, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPZMPU, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]


/-- The case clause of core PZMPU holds when `CaseT16 x` (`x 1 - x 6` is not orthogonal to both `x 0 - x 3` and `x 0 - x 6`). -/
theorem clausePZMPU_true (F : S0xFac 8 V2.fIdx x) (h : CaseT16 x) : HoldsW (rhoW (geoF F)) clausePZMPU := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v2 : (geoF F).vv 2 = x 0 - x 3 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e3]
  have v5 : (geoF F).vv 5 = x 0 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e6]
  have v10 : (geoF F).vv 10 = x 1 - x 6 := by simp [Minimality.H16.SAT.Geo.vv, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e1, e6]
  rcases h with h | h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 2 10)), by simp [clausePZMPU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
    · refine ⟨(true, W.base (V.tp 2 10)), by simp [clausePZMPU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 2 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v2, v10] using h
  · rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 5 10)), by simp [clausePZMPU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tq 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h
    · refine ⟨(true, W.base (V.tp 5 10)), by simp [clausePZMPU], ?_⟩
      show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.tp 5 10) = true
      simpa [evalL, Minimality.H16.SAT.rho, v5, v10] using h

/-- **Core PZMPU gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16TW`. -/
theorem rupert_of_core_dataPZMPU (hU : CoreUnsat rowsPZMPU) : Core16TW 1 0 (-1) 1 := by
  intro y F hC h1 h2 h3 h4 hA
  exact caseSK_of_unsat chunksPZMPU rowsPZMPU unitsPZMPU clausePZMPU hU allOKPZMPU F hC
    (unitsPZMPU_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)) (clausePZMPU_true F hA)

end Minimality.H16K.SAT
