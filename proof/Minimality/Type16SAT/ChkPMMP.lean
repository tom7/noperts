module

public import Minimality.Type16SAT.DataPMMP
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16, J7: core PMMP, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsPMMP`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PMMP. -/
def allDPMMP (n : Nat) : Bool := rowS unitsPMMP chunksPMMP n

/-- Chunk 0 of core PMMP: all rows pass. -/
theorem chkPMMP0 : (rowsPMMP0.all allDPMMP) = true := by decide +kernel

/-- Chunk 1 of core PMMP: all rows pass. -/
theorem chkPMMP1 : (rowsPMMP1.all allDPMMP) = true := by decide +kernel

/-- Chunk 2 of core PMMP: all rows pass. -/
theorem chkPMMP2 : (rowsPMMP2.all allDPMMP) = true := by decide +kernel

/-- Chunk 3 of core PMMP: all rows pass. -/
theorem chkPMMP3 : (rowsPMMP3.all allDPMMP) = true := by decide +kernel

/-- Chunk 4 of core PMMP: all rows pass. -/
theorem chkPMMP4 : (rowsPMMP4.all allDPMMP) = true := by decide +kernel

/-- Chunk 5 of core PMMP: all rows pass. -/
theorem chkPMMP5 : (rowsPMMP5.all allDPMMP) = true := by decide +kernel

/-- Chunk 6 of core PMMP: all rows pass. -/
theorem chkPMMP6 : (rowsPMMP6.all allDPMMP) = true := by decide +kernel

/-- Chunk 7 of core PMMP: all rows pass. -/
theorem chkPMMP7 : (rowsPMMP7.all allDPMMP) = true := by decide +kernel

/-- Chunk 8 of core PMMP: all rows pass. -/
theorem chkPMMP8 : (rowsPMMP8.all allDPMMP) = true := by decide +kernel

/-- Chunk 9 of core PMMP: all rows pass. -/
theorem chkPMMP9 : (rowsPMMP9.all allDPMMP) = true := by decide +kernel

/-- Chunk 10 of core PMMP: all rows pass. -/
theorem chkPMMP10 : (rowsPMMP10.all allDPMMP) = true := by decide +kernel

/-- Chunk 11 of core PMMP: all rows pass. -/
theorem chkPMMP11 : (rowsPMMP11.all allDPMMP) = true := by decide +kernel

/-- Every row of core PMMP passes the check. -/
theorem allOKPMMP : ∀ ch ∈ rowsPMMP, ∀ n ∈ ch, allDPMMP n = true := by
  intro ch hch n hn
  simp only [rowsPMMP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPMMP0 n hn
  · exact List.all_eq_true.mp chkPMMP1 n hn
  · exact List.all_eq_true.mp chkPMMP2 n hn
  · exact List.all_eq_true.mp chkPMMP3 n hn
  · exact List.all_eq_true.mp chkPMMP4 n hn
  · exact List.all_eq_true.mp chkPMMP5 n hn
  · exact List.all_eq_true.mp chkPMMP6 n hn
  · exact List.all_eq_true.mp chkPMMP7 n hn
  · exact List.all_eq_true.mp chkPMMP8 n hn
  · exact List.all_eq_true.mp chkPMMP9 n hn
  · exact List.all_eq_true.mp chkPMMP10 n hn
  · exact List.all_eq_true.mp chkPMMP11 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PMMP are true when the four class brackets have the signs `+--+`. -/
theorem unitsPMMP_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsPMMP, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPMMP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core PMMP gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataPMMP (hU : CoreUnsat rowsPMMP) : Core16 1 (-1) (-1) 1 := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksPMMP rowsPMMP unitsPMMP hU allOKPMMP F hC
    (unitsPMMP_true F (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith)
      (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
