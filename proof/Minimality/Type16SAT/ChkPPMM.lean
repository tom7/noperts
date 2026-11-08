module

public import Minimality.Type16SAT.DataPPMM
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16, J7: core PPMM, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsPPMM`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PPMM. -/
def allDPPMM (n : Nat) : Bool := rowS unitsPPMM chunksPPMM n

/-- Chunk 0 of core PPMM: all rows pass. -/
theorem chkPPMM0 : (rowsPPMM0.all allDPPMM) = true := by decide +kernel

/-- Chunk 1 of core PPMM: all rows pass. -/
theorem chkPPMM1 : (rowsPPMM1.all allDPPMM) = true := by decide +kernel

/-- Chunk 2 of core PPMM: all rows pass. -/
theorem chkPPMM2 : (rowsPPMM2.all allDPPMM) = true := by decide +kernel

/-- Chunk 3 of core PPMM: all rows pass. -/
theorem chkPPMM3 : (rowsPPMM3.all allDPPMM) = true := by decide +kernel

/-- Chunk 4 of core PPMM: all rows pass. -/
theorem chkPPMM4 : (rowsPPMM4.all allDPPMM) = true := by decide +kernel

/-- Chunk 5 of core PPMM: all rows pass. -/
theorem chkPPMM5 : (rowsPPMM5.all allDPPMM) = true := by decide +kernel

/-- Chunk 6 of core PPMM: all rows pass. -/
theorem chkPPMM6 : (rowsPPMM6.all allDPPMM) = true := by decide +kernel

/-- Chunk 7 of core PPMM: all rows pass. -/
theorem chkPPMM7 : (rowsPPMM7.all allDPPMM) = true := by decide +kernel

/-- Chunk 8 of core PPMM: all rows pass. -/
theorem chkPPMM8 : (rowsPPMM8.all allDPPMM) = true := by decide +kernel

/-- Chunk 9 of core PPMM: all rows pass. -/
theorem chkPPMM9 : (rowsPPMM9.all allDPPMM) = true := by decide +kernel

/-- Chunk 10 of core PPMM: all rows pass. -/
theorem chkPPMM10 : (rowsPPMM10.all allDPPMM) = true := by decide +kernel

/-- Chunk 11 of core PPMM: all rows pass. -/
theorem chkPPMM11 : (rowsPPMM11.all allDPPMM) = true := by decide +kernel

/-- Every row of core PPMM passes the check. -/
theorem allOKPPMM : ∀ ch ∈ rowsPPMM, ∀ n ∈ ch, allDPPMM n = true := by
  intro ch hch n hn
  simp only [rowsPPMM, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPPMM0 n hn
  · exact List.all_eq_true.mp chkPPMM1 n hn
  · exact List.all_eq_true.mp chkPPMM2 n hn
  · exact List.all_eq_true.mp chkPPMM3 n hn
  · exact List.all_eq_true.mp chkPPMM4 n hn
  · exact List.all_eq_true.mp chkPPMM5 n hn
  · exact List.all_eq_true.mp chkPPMM6 n hn
  · exact List.all_eq_true.mp chkPPMM7 n hn
  · exact List.all_eq_true.mp chkPPMM8 n hn
  · exact List.all_eq_true.mp chkPPMM9 n hn
  · exact List.all_eq_true.mp chkPPMM10 n hn
  · exact List.all_eq_true.mp chkPPMM11 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PPMM are true when the four class brackets have the signs `++--`. -/
theorem unitsPPMM_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsPPMM, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPPMM, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core PPMM gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataPPMM (hU : CoreUnsat rowsPPMM) : Core16 1 1 (-1) (-1) := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksPPMM rowsPPMM unitsPPMM hU allOKPPMM F hC
    (unitsPPMM_true F (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith)
      (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
