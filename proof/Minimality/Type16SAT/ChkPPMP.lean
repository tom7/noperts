module

public import Minimality.Type16SAT.DataPPMP
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16, J7: core PPMP, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsPPMP`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PPMP. -/
def allDPPMP (n : Nat) : Bool := rowS unitsPPMP chunksPPMP n

/-- Chunk 0 of core PPMP: all rows pass. -/
theorem chkPPMP0 : (rowsPPMP0.all allDPPMP) = true := by decide +kernel

/-- Chunk 1 of core PPMP: all rows pass. -/
theorem chkPPMP1 : (rowsPPMP1.all allDPPMP) = true := by decide +kernel

/-- Chunk 2 of core PPMP: all rows pass. -/
theorem chkPPMP2 : (rowsPPMP2.all allDPPMP) = true := by decide +kernel

/-- Chunk 3 of core PPMP: all rows pass. -/
theorem chkPPMP3 : (rowsPPMP3.all allDPPMP) = true := by decide +kernel

/-- Chunk 4 of core PPMP: all rows pass. -/
theorem chkPPMP4 : (rowsPPMP4.all allDPPMP) = true := by decide +kernel

/-- Chunk 5 of core PPMP: all rows pass. -/
theorem chkPPMP5 : (rowsPPMP5.all allDPPMP) = true := by decide +kernel

/-- Chunk 6 of core PPMP: all rows pass. -/
theorem chkPPMP6 : (rowsPPMP6.all allDPPMP) = true := by decide +kernel

/-- Chunk 7 of core PPMP: all rows pass. -/
theorem chkPPMP7 : (rowsPPMP7.all allDPPMP) = true := by decide +kernel

/-- Chunk 8 of core PPMP: all rows pass. -/
theorem chkPPMP8 : (rowsPPMP8.all allDPPMP) = true := by decide +kernel

/-- Chunk 9 of core PPMP: all rows pass. -/
theorem chkPPMP9 : (rowsPPMP9.all allDPPMP) = true := by decide +kernel

/-- Chunk 10 of core PPMP: all rows pass. -/
theorem chkPPMP10 : (rowsPPMP10.all allDPPMP) = true := by decide +kernel

/-- Every row of core PPMP passes the check. -/
theorem allOKPPMP : ∀ ch ∈ rowsPPMP, ∀ n ∈ ch, allDPPMP n = true := by
  intro ch hch n hn
  simp only [rowsPPMP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPPMP0 n hn
  · exact List.all_eq_true.mp chkPPMP1 n hn
  · exact List.all_eq_true.mp chkPPMP2 n hn
  · exact List.all_eq_true.mp chkPPMP3 n hn
  · exact List.all_eq_true.mp chkPPMP4 n hn
  · exact List.all_eq_true.mp chkPPMP5 n hn
  · exact List.all_eq_true.mp chkPPMP6 n hn
  · exact List.all_eq_true.mp chkPPMP7 n hn
  · exact List.all_eq_true.mp chkPPMP8 n hn
  · exact List.all_eq_true.mp chkPPMP9 n hn
  · exact List.all_eq_true.mp chkPPMP10 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PPMP are true when the four class brackets have the signs `++-+`. -/
theorem unitsPPMP_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsPPMP, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPPMP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core PPMP gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataPPMP (hU : CoreUnsat rowsPPMP) : Core16 1 1 (-1) 1 := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksPPMP rowsPPMP unitsPPMP hU allOKPPMP F hC
    (unitsPPMP_true F (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith)
      (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
