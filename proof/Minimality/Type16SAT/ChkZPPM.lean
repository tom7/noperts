module

public import Minimality.Type16SAT.DataZPPM
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W

@[expose] public section

/-!
# Type 16, J7: core ZPPM, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsZPPM`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core ZPPM. -/
def allDZPPM (n : Nat) : Bool := rowS unitsZPPM chunksZPPM n

/-- Chunk 0 of core ZPPM: all rows pass. -/
theorem chkZPPM0 : (rowsZPPM0.all allDZPPM) = true := by decide +kernel

/-- Chunk 1 of core ZPPM: all rows pass. -/
theorem chkZPPM1 : (rowsZPPM1.all allDZPPM) = true := by decide +kernel

/-- Chunk 2 of core ZPPM: all rows pass. -/
theorem chkZPPM2 : (rowsZPPM2.all allDZPPM) = true := by decide +kernel

/-- Chunk 3 of core ZPPM: all rows pass. -/
theorem chkZPPM3 : (rowsZPPM3.all allDZPPM) = true := by decide +kernel

/-- Chunk 4 of core ZPPM: all rows pass. -/
theorem chkZPPM4 : (rowsZPPM4.all allDZPPM) = true := by decide +kernel

/-- Chunk 5 of core ZPPM: all rows pass. -/
theorem chkZPPM5 : (rowsZPPM5.all allDZPPM) = true := by decide +kernel

/-- Chunk 6 of core ZPPM: all rows pass. -/
theorem chkZPPM6 : (rowsZPPM6.all allDZPPM) = true := by decide +kernel

/-- Chunk 7 of core ZPPM: all rows pass. -/
theorem chkZPPM7 : (rowsZPPM7.all allDZPPM) = true := by decide +kernel

/-- Every row of core ZPPM passes the check. -/
theorem allOKZPPM : ∀ ch ∈ rowsZPPM, ∀ n ∈ ch, allDZPPM n = true := by
  intro ch hch n hn
  simp only [rowsZPPM, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZPPM0 n hn
  · exact List.all_eq_true.mp chkZPPM1 n hn
  · exact List.all_eq_true.mp chkZPPM2 n hn
  · exact List.all_eq_true.mp chkZPPM3 n hn
  · exact List.all_eq_true.mp chkZPPM4 n hn
  · exact List.all_eq_true.mp chkZPPM5 n hn
  · exact List.all_eq_true.mp chkZPPM6 n hn
  · exact List.all_eq_true.mp chkZPPM7 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core ZPPM are true when the four class brackets have the signs `0++-`. -/
theorem unitsZPPM_true (F : S0xFac 8 V2.fIdx x) (h0 : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = 0) (h1 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h2 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1)) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsZPPM, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsZPPM, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 2 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 1 2 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core ZPPM gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataZPPM (hU : CoreUnsat rowsZPPM) : Core16W 0 1 1 (-1) := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksZPPM rowsZPPM unitsZPPM hU allOKZPPM F hC
    (unitsZPPM_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
