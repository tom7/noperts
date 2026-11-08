module

public import Minimality.Type16SAT.DataPMZP
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W

@[expose] public section

/-!
# Type 16, J7: core PMZP, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsPMZP`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PMZP. -/
def allDPMZP (n : Nat) : Bool := rowS unitsPMZP chunksPMZP n

/-- Chunk 0 of core PMZP: all rows pass. -/
theorem chkPMZP0 : (rowsPMZP0.all allDPMZP) = true := by decide +kernel

/-- Chunk 1 of core PMZP: all rows pass. -/
theorem chkPMZP1 : (rowsPMZP1.all allDPMZP) = true := by decide +kernel

/-- Chunk 2 of core PMZP: all rows pass. -/
theorem chkPMZP2 : (rowsPMZP2.all allDPMZP) = true := by decide +kernel

/-- Chunk 3 of core PMZP: all rows pass. -/
theorem chkPMZP3 : (rowsPMZP3.all allDPMZP) = true := by decide +kernel

/-- Chunk 4 of core PMZP: all rows pass. -/
theorem chkPMZP4 : (rowsPMZP4.all allDPMZP) = true := by decide +kernel

/-- Chunk 5 of core PMZP: all rows pass. -/
theorem chkPMZP5 : (rowsPMZP5.all allDPMZP) = true := by decide +kernel

/-- Chunk 6 of core PMZP: all rows pass. -/
theorem chkPMZP6 : (rowsPMZP6.all allDPMZP) = true := by decide +kernel

/-- Every row of core PMZP passes the check. -/
theorem allOKPMZP : ∀ ch ∈ rowsPMZP, ∀ n ∈ ch, allDPMZP n = true := by
  intro ch hch n hn
  simp only [rowsPMZP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPMZP0 n hn
  · exact List.all_eq_true.mp chkPMZP1 n hn
  · exact List.all_eq_true.mp chkPMZP2 n hn
  · exact List.all_eq_true.mp chkPMZP3 n hn
  · exact List.all_eq_true.mp chkPMZP4 n hn
  · exact List.all_eq_true.mp chkPMZP5 n hn
  · exact List.all_eq_true.mp chkPMZP6 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PMZP are true when the four class brackets have the signs `+-0+`. -/
theorem unitsPMZP_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsPMZP, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPMZP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 1 2 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core PMZP gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataPMZP (hU : CoreUnsat rowsPMZP) : Core16W 1 (-1) 0 1 := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksPMZP rowsPMZP unitsPMZP hU allOKPMZP F hC
    (unitsPMZP_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
