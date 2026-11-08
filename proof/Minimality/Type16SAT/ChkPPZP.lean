module

public import Minimality.Type16SAT.DataPPZP
public import Minimality.Type16SAT.KDec16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W

@[expose] public section

/-!
# Type 16, J7: core PPZP, the kernel checks of all rows (dispatcher `rowS`, class literals `unitsPPZP`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PPZP. -/
def allDPPZP (n : Nat) : Bool := rowS unitsPPZP chunksPPZP n

/-- Chunk 0 of core PPZP: all rows pass. -/
theorem chkPPZP0 : (rowsPPZP0.all allDPPZP) = true := by decide +kernel

/-- Chunk 1 of core PPZP: all rows pass. -/
theorem chkPPZP1 : (rowsPPZP1.all allDPPZP) = true := by decide +kernel

/-- Chunk 2 of core PPZP: all rows pass. -/
theorem chkPPZP2 : (rowsPPZP2.all allDPPZP) = true := by decide +kernel

/-- Every row of core PPZP passes the check. -/
theorem allOKPPZP : ∀ ch ∈ rowsPPZP, ∀ n ∈ ch, allDPPZP n = true := by
  intro ch hch n hn
  simp only [rowsPPZP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPPZP0 n hn
  · exact List.all_eq_true.mp chkPPZP1 n hn
  · exact List.all_eq_true.mp chkPPZP2 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PPZP are true when the four class brackets have the signs `++0+`. -/
theorem unitsPPZP_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = 0) (h3 : 0 < det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2)) :
    ∀ l ∈ unitsPPZP, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPPZP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 1 2 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]

/-- **Core PPZP gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16`. -/
theorem rupert_of_core_dataPPZP (hU : CoreUnsat rowsPPZP) : Core16W 1 1 0 1 := by
  intro y F hC h1 h2 h3 h4
  exact caseS_of_unsat chunksPPZP rowsPPZP unitsPPZP hU allOKPPZP F hC
    (unitsPPZP_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith))

end Minimality.H16K.SAT
