module

public import Minimality.Type16SAT.DataPMPMZ
public import Minimality.Type16SAT.KDecX16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16Z

@[expose] public section

/-!
# Type 16, J7: core PMPMZ, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsPMPMZ`, class clause `clausePMPMZ`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PMPMZ. -/
def allDPMPMZ (n : Nat) : Bool := rowSKX unitsPMPMZ clausePMPMZ chunksPMPMZ n

/-- Chunk 0 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ0 : (rowsPMPMZ0.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 1 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ1 : (rowsPMPMZ1.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 2 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ2 : (rowsPMPMZ2.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 3 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ3 : (rowsPMPMZ3.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 4 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ4 : (rowsPMPMZ4.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 5 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ5 : (rowsPMPMZ5.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 6 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ6 : (rowsPMPMZ6.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 7 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ7 : (rowsPMPMZ7.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 8 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ8 : (rowsPMPMZ8.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 9 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ9 : (rowsPMPMZ9.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 10 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ10 : (rowsPMPMZ10.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 11 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ11 : (rowsPMPMZ11.all allDPMPMZ) = true := by decide +kernel

/-- Chunk 12 of core PMPMZ: all rows pass. -/
theorem chkPMPMZ12 : (rowsPMPMZ12.all allDPMPMZ) = true := by decide +kernel

/-- Every row of core PMPMZ passes the check. -/
theorem allOKPMPMZ : ∀ ch ∈ rowsPMPMZ, ∀ n ∈ ch, allDPMPMZ n = true := by
  intro ch hch n hn
  simp only [rowsPMPMZ, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPMPMZ0 n hn
  · exact List.all_eq_true.mp chkPMPMZ1 n hn
  · exact List.all_eq_true.mp chkPMPMZ2 n hn
  · exact List.all_eq_true.mp chkPMPMZ3 n hn
  · exact List.all_eq_true.mp chkPMPMZ4 n hn
  · exact List.all_eq_true.mp chkPMPMZ5 n hn
  · exact List.all_eq_true.mp chkPMPMZ6 n hn
  · exact List.all_eq_true.mp chkPMPMZ7 n hn
  · exact List.all_eq_true.mp chkPMPMZ8 n hn
  · exact List.all_eq_true.mp chkPMPMZ9 n hn
  · exact List.all_eq_true.mp chkPMPMZ10 n hn
  · exact List.all_eq_true.mp chkPMPMZ11 n hn
  · exact List.all_eq_true.mp chkPMPMZ12 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PMPMZ are true when the four class brackets have the signs `+-+-`. -/
theorem unitsPMPMZ_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0) (h2 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1)) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsPMPMZ, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPMPMZ, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 1 2 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]


/-- The case clause of core PMPMZ holds when some of the 18 shape entries of `Z` is nonzero (`¬ ZShape16 x F`). -/
theorem clausePMPMZ_true (F : S0xFac 8 V2.fIdx x) (h : ¬ ZShape16 x F) : HoldsW (rhoW (geoF F)) clausePMPMZ := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have n0 : (geoF F).N 0 = F.N 0 := geoF_N F 0
  have n1 : (geoF F).N 1 = F.N 1 := geoF_N F 1
  have n2 : (geoF F).N 2 = F.N 2 := geoF_N F 2
  have n3 : (geoF F).N 3 = F.N 3 := geoF_N F 3
  have n5 : (geoF F).N 5 = F.N 5 := geoF_N F 5
  have n6 : (geoF F).N 6 = F.N 6 := geoF_N F 6
  by_contra hc
  apply h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 9 17) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 10 16) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 0 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 4) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 4 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 2 3 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 5 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.nv 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePMPMZ]) (by simp [clausePMPMZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne

/-- **Core PMPMZ gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16Z`. -/
theorem rupert_of_core_dataPMPMZ (hU : CoreUnsat rowsPMPMZ) : Core16Z 1 (-1) 1 (-1) := by
  intro y F hC h1 h2 h3 h4 hA
  exact caseSKX_of_unsat chunksPMPMZ rowsPMPMZ unitsPMPMZ clausePMPMZ hU allOKPMPMZ F hC
    (unitsPMPMZ_true F (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith)
      (by simp only [br16] at h1 h2 h3 h4; linarith) (by simp only [br16] at h1 h2 h3 h4; linarith)) (clausePMPMZ_true F hA)

end Minimality.H16K.SAT
