module

public import Minimality.Type16SAT.DataPZMZZZ
public import Minimality.Type16SAT.KDec2X16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.Cls16ZZ
public import Minimality.Type16SAT.Cls16Z

@[expose] public section

/-!
# Type 16, J7: core PZMZZZ, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsPZMZZZ`, class clause `clausePZMZZZ`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core PZMZZZ. -/
def allDPZMZZZ (n : Nat) : Bool := rowSK2X unitsPZMZZZ clausePZMZZZ clause2PZMZZZ chunksPZMZZZ n

/-- Chunk 0 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ0 : (rowsPZMZZZ0.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 1 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ1 : (rowsPZMZZZ1.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 2 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ2 : (rowsPZMZZZ2.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 3 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ3 : (rowsPZMZZZ3.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 4 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ4 : (rowsPZMZZZ4.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 5 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ5 : (rowsPZMZZZ5.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 6 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ6 : (rowsPZMZZZ6.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 7 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ7 : (rowsPZMZZZ7.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 8 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ8 : (rowsPZMZZZ8.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 9 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ9 : (rowsPZMZZZ9.all allDPZMZZZ) = true := by decide +kernel

/-- Chunk 10 of core PZMZZZ: all rows pass. -/
theorem chkPZMZZZ10 : (rowsPZMZZZ10.all allDPZMZZZ) = true := by decide +kernel

/-- Every row of core PZMZZZ passes the check. -/
theorem allOKPZMZZZ : ∀ ch ∈ rowsPZMZZZ, ∀ n ∈ ch, allDPZMZZZ n = true := by
  intro ch hch n hn
  simp only [rowsPZMZZZ, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPZMZZZ0 n hn
  · exact List.all_eq_true.mp chkPZMZZZ1 n hn
  · exact List.all_eq_true.mp chkPZMZZZ2 n hn
  · exact List.all_eq_true.mp chkPZMZZZ3 n hn
  · exact List.all_eq_true.mp chkPZMZZZ4 n hn
  · exact List.all_eq_true.mp chkPZMZZZ5 n hn
  · exact List.all_eq_true.mp chkPZMZZZ6 n hn
  · exact List.all_eq_true.mp chkPZMZZZ7 n hn
  · exact List.all_eq_true.mp chkPZMZZZ8 n hn
  · exact List.all_eq_true.mp chkPZMZZZ9 n hn
  · exact List.all_eq_true.mp chkPZMZZZ10 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core PZMZZZ are true when the four class brackets have the signs `+0-0`. -/
theorem unitsPZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h0 : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) = 0) :
    ∀ l ∈ unitsPZMZZZ, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsPZMZZZ, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]


/-- The case clause of core PZMZZZ holds when some of the 18 shape entries of `Z` is nonzero (`¬ ZShape16 x F`). -/
theorem clausePZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h : ¬ ZShape16 x F) : HoldsW (rhoW (geoF F)) clausePZMZZZ := by
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
    refine hc (holdsW_atom_ne (a := V.lv 0 1 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 9 17) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 10 16) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 0 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 4) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 4 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 2 3 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 5 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.nv 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clausePZMZZZ]) (by simp [clausePZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne

/-- The second case clause of core PZMZZZ holds when some of the `sigma16` images of the 18 shape entries of `Z` is nonzero
(`¬ ZShape16 (x ∘ sigma16) (sigFac F)`). -/
theorem clause2PZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h : ¬ ZShape16 (x ∘ sigma16) (sigFac F)) : HoldsW (rhoW (geoF F)) clause2PZMZZZ := by
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
  have n4 : (geoF F).N 4 = F.N 4 := geoF_N F 4
  have n5 : (geoF F).N 5 = F.N 5 := geoF_N F 5
  have n6 : (geoF F).N 6 = F.N 6 := geoF_N F 6
  have n7 : (geoF F).N 7 = F.N 7 := geoF_N F 7
  by_contra hc
  apply h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 2 5 6 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 2 5 6 0 3) = det3 (x 5 - x 2) (x 6 - x 2) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 6) (x 5 - x 6) (x 3 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 2 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 2 6 3 5) = det3 (x 2 - x 0) (x 6 - x 0) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 6) (x 0 - x 6) (x 3 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 0 2 13) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.kv 0 2 13) = det3 (x 0 - x 3) (x 2 - x 5) (F.N 0) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 5) (x 3 - x 0) (F.N 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 0 1 16) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.kv 0 1 16) = det3 (x 0 - x 2) (x 3 - x 5) (F.N 0) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 0) (x 3 - x 5) (F.N 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 1 0 2) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 1 0 2) = inner ℝ (F.N 1) (x 0 - x 2) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 1) (x 2 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 2 4) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 2 4) = inner ℝ (F.N 3) (x 2 - x 4) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 2 - x 4) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 2 5) = inner ℝ (F.N 3) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 2 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 4 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 4 5) = inner ℝ (F.N 3) (x 4 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 4 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 3 6) = inner ℝ (F.N 7) (x 3 - x 6) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 6 - x 3) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 0 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 0 6) = inner ℝ (F.N 7) (x 0 - x 6) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 6 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 5 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 1 2 5 0 3) = det3 (x 2 - x 1) (x 5 - x 1) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 1 - x 2) (x 5 - x 2) (x 3 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 1 2 3 5) = det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 1 - x 2) (x 0 - x 2) (x 3 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 0 3) = inner ℝ (F.N 7) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 3 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 2 3 5) = inner ℝ (F.N 2) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 2) (x 3 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 3 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 1 3 2 5) = det3 (x 1 - x 0) (x 3 - x 0) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 3 - x 1) (x 0 - x 1) (x 2 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 3 4 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 3 4 2 5) = det3 (x 3 - x 0) (x 4 - x 0) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 4 - x 3) (x 0 - x 3) (x 2 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 5 0 2) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 3 4 5 0 2) = det3 (x 4 - x 3) (x 5 - x 3) (x 0 - x 2) := by
      simp [Minimality.H16.SAT.Geo.atom, e0, e2, e3, e4, e5]
    rw [ha] at h0
    show det3 (x 4 - x 3) (x 5 - x 3) (x 2 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.nv 3 6 7) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2PZMZZZ]) (by simp [clause2PZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.nv 3 6 7) = det3 (F.N 3) (F.N 6) (F.N 7) := by
      simp [Minimality.H16.SAT.Geo.atom, n3, n6, n7]
    rw [ha] at h0
    show det3 (F.N 6) (F.N 3) (F.N 7) = 0
    (simp only [det3_expand] at h0 ⊢; linear_combination (-1) * h0)

/-- **Core PZMZZZ gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16ZZW`. -/
theorem rupert_of_core_dataPZMZZZ (hU : CoreUnsat rowsPZMZZZ) : Core16ZZW 1 0 (-1) 0 := by
  intro y F hC h1 h2 h3 h4 hA hB
  exact caseSK2X_of_unsat chunksPZMZZZ rowsPZMZZZ unitsPZMZZZ clausePZMZZZ clause2PZMZZZ hU allOKPZMZZZ F hC
    (unitsPZMZZZ_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)) (clausePZMZZZ_true F hA) (clause2PZMZZZ_true F hB)

end Minimality.H16K.SAT
