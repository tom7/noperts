module

public import Minimality.Type16SAT.DataZZMZZZ
public import Minimality.Type16SAT.KDec2X16
public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.Cls16ZZ
public import Minimality.Type16SAT.Cls16Z

@[expose] public section

/-!
# Type 16, J7: core ZZMZZZ, the kernel checks of all rows (dispatcher `rowSK`, class literals `unitsZZMZZZ`, class clause `clauseZZMZZZ`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

/-- The row check of core ZZMZZZ. -/
def allDZZMZZZ (n : Nat) : Bool := rowSK2X unitsZZMZZZ clauseZZMZZZ clause2ZZMZZZ chunksZZMZZZ n

/-- Chunk 0 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ0 : (rowsZZMZZZ0.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 1 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ1 : (rowsZZMZZZ1.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 2 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ2 : (rowsZZMZZZ2.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 3 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ3 : (rowsZZMZZZ3.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 4 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ4 : (rowsZZMZZZ4.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 5 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ5 : (rowsZZMZZZ5.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 6 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ6 : (rowsZZMZZZ6.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 7 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ7 : (rowsZZMZZZ7.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 8 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ8 : (rowsZZMZZZ8.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 9 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ9 : (rowsZZMZZZ9.all allDZZMZZZ) = true := by decide +kernel

/-- Chunk 10 of core ZZMZZZ: all rows pass. -/
theorem chkZZMZZZ10 : (rowsZZMZZZ10.all allDZZMZZZ) = true := by decide +kernel

/-- Every row of core ZZMZZZ passes the check. -/
theorem allOKZZMZZZ : ∀ ch ∈ rowsZZMZZZ, ∀ n ∈ ch, allDZZMZZZ n = true := by
  intro ch hch n hn
  simp only [rowsZZMZZZ, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZZMZZZ0 n hn
  · exact List.all_eq_true.mp chkZZMZZZ1 n hn
  · exact List.all_eq_true.mp chkZZMZZZ2 n hn
  · exact List.all_eq_true.mp chkZZMZZZ3 n hn
  · exact List.all_eq_true.mp chkZZMZZZ4 n hn
  · exact List.all_eq_true.mp chkZZMZZZ5 n hn
  · exact List.all_eq_true.mp chkZZMZZZ6 n hn
  · exact List.all_eq_true.mp chkZZMZZZ7 n hn
  · exact List.all_eq_true.mp chkZZMZZZ8 n hn
  · exact List.all_eq_true.mp chkZZMZZZ9 n hn
  · exact List.all_eq_true.mp chkZZMZZZ10 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core ZZMZZZ are true when the four class brackets have the signs `00-0`. -/
theorem unitsZZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h0 : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = 0) (h1 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0) (h3 : det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) = 0) :
    ∀ l ∈ unitsZZMZZZ, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  simp only [unitsZZMZZZ, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 2 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 2 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e2, e6, h0]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 0 1 3 4) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e0, e1, e3, e4, h1]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.br 2 3 4 6) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (false, V.ng (V.br 2 3 4 6)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e2, e3, e4, e6, h3]
  · show evalL (Minimality.H16.SAT.rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, Minimality.H16.SAT.rho, Minimality.H16.SAT.Geo.atom, e1, e2, e3, e4, h2]


/-- The case clause of core ZZMZZZ holds when some of the 18 shape entries of `Z` is nonzero (`¬ ZShape16 x F`). -/
theorem clauseZZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h : ¬ ZShape16 x F) : HoldsW (rhoW (geoF F)) clauseZZMZZZ := by
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
    refine hc (holdsW_atom_ne (a := V.lv 0 1 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 9 17) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 1 10 16) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 0 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 4) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 4 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 0 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 5 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 2 3 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 6 1 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 5 1 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.nv 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clauseZZMZZZ]) (by simp [clauseZZMZZZ]) ?_)
    simpa [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n5, n6] using hne

/-- The second case clause of core ZZMZZZ holds when some of the `sigma16` images of the 18 shape entries of `Z` is nonzero
(`¬ ZShape16 (x ∘ sigma16) (sigFac F)`). -/
theorem clause2ZZMZZZ_true (F : S0xFac 8 V2.fIdx x) (h : ¬ ZShape16 (x ∘ sigma16) (sigFac F)) : HoldsW (rhoW (geoF F)) clause2ZZMZZZ := by
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
    refine hc (holdsW_atom_ne (a := V.lv 2 5 6 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 2 5 6 0 3) = det3 (x 5 - x 2) (x 6 - x 2) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 6) (x 5 - x 6) (x 3 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 2 6 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 2 6 3 5) = det3 (x 2 - x 0) (x 6 - x 0) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 6) (x 0 - x 6) (x 3 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 0 2 13) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.kv 0 2 13) = det3 (x 0 - x 3) (x 2 - x 5) (F.N 0) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 5) (x 3 - x 0) (F.N 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.kv 0 1 16) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.kv 0 1 16) = det3 (x 0 - x 2) (x 3 - x 5) (F.N 0) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 2 - x 0) (x 3 - x 5) (F.N 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 1 0 2) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 1 0 2) = inner ℝ (F.N 1) (x 0 - x 2) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 1) (x 2 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 2 4) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 2 4) = inner ℝ (F.N 3) (x 2 - x 4) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 2 - x 4) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 2 5) = inner ℝ (F.N 3) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 2 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 3 4 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 3 4 5) = inner ℝ (F.N 3) (x 4 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 3) (x 4 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 3 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 3 6) = inner ℝ (F.N 7) (x 3 - x 6) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 6 - x 3) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 0 6) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 0 6) = inner ℝ (F.N 7) (x 0 - x 6) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 6 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 1 2 5 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 1 2 5 0 3) = det3 (x 2 - x 1) (x 5 - x 1) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 1 - x 2) (x 5 - x 2) (x 3 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 1 2 3 5) = det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 1 - x 2) (x 0 - x 2) (x 3 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 7 0 3) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 7 0 3) = inner ℝ (F.N 7) (x 0 - x 3) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 7) (x 3 - x 0) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.fv 2 3 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.fv 2 3 5) = inner ℝ (F.N 2) (x 3 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show inner ℝ (F.N 2) (x 3 - x 5) = 0
    (simp only [inner_sub_right] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 1 3 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 1 3 2 5) = det3 (x 1 - x 0) (x 3 - x 0) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 3 - x 1) (x 0 - x 1) (x 2 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 0 3 4 2 5) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 0 3 4 2 5) = det3 (x 3 - x 0) (x 4 - x 0) (x 2 - x 5) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 4 - x 3) (x 0 - x 3) (x 2 - x 5) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.lv 3 4 5 0 2) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.lv 3 4 5 0 2) = det3 (x 4 - x 3) (x 5 - x 3) (x 0 - x 2) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (x 4 - x 3) (x 5 - x 3) (x 2 - x 0) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)
  · by_contra hne
    refine hc (holdsW_atom_ne (a := V.nv 3 6 7) (by simp [Minimality.H16.SAT.rho]) (by simp [clause2ZZMZZZ]) (by simp [clause2ZZMZZZ]) ?_)
    intro h0
    apply hne
    have ha : (geoF F).atom (V.nv 3 6 7) = det3 (F.N 3) (F.N 6) (F.N 7) := by
      simp [Minimality.H16.SAT.Geo.atom, Minimality.H16.SAT.Geo.dv, Minimality.H16.SAT.EA, Minimality.H16.SAT.EB, Minimality.H16.SAT.edges, e0, e1, e2, e3, e4, e5, e6, n0, n1, n2, n3, n4, n5, n6, n7]
    rw [ha] at h0
    show det3 (F.N 6) (F.N 3) (F.N 7) = 0
    (simp only [det3_expand, PiLp.sub_apply] at h0 ⊢; linear_combination (-1) * h0)

/-- **Core ZZMZZZ gives Rupert**, from the unsatisfiability of its numbered clauses: in the shape of `Core16ZZW`. -/
theorem rupert_of_core_dataZZMZZZ (hU : CoreUnsat rowsZZMZZZ) : Core16ZZW 0 0 (-1) 0 := by
  intro y F hC h1 h2 h3 h4 hA hB
  exact caseSK2X_of_unsat chunksZZMZZZ rowsZZMZZZ unitsZZMZZZ clauseZZMZZZ clause2ZZMZZZ hU allOKZZMZZZ F hC
    (unitsZZMZZZ_true F (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)
      (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith) (by simp only [br16, SgnP] at h1 h2 h3 h4; norm_num at h1 h2 h3 h4; linarith)) (clauseZZMZZZ_true F hA) (clause2ZZMZZZ_true F hB)

end Minimality.H16K.SAT
