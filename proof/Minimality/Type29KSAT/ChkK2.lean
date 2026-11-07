module

public import Minimality.Type29KSAT.DataK2
public import Minimality.Type29KSAT.KDec
public import Minimality.Type29KSAT.NfK2

@[expose] public section

/-!
# L29T, T11: core K2, the kernel checks of all rows (dispatcher `rowK`, class literals `unitsK2` and class clause `clauseK2`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- The row check of core K2. -/
def allDK2 (n : Nat) : Bool := rowK unitsK2 clauseK2 chunksK2 n

/-- Chunk 0 of core K2: all rows pass. -/
theorem chkK20 : (rowsK20.all allDK2) = true := by decide +kernel

/-- Chunk 1 of core K2: all rows pass. -/
theorem chkK21 : (rowsK21.all allDK2) = true := by decide +kernel

/-- Chunk 2 of core K2: all rows pass. -/
theorem chkK22 : (rowsK22.all allDK2) = true := by decide +kernel

/-- Chunk 3 of core K2: all rows pass. -/
theorem chkK23 : (rowsK23.all allDK2) = true := by decide +kernel

/-- Chunk 4 of core K2: all rows pass. -/
theorem chkK24 : (rowsK24.all allDK2) = true := by decide +kernel

/-- Chunk 5 of core K2: all rows pass. -/
theorem chkK25 : (rowsK25.all allDK2) = true := by decide +kernel

/-- Chunk 6 of core K2: all rows pass. -/
theorem chkK26 : (rowsK26.all allDK2) = true := by decide +kernel

/-- Chunk 7 of core K2: all rows pass. -/
theorem chkK27 : (rowsK27.all allDK2) = true := by decide +kernel

/-- Chunk 8 of core K2: all rows pass. -/
theorem chkK28 : (rowsK28.all allDK2) = true := by decide +kernel

/-- Chunk 9 of core K2: all rows pass. -/
theorem chkK29 : (rowsK29.all allDK2) = true := by decide +kernel

/-- Chunk 10 of core K2: all rows pass. -/
theorem chkK210 : (rowsK210.all allDK2) = true := by decide +kernel

/-- Chunk 11 of core K2: all rows pass. -/
theorem chkK211 : (rowsK211.all allDK2) = true := by decide +kernel

/-- Chunk 12 of core K2: all rows pass. -/
theorem chkK212 : (rowsK212.all allDK2) = true := by decide +kernel

/-- Every row of core K2 passes the check. -/
theorem allOKK2 : ∀ ch ∈ rowsK2, ∀ n ∈ ch, allDK2 n = true := by
  intro ch hch n hn
  simp only [rowsK2, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkK20 n hn
  · exact List.all_eq_true.mp chkK21 n hn
  · exact List.all_eq_true.mp chkK22 n hn
  · exact List.all_eq_true.mp chkK23 n hn
  · exact List.all_eq_true.mp chkK24 n hn
  · exact List.all_eq_true.mp chkK25 n hn
  · exact List.all_eq_true.mp chkK26 n hn
  · exact List.all_eq_true.mp chkK27 n hn
  · exact List.all_eq_true.mp chkK28 n hn
  · exact List.all_eq_true.mp chkK29 n hn
  · exact List.all_eq_true.mp chkK210 n hn
  · exact List.all_eq_true.mp chkK211 n hn
  · exact List.all_eq_true.mp chkK212 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core K2 are true when the brackets `[0134] [0245] [1235]` are negative. -/
theorem unitsK2_true (F : S0xFac 9 s0x_S29 x) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0) :
    ∀ l ∈ unitsK2, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  simp only [unitsK2, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 2 4 5)) = true
    simp [evalL, rho, Geo.atom, e0, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 5)) = true
    simp [evalL, rho, Geo.atom, e1, e2, e3, e5, h2]

/-- A nonzero atom makes its negated zero gate true. -/
theorem gateNZ (g : Geo) (v : V) (hv : rho g v = decide (0 < g.atom v)) (h : g.atom v ≠ 0) :
    evalL (rho g) (false, V.gate false v false (V.ng v)) = true := by
  rcases lt_or_gt_of_ne h with h | h <;> simp [evalL, rho, hv, h, not_lt.mpr, h.le]

/-- The class clause of core K2 holds when the three atoms are not all zero. -/
theorem clauseK2_true (F : S0xFac 9 s0x_S29 x) (h : K2NZ F) : HoldsW (rhoW (geoF F)) clauseK2 := by
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have n5 : (geoF F).N 5 = F.N 5 := geoF_N F 5
  have n1 : (geoF F).N 1 = F.N 1 := geoF_N F 1
  have d8 : (geoF F).dv 8 = x 1 - x 4 := by simp [Geo.dv, EA, EB, edges, e1, e4]
  have d20 : (geoF F).dv 20 = x 5 - x 6 := by simp [Geo.dv, EA, EB, edges, e5, e6]
  have d9 : (geoF F).dv 9 = x 1 - x 5 := by simp [Geo.dv, EA, EB, edges, e1, e5]
  have d19 : (geoF F).dv 19 = x 4 - x 6 := by simp [Geo.dv, EA, EB, edges, e4, e6]
  unfold K2NZ at h
  by_cases a1 : det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0
  · by_cases a2 : det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0
    · have a3 : ⟪F.N 1, x 3 - x 4⟫ ≠ 0 := fun h3 => h ⟨a1, a2, h3⟩
      refine ⟨(false, W.base (V.gate false (V.fv 1 3 4) false (V.ng (V.fv 1 3 4)))), by simp [clauseK2], ?_⟩
      show evalL (rho (geoF F)) (false, V.gate false (V.fv 1 3 4) false (V.ng (V.fv 1 3 4))) = true
      exact gateNZ _ _ (by simp [rho, Geo.atom, e3, e4, n1]) (by simpa [Geo.atom, e3, e4, n1] using a3)
    · refine ⟨(false, W.base (V.gate false (V.kv 5 9 19) false (V.ng (V.kv 5 9 19)))), by simp [clauseK2], ?_⟩
      show evalL (rho (geoF F)) (false, V.gate false (V.kv 5 9 19) false (V.ng (V.kv 5 9 19))) = true
      exact gateNZ _ _ (by simp [rho, Geo.atom, d9, d19, n5]) (by simpa [Geo.atom, d9, d19, n5] using a2)
  · refine ⟨(false, W.base (V.gate false (V.kv 5 8 20) false (V.ng (V.kv 5 8 20)))), by simp [clauseK2], ?_⟩
    show evalL (rho (geoF F)) (false, V.gate false (V.kv 5 8 20) false (V.ng (V.kv 5 8 20))) = true
    exact gateNZ _ _ (by simp [rho, Geo.atom, d8, d20, n5]) (by simpa [Geo.atom, d8, d20, n5] using a1)

/-- **Core K2 gives Rupert**: if the numbered clauses of core K2 are unsatisfiable, every type 29 shape with `0 < [0123]`,
`[0134] < 0`, `[0245] < 0`, `[1235] < 0` and the three atoms of the class clause not all zero is Rupert. -/
theorem rupert_of_coreK2 (hU : CoreUnsat rowsK2) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hZ : K2NZ F) : IsRupert (univ.image x) :=
  caseK_of_unsat chunksK2 rowsK2 unitsK2 clauseK2 hU allOKK2 F hchir (unitsK2_true F h0 h1 h2) (clauseK2_true F hZ)

end Minimality.H29K.SAT
