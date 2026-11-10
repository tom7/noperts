module

public import Minimality.Type29KSAT.DataZA
public import Minimality.Type29KSAT.KDec
public import Minimality.Type29KSAT.NfZA

@[expose] public section

/-!
# Type 29, K2a on `Z1`, case A: core ZA, the kernel checks of all rows (dispatcher `rowK`, class literals `unitsZA` and case clause `clauseZA`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- The row check of core ZA. -/
def allDZA (n : Nat) : Bool := rowK unitsZA clauseZA chunksZA n

/-- Chunk 0 of core ZA: all rows pass. -/
theorem chkZA0 : (rowsZA0.all allDZA) = true := by decide +kernel

/-- Chunk 1 of core ZA: all rows pass. -/
theorem chkZA1 : (rowsZA1.all allDZA) = true := by decide +kernel

/-- Chunk 2 of core ZA: all rows pass. -/
theorem chkZA2 : (rowsZA2.all allDZA) = true := by decide +kernel

/-- Every row of core ZA passes the check. -/
theorem allOKZA : ∀ ch ∈ rowsZA, ∀ n ∈ ch, allDZA n = true := by
  intro ch hch n hn
  simp only [rowsZA, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl
  · exact List.all_eq_true.mp chkZA0 n hn
  · exact List.all_eq_true.mp chkZA1 n hn
  · exact List.all_eq_true.mp chkZA2 n hn

variable {x : Fin 7 → ℝ³}

/-- A vanishing atom makes its zero gate true. -/
theorem gateZ (g : Geo) (v : V) (hv : rho g v = decide (0 < g.atom v)) (h : g.atom v = 0) :
    evalL (rho g) (true, V.gate false v false (V.ng v)) = true := by
  simp [evalL, rho, hv, h]

/-- The class literals of core ZA are true when the brackets `[0134] [0245] [1235]` are negative and the three atoms
`KF1456`, `KF1546`, `B:34` vanish. -/
theorem unitsZA_true (F : S0xFac 9 s0x_S29 x) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hz : det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0) :
    ∀ l ∈ unitsZA, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
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
  simp only [unitsZA, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 2 4 5)) = true
    simp [evalL, rho, Geo.atom, e0, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 5)) = true
    simp [evalL, rho, Geo.atom, e1, e2, e3, e5, h2]
  · show evalL (rho (geoF F)) (true, V.gate false (V.kv 5 8 20) false (V.ng (V.kv 5 8 20))) = true
    exact gateZ _ _ (by simp [rho, Geo.atom, d8, d20, n5]) (by simpa [Geo.atom, d8, d20, n5] using hz.1)
  · show evalL (rho (geoF F)) (true, V.gate false (V.kv 5 9 19) false (V.ng (V.kv 5 9 19))) = true
    exact gateZ _ _ (by simp [rho, Geo.atom, d9, d19, n5]) (by simpa [Geo.atom, d9, d19, n5] using hz.2.1)
  · show evalL (rho (geoF F)) (true, V.gate false (V.fv 1 3 4) false (V.ng (V.fv 1 3 4))) = true
    exact gateZ _ _ (by simp [rho, Geo.atom, e3, e4, n1]) (by simpa [Geo.atom, e3, e4, n1] using hz.2.2)

/-- The case clause of core ZA holds when `x1 - x4` is not orthogonal to both `x0 - x1` and `x0 - x5`. -/
theorem clauseZA_true (F : S0xFac 9 s0x_S29 x) (h : CaseA x) : HoldsW (rhoW (geoF F)) clauseZA := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have v0 : (geoF F).vv 0 = x 0 - x 1 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e1]
  have v4 : (geoF F).vv 4 = x 0 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e5]
  have v8 : (geoF F).vv 8 = x 1 - x 4 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e1, e4]
  rcases h with h | h
  · have h : ⟪x 0 - x 1, x 1 - x 4⟫ ≠ 0 := by rw [real_inner_comm]; exact h
    rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 0 8)), by simp [clauseZA], ?_⟩
      show evalL (rho (geoF F)) (true, V.tq 0 8) = true
      simpa [evalL, rho, v0, v8] using h
    · refine ⟨(true, W.base (V.tp 0 8)), by simp [clauseZA], ?_⟩
      show evalL (rho (geoF F)) (true, V.tp 0 8) = true
      simpa [evalL, rho, v0, v8] using h
  · have h : ⟪x 0 - x 5, x 1 - x 4⟫ ≠ 0 := by rw [real_inner_comm]; exact h
    rcases lt_or_gt_of_ne h with h | h
    · refine ⟨(true, W.base (V.tq 4 8)), by simp [clauseZA], ?_⟩
      show evalL (rho (geoF F)) (true, V.tq 4 8) = true
      simpa [evalL, rho, v4, v8] using h
    · refine ⟨(true, W.base (V.tp 4 8)), by simp [clauseZA], ?_⟩
      show evalL (rho (geoF F)) (true, V.tp 4 8) = true
      simpa [evalL, rho, v4, v8] using h

/-- **Core ZA gives Rupert**: if the numbered clauses of core ZA are unsatisfiable, every type 29 shape with `0 < [0123]`,
`[0134] < 0`, `[0245] < 0`, `[1235] < 0`, the atoms `KF1456`, `KF1546`, `B:34` zero and `CaseA` is Rupert. -/
theorem rupert_of_coreZA (hU : CoreUnsat rowsZA) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hz : det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0)
    (hA : CaseA x) : IsRupert (univ.image x) :=
  caseK_of_unsat chunksZA rowsZA unitsZA clauseZA hU allOKZA F hchir (unitsZA_true F h0 h1 h2 hz) (clauseZA_true F hA)

end Minimality.H29K.SAT
