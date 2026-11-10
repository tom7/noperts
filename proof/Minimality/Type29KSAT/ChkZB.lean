module

public import Minimality.Type29KSAT.DataZB
public import Minimality.Type29KSAT.NfZB

@[expose] public section

/-!
# Type 29, K2a on `Z1`, case B residue: core ZB, the kernel checks of all rows (dispatcher `rowKs`, class literals
`unitsZB` and the two residue clauses `clausesZB`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- The row check of core ZB. -/
def allDZB (n : Nat) : Bool := rowKs unitsZB clausesZB chunksZB n

/-- Chunk 0 of core ZB: all rows pass. -/
theorem chkZB0 : (rowsZB0.all allDZB) = true := by decide +kernel

/-- Chunk 1 of core ZB: all rows pass. -/
theorem chkZB1 : (rowsZB1.all allDZB) = true := by decide +kernel

/-- Every row of core ZB passes the check. -/
theorem allOKZB : ∀ ch ∈ rowsZB, ∀ n ∈ ch, allDZB n = true := by
  intro ch hch n hn
  simp only [rowsZB, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl
  · exact List.all_eq_true.mp chkZB0 n hn
  · exact List.all_eq_true.mp chkZB1 n hn

variable {x : Fin 7 → ℝ³}

/-- A vanishing atom makes its zero gate true. -/
theorem gateZB (g : Geo) (v : V) (hv : rho g v = decide (0 < g.atom v)) (h : g.atom v = 0) :
    evalL (rho g) (true, V.gate false v false (V.ng v)) = true := by
  simp [evalL, rho, hv, h]

/-- The class literals of core ZB are true when the brackets `[0134] [0245] [1235]` are negative, the three atoms
`KF1456`, `KF1546`, `B:34` vanish, and `x1 - x4` is orthogonal to `x0 - x1` and `x0 - x5` (case B). -/
theorem unitsZB_true (F : S0xFac 9 s0x_S29 x) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hz : det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0) (hB : CaseB x) :
    ∀ l ∈ unitsZB, evalW (rhoW (geoF F)) l = true := by
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
  have v0 : (geoF F).vv 0 = x 0 - x 1 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e1]
  have v4 : (geoF F).vv 4 = x 0 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e5]
  have v8 : (geoF F).vv 8 = x 1 - x 4 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e1, e4]
  have b0 : ⟪x 0 - x 1, x 1 - x 4⟫ = 0 := by rw [real_inner_comm]; exact hB.1
  have b4 : ⟪x 0 - x 5, x 1 - x 4⟫ = 0 := by rw [real_inner_comm]; exact hB.2
  simp only [unitsZB, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 1 3 4)) = true
    simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 2 4 5)) = true
    simp [evalL, rho, Geo.atom, e0, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 5)) = true
    simp [evalL, rho, Geo.atom, e1, e2, e3, e5, h2]
  · show evalL (rho (geoF F)) (true, V.gate false (V.kv 5 8 20) false (V.ng (V.kv 5 8 20))) = true
    exact gateZB _ _ (by simp [rho, Geo.atom, d8, d20, n5]) (by simpa [Geo.atom, d8, d20, n5] using hz.1)
  · show evalL (rho (geoF F)) (true, V.gate false (V.kv 5 9 19) false (V.ng (V.kv 5 9 19))) = true
    exact gateZB _ _ (by simp [rho, Geo.atom, d9, d19, n5]) (by simpa [Geo.atom, d9, d19, n5] using hz.2.1)
  · show evalL (rho (geoF F)) (true, V.gate false (V.fv 1 3 4) false (V.ng (V.fv 1 3 4))) = true
    exact gateZB _ _ (by simp [rho, Geo.atom, e3, e4, n1]) (by simpa [Geo.atom, e3, e4, n1] using hz.2.2)
  · show evalL (rho (geoF F)) (false, V.tp 0 8) = true
    simp [evalL, rho, v0, v8, b0]
  · show evalL (rho (geoF F)) (false, V.tq 0 8) = true
    simp [evalL, rho, v0, v8, b0]
  · show evalL (rho (geoF F)) (false, V.tp 4 8) = true
    simp [evalL, rho, v4, v8, b4]
  · show evalL (rho (geoF F)) (false, V.tq 4 8) = true
    simp [evalL, rho, v4, v8, b4]

/-- The two residue clauses of core ZB hold under the residue hypothesis `CaseBRes` (overhang at both ends of `15`). -/
theorem clausesZB_true (F : S0xFac 9 s0x_S29 x) (h : CaseBRes x) :
    ∀ C ∈ clausesZB, HoldsW (rhoW (geoF F)) C := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have v0 : (geoF F).vv 0 = x 0 - x 1 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e1]
  have v4 : (geoF F).vv 4 = x 0 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e0, e5]
  have v6 : (geoF F).vv 6 = x 1 - x 2 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e1, e2]
  have v7 : (geoF F).vv 7 = x 1 - x 3 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e1, e3]
  have v9 : (geoF F).vv 9 = x 1 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e1, e5]
  have v13 : (geoF F).vv 13 = x 2 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e2, e5]
  have v16 : (geoF F).vv 16 = x 3 - x 5 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e3, e5]
  have neg2 : ∀ a b c d : ℝ³, ⟪a - b, c - d⟫ = ⟪b - a, d - c⟫ := by
    intro a b c d
    rw [← neg_sub b a, ← neg_sub d c, inner_neg_left, inner_neg_right, neg_neg]
  obtain ⟨⟨p, hp, hP⟩, ⟨q, hq, hQ⟩⟩ := h
  intro C hC
  simp only [clausesZB, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨(false, W.base (V.tq 0 9)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tq 0 9) = true
      have : ⟪x 0 - x 1, x 1 - x 5⟫ = -⟪x 0 - x 1, x 5 - x 1⟫ := by
        rw [← neg_sub (x 5) (x 1), inner_neg_right]
      have : ¬ ⟪x 0 - x 1, x 1 - x 5⟫ < 0 := by linarith
      simpa [evalL, rho, v0, v9] using this
    · refine ⟨(false, W.base (V.tp 6 9)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tp 6 9) = true
      have : ¬ 0 < ⟪x 1 - x 2, x 1 - x 5⟫ := by rw [neg2]; linarith
      simpa [evalL, rho, v6, v9] using this
    · refine ⟨(false, W.base (V.tp 7 9)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tp 7 9) = true
      have : ¬ 0 < ⟪x 1 - x 3, x 1 - x 5⟫ := by rw [neg2]; linarith
      simpa [evalL, rho, v7, v9] using this
  · simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · refine ⟨(false, W.base (V.tp 4 9)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tp 4 9) = true
      have : ¬ 0 < ⟪x 0 - x 5, x 1 - x 5⟫ := by linarith
      simpa [evalL, rho, v4, v9] using this
    · refine ⟨(false, W.base (V.tp 9 13)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tp 9 13) = true
      have : ¬ 0 < ⟪x 1 - x 5, x 2 - x 5⟫ := by rw [real_inner_comm]; linarith
      simpa [evalL, rho, v9, v13] using this
    · refine ⟨(false, W.base (V.tp 9 16)), by simp, ?_⟩
      show evalL (rho (geoF F)) (false, V.tp 9 16) = true
      have : ¬ 0 < ⟪x 1 - x 5, x 3 - x 5⟫ := by rw [real_inner_comm]; linarith
      simpa [evalL, rho, v9, v16] using this

/-- **Core ZB gives Rupert**: if the numbered clauses of core ZB are unsatisfiable, every type 29 shape with `0 < [0123]`,
`[0134] < 0`, `[0245] < 0`, `[1235] < 0`, the atoms `KF1456`, `KF1546`, `B:34` zero, `CaseB` and `CaseBRes` is Rupert. -/
theorem rupert_of_coreZB (hU : CoreUnsat rowsZB) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) < 0)
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hz : det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0)
    (hB : CaseB x) (hR : CaseBRes x) : IsRupert (univ.image x) :=
  caseKs_of_unsat chunksZB rowsZB unitsZB clausesZB hU allOKZB F hchir (unitsZB_true F h0 h1 h2 hz hB)
    (clausesZB_true F hR)

end Minimality.H29K.SAT
