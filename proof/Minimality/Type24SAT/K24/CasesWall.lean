module

public import Minimality.Type24SAT.K24.CasesSplit
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

/-!
# Type 24, the double wall `25 // 46`, `z0 = z3 = z4 = z5`: class units of the SAT cores

The wall (ZSTRATA24 section 6.z, DOUBLEWALL.md): the edges `x2 - x5` and `x4 - x6` are parallel and the four vertices
`0, 3, 4, 5` have the same depth along `d = x2 - x5`.  The cores use the wall only through nine literals, all of them
zero tests, so the Final theorems take the wall as one hypothesis `WallHyp` listing exactly these zeros:
the entries `E:25`, `G:46`, `I:25` (inner products of a facet normal with an edge), the brackets `L125;46`, `L146;25`
(`x2 - x5` and `x4 - x6` lie in the plane of `x1, x2, x5`, resp. `x1, x4, x6`), and the tie entries
`T(d05, d25)`, `T(d25, d35)` (the depths of `x0`, `x3` against `x5` along `d`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

variable {x : Fin 7 → ℝ³}

/-- The wall zeros used by the cores of the double wall classes. -/
def WallHyp (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 4, x 2 - x 5⟫ = 0 ∧ ⟪F.N 6, x 4 - x 6⟫ = 0 ∧ ⟪F.N 8, x 2 - x 5⟫ = 0 ∧
  det3 (x 2 - x 1) (x 5 - x 1) (x 4 - x 6) = 0 ∧ det3 (x 4 - x 1) (x 6 - x 1) (x 2 - x 5) = 0 ∧
  ⟪x 0 - x 5, x 2 - x 5⟫ = 0 ∧ ⟪x 2 - x 5, x 3 - x 5⟫ = 0

open V W in
/-- The nine wall literals: zero gates of `E:25 G:46 I:25 L125;46 L146;25` and `T(d05,d25) = 0`, `T(d25,d35) = 0`. -/
def unitsWall : List LitW :=
  [(true, base (gate false (fv 4 2 5) false (ng (fv 4 2 5)))), (true, base (gate false (fv 6 4 6) false (ng (fv 6 4 6)))),
   (true, base (gate false (fv 8 2 5) false (ng (fv 8 2 5)))),
   (true, base (gate false (lv 1 2 5 4 6) false (ng (lv 1 2 5 4 6)))),
   (true, base (gate false (lv 1 4 6 2 5) false (ng (lv 1 4 6 2 5)))),
   (false, base (tp 4 13)), (false, base (tq 4 13)), (false, base (tp 13 16)), (false, base (tq 13 16))]

/-- The wall literals hold on a wall. -/
theorem unitsWall_true (F : S0xFac 9 s0x_S24 x) (hW : WallHyp F) :
    ∀ l ∈ unitsWall, evalW (rhoW (geoF F)) l = true := by
  obtain ⟨hE, hG, hI, hL1, hL2, hT1, hT2⟩ := hW
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have n4 : (geoF F).N 4 = F.N 4 := geoF_N F 4
  have n6 : (geoF F).N 6 = F.N 6 := geoF_N F 6
  have n8 : (geoF F).N 8 = F.N 8 := geoF_N F 8
  have v4 : (geoF F).vv 4 = x 0 - x 5 := by
    simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e0, e5]
  have v13 : (geoF F).vv 13 = x 2 - x 5 := by
    simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e2, e5]
  have v16 : (geoF F).vv 16 = x 3 - x 5 := by
    simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e3, e5]
  have h2 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := hT2
  intro l hl
  simp only [unitsWall, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by simp [H24.SAT.Geo.atom, e2, e5, n4, hE])
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by simp [H24.SAT.Geo.atom, e4, e6, n6, hG])
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by simp [H24.SAT.Geo.atom, e2, e5, n8, hI])
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by simp [H24.SAT.Geo.atom, e1, e2, e4, e5, e6, hL1])
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by simp [H24.SAT.Geo.atom, e1, e2, e4, e5, e6, hL2])
  · simp [evalW, rhoW_base, H24.SAT.rho, v4, v13, hT1]
  · simp [evalW, rhoW_base, H24.SAT.rho, v4, v13, hT1]
  · simp [evalW, rhoW_base, H24.SAT.rho, v13, v16, h2]
  · simp [evalW, rhoW_base, H24.SAT.rho, v13, v16, h2]

/-- The wall hypotheses are preserved by the mirror. -/
theorem wall_mir (F : S0xFac 9 s0x_S24 x) (hW : WallHyp F) :
    ⟪(mirFac F).N 4, mir (x 2) - mir (x 5)⟫ = 0 ∧ ⟪(mirFac F).N 6, mir (x 4) - mir (x 6)⟫ = 0 ∧
    ⟪(mirFac F).N 8, mir (x 2) - mir (x 5)⟫ = 0 ∧
    det3 (mir (x 2) - mir (x 1)) (mir (x 5) - mir (x 1)) (mir (x 4) - mir (x 6)) = 0 ∧
    det3 (mir (x 4) - mir (x 1)) (mir (x 6) - mir (x 1)) (mir (x 2) - mir (x 5)) = 0 ∧
    ⟪mir (x 0) - mir (x 5), mir (x 2) - mir (x 5)⟫ = 0 ∧ ⟪mir (x 2) - mir (x 5), mir (x 3) - mir (x 5)⟫ = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hW
  simp only [mirFac, ← mir_sub, mir_inner, mir_det3, neg_eq_zero]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Minimality.H24K.SAT
