module

public import Minimality.Type24SAT.K24.CornerOB1
public import Minimality.Type24SAT.K24.KDecs

@[expose] public section

/-!
# Type 24, off `OB1`, the parallelogram split: class units and class clauses of the two cases

The quad facet `D = {0, 3, 4, 5}` (cyclic order `0 4 3 5`) has the opposite side pairs `x0 - x4`, `x3 - x5` and `x0 - x5`,
`x3 - x4`.  The atoms `KD0435 = kv 3 3 16` and `KD0534 = kv 3 4 15` are `det3 (x0 - x4) (x3 - x5) (N_D)` and
`det3 (x0 - x5) (x3 - x4) (N_D)`, `N_D = F.N 3` the normal of `D`; both vanish exactly when `D` is a parallelogram.
Case `notP`: they do not both vanish (`clauseNotP`).  Case `Pq`: both vanish (the two zero gates `unitsZ`) and neither the
facet pair `E = 046`, `G = 235` (`E:23`, `E:25`: `N_E` is not orthogonal to `G`) nor `C = 025`, `I = 346`
(`C:36`, `C:46`) is parallel (`clauseEG`, `clauseCI`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

variable {x : Fin 7 → ℝ³}

open V W in
/-- Some `KD` atom is nonzero: `KD0435+ KD0435- KD0534+ KD0534-`. -/
def clauseNotP : List LitW :=
  [(true, base (kv 3 3 16)), (true, base (ng (kv 3 3 16))), (true, base (kv 3 4 15)), (true, base (ng (kv 3 4 15)))]

open V W in
/-- `N_E` is not orthogonal to the plane of `G`: `E:23+ E:23- E:25+ E:25-`. -/
def clauseEG : List LitW :=
  [(true, base (fv 4 2 3)), (true, base (ng (fv 4 2 3))), (true, base (fv 4 2 5)), (true, base (ng (fv 4 2 5)))]

open V W in
/-- `N_C` is not orthogonal to the plane of `I`: `C:36+ C:36- C:46+ C:46-`. -/
def clauseCI : List LitW :=
  [(true, base (fv 2 3 6)), (true, base (ng (fv 2 3 6))), (true, base (fv 2 4 6)), (true, base (ng (fv 2 4 6)))]

open V W in
/-- The zero gates of `KD0435` and `KD0534`. -/
def unitsZ : List LitW :=
  [(true, base (gate false (kv 3 3 16) false (ng (kv 3 3 16)))), (true, base (gate false (kv 3 4 15) false (ng (kv 3 4 15))))]

/-- The class clauses of case `notP`. -/
def clausesNotP : List (List LitW) := [clauseNotP, clauseOB1]
/-- The class clauses of case `Pq`. -/
def clausesPq : List (List LitW) := [clauseEG, clauseCI, clauseOB1]

/-- A nonzero atom makes one of its two sign literals true. -/
theorem holds_pm (g : H24.SAT.Geo) (v : V) (h : g.atom v ≠ 0) (hv : H24.SAT.rho g v = decide (0 < g.atom v)) :
    evalL (H24.SAT.rho g) (true, v) = true ∨ evalL (H24.SAT.rho g) (true, V.ng v) = true := by
  rcases lt_or_gt_of_ne h with h | h
  · right; simp [evalL, H24.SAT.rho, h]
  · left; simp [evalL, hv, h]

/-- A vanishing atom makes its zero gate true. -/
theorem gateZ (g : H24.SAT.Geo) (v : V) (hv : H24.SAT.rho g v = decide (0 < g.atom v)) (h : g.atom v = 0) :
    evalL (H24.SAT.rho g) (true, V.gate false v false (V.ng v)) = true := by
  simp [evalL, H24.SAT.rho, hv, h]

theorem atom_KD1 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.kv 3 3 16) = det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have n3 : (geoF F).N 3 = F.N 3 := geoF_N F 3
  simp [H24.SAT.Geo.atom, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e0, e3, e4, e5, n3]

theorem atom_KD2 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.kv 3 4 15) = det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have n3 : (geoF F).N 3 = F.N 3 := geoF_N F 3
  simp [H24.SAT.Geo.atom, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e0, e3, e4, e5, n3]

theorem atom_fv423 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.fv 4 2 3) = ⟪F.N 4, x 2 - x 3⟫ := by
  have ep : (geoF F).x 2 = x 2 := geoF_x F 2
  have eq : (geoF F).x 3 = x 3 := geoF_x F 3
  have n : (geoF F).N 4 = F.N 4 := geoF_N F 4
  simp [H24.SAT.Geo.atom, ep, eq, n]

theorem atom_fv425 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.fv 4 2 5) = ⟪F.N 4, x 2 - x 5⟫ := by
  have ep : (geoF F).x 2 = x 2 := geoF_x F 2
  have eq : (geoF F).x 5 = x 5 := geoF_x F 5
  have n : (geoF F).N 4 = F.N 4 := geoF_N F 4
  simp [H24.SAT.Geo.atom, ep, eq, n]

theorem atom_fv236 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.fv 2 3 6) = ⟪F.N 2, x 3 - x 6⟫ := by
  have ep : (geoF F).x 3 = x 3 := geoF_x F 3
  have eq : (geoF F).x 6 = x 6 := geoF_x F 6
  have n : (geoF F).N 2 = F.N 2 := geoF_N F 2
  simp [H24.SAT.Geo.atom, ep, eq, n]

theorem atom_fv246 (F : S0xFac 9 s0x_S24 x) :
    (geoF F).atom (V.fv 2 4 6) = ⟪F.N 2, x 4 - x 6⟫ := by
  have ep : (geoF F).x 4 = x 4 := geoF_x F 4
  have eq : (geoF F).x 6 = x 6 := geoF_x F 6
  have n : (geoF F).N 2 = F.N 2 := geoF_N F 2
  simp [H24.SAT.Geo.atom, ep, eq, n]

/-- The zero gates of the two `KD` atoms hold when `D` is a parallelogram. -/
theorem unitsZ_true (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0) :
    ∀ l ∈ unitsZ, evalW (rhoW (geoF F)) l = true := by
  intro l hl
  simp only [unitsZ, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by rw [atom_KD1]; exact hD.1)
  · exact gateZ _ _ (by simp [H24.SAT.rho]) (by rw [atom_KD2]; exact hD.2)

/-- Case `notP`: `D` is not a parallelogram. -/
theorem clausesNotP_true (F : S0xFac 9 s0x_S24 x) (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) :
    ∀ C ∈ clausesNotP, HoldsW (rhoW (geoF F)) C := by
  intro C hC
  simp only [clausesNotP, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · have : (geoF F).atom (V.kv 3 3 16) ≠ 0 ∨ (geoF F).atom (V.kv 3 4 15) ≠ 0 := by
      rw [atom_KD1, atom_KD2]; by_contra hc; push_neg at hc; exact hP hc
    rcases this with h | h
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_self .., h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h'⟩
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), h'⟩
  · exact clauseOB1_true F hO

/-- Case `Pq`: neither `E ∥ G` nor `C ∥ I`. -/
theorem clausesPq_true (F : S0xFac 9 s0x_S24 x) (hO : ¬ OB1 x)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) :
    ∀ C ∈ clausesPq, HoldsW (rhoW (geoF F)) C := by
  intro C hC
  simp only [clausesPq, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl
  · have a1 := atom_fv423 F
    have a2 := atom_fv425 F
    have : (geoF F).atom (V.fv 4 2 3) ≠ 0 ∨ (geoF F).atom (V.fv 4 2 5) ≠ 0 := by
      rw [a1, a2]; by_contra hc; push_neg at hc; exact hEG hc
    rcases this with h | h
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_self .., h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h'⟩
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), h'⟩
  · have a1 := atom_fv236 F
    have a2 := atom_fv246 F
    have : (geoF F).atom (V.fv 2 3 6) ≠ 0 ∨ (geoF F).atom (V.fv 2 4 6) ≠ 0 := by
      rw [a1, a2]; by_contra hc; push_neg at hc; exact hCI hc
    rcases this with h | h
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_self .., h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h'⟩
    · rcases holds_pm (geoF F) _ h (by simp [H24.SAT.rho]) with h' | h'
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h'⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), h'⟩
  · exact clauseOB1_true F hO

/-- The case hypotheses of `notP` are preserved by the mirror. -/
theorem notP_mir (F : S0xFac 9 s0x_S24 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) :
    ¬ (det3 (mir (x 0) - mir (x 4)) (mir (x 3) - mir (x 5)) ((mirFac F).N 3) = 0 ∧
      det3 (mir (x 0) - mir (x 5)) (mir (x 3) - mir (x 4)) ((mirFac F).N 3) = 0) := by
  simp only [mirFac, ← mir_sub, mir_det3, neg_eq_zero]
  exact hP

/-- `D` a parallelogram is preserved by the mirror. -/
theorem hD_mir (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0) :
    det3 (mir (x 0) - mir (x 4)) (mir (x 3) - mir (x 5)) ((mirFac F).N 3) = 0 ∧
      det3 (mir (x 0) - mir (x 5)) (mir (x 3) - mir (x 4)) ((mirFac F).N 3) = 0 := by
  simp only [mirFac, ← mir_sub, mir_det3, neg_eq_zero]
  exact hD

/-- The `E`, `G` and `C`, `I` hypotheses of `Pq` are preserved by the mirror. -/
theorem pq_mir (F : S0xFac 9 s0x_S24 x)
    (hEG : ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0))
    (hCI : ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)) :
    ¬ (⟪(mirFac F).N 4, mir (x 2) - mir (x 3)⟫ = 0 ∧ ⟪(mirFac F).N 4, mir (x 2) - mir (x 5)⟫ = 0) ∧
    ¬ (⟪(mirFac F).N 2, mir (x 3) - mir (x 6)⟫ = 0 ∧ ⟪(mirFac F).N 2, mir (x 4) - mir (x 6)⟫ = 0) := by
  simp only [mirFac, ← mir_sub, mir_inner]
  exact ⟨hEG, hCI⟩

end Minimality.H24K.SAT
