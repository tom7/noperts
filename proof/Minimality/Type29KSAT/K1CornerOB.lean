module

public import Minimality.Type29KSAT.K1Corner

@[expose] public section

/-!
# Type 29, K1 off the obtuse corner: class literals and clause for the residue `¬OB6`

`OB6` says that all three face angles at vertex `6` are non-acute (`⟪x3 - x6, x4 - x6⟫ ≤ 0` and the two others).
Its negation says that one of them is acute, which is the clause `clausesOB` of the SAT core, with the three brackets
as units `unitsK1aB`.  `¬OB6` is invariant under the symmetry `σ = (0 2)(4 5)` and under the mirror.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K1
open Minimality.H29T.SAT

variable {x : Fin 7 → ℝ³}

/-- **The obtuse corner `OB6`**: all three face angles at vertex `6` are non-acute. -/
def OB6 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0 ∧ ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0

open V W in
/-- The bracket literals of class K1a: `[0134]+ [0245]- [1235]-`. -/
def unitsK1aB : List LitW :=
  [(true, base (br 0 1 3 4)), (true, base (ng (br 0 2 4 5))), (true, base (ng (br 1 2 3 5)))]

open V W in
/-- The OB6 clause: some face angle at vertex `6` is acute (`17 = 36`, `19 = 46`, `20 = 56`). -/
def clausesOB : List (List LitW) :=
  [[(true, base (tp 17 19)), (true, base (tp 17 20)), (true, base (tp 19 20))]]

/-- The bracket literals of K1a hold for `[0134] > 0`, `[0245] < 0`, `[1235] < 0`. -/
theorem unitsK1aB_true (F : S0xFac 9 s0x_S29 x) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0))
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0) :
    ∀ l ∈ unitsK1aB, evalW (rhoW (geoF F)) l = true := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  intro l hl
  simp only [unitsK1aB, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 2 4 5)) = true
    simp [evalL, rho, Geo.atom, e0, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 5)) = true
    simp [evalL, rho, Geo.atom, e1, e2, e3, e5, h2]

/-- The OB6 clause holds when one face angle at vertex `6` is acute. -/
theorem clausesOB_true (F : S0xFac 9 s0x_S29 x) (hO : ¬ OB6 x) :
    ∀ C ∈ clausesOB, HoldsW (rhoW (geoF F)) C := by
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v17 : (geoF F).vv 17 = x 3 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e3, e6]
  have v19 : (geoF F).vv 19 = x 4 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e4, e6]
  have v20 : (geoF F).vv 20 = x 5 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e5, e6]
  intro C hC
  simp only [clausesOB, List.mem_cons, List.not_mem_nil, or_false] at hC
  subst hC
  unfold OB6 at hO
  simp only [not_and_or, not_le] at hO
  rcases hO with h | h | h
  · exact ⟨_, List.mem_cons_self .., by simp [evalW, rhoW_base, rho, v17, v19, h]⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp [evalW, rhoW_base, rho, v17, v20, h]⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      by simp [evalW, rhoW_base, rho, v19, v20, h]⟩

theorem ob6_mir (hO : ¬ OB6 x) : ¬ OB6 (fun i => mir (x i)) := by
  intro h
  apply hO
  obtain ⟨z1, z2, z3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [← mir_sub, mir_inner] at z1 z2 z3 <;> assumption

/-- `¬OB6` is invariant under `σ = (0 2)(4 5)`, which fixes `3` and `6` and swaps `4` and `5`. -/
theorem ob6_sigma (hO : ¬ OB6 x) : ¬ OB6 (x ∘ sigma29) := by
  intro h
  apply hO
  obtain ⟨z1, z2, z3⟩ := h
  simp only [Function.comp_apply, sigma29] at z1 z2 z3
  refine ⟨?_, ?_, ?_⟩ <;> simp at z1 z2 z3
  · exact z2
  · exact z1
  · rw [real_inner_comm]; exact z3

/-- **K1a off `OB6` from the core theorem** (as `nf29_K1a_Z_of_core`). -/
theorem nf29_K1a_offOB_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³}, S0xFac 9 s0x_S29 y →
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      ¬ OB6 y → IsRupert (univ.image y))
    (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0) (hV : N.V < 0) (hO : ¬ OB6 x) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ (ob6_mir hO))
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0))
      rw [mir_br, i1]; have := mul_neg_of_neg_of_pos hD hb0; linarith
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) < 0
      rw [mir_br, i2]; have := mul_pos_of_neg_of_neg hD hV; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) < 0
      rw [mir_br, i3]; have := mul_pos_of_neg_of_neg hD ha2; linarith
  · exact hcore F (by rw [i0]; exact mul_pos hD hDD) (by rw [i1]; exact mul_pos hD hb0)
      (by rw [i2]; exact mul_neg_of_pos_of_neg hD hV) (by rw [i3]; exact mul_neg_of_pos_of_neg hD ha2) hO

/-- **K1 off `OB6` from the K1a core theorem**: K1b is the `σ`-image of K1a. -/
theorem nf29_K1_offOB_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³}, S0xFac 9 s0x_S29 y →
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      ¬ OB6 y → IsRupert (univ.image y))
    (N : NF29 x) (hK1 : (N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V))
    (hO : ¬ OB6 x) : IsRupert (univ.image x) := by
  rcases hK1 with ⟨ha2, hb0, hV⟩ | ⟨ha2, hb0, hV⟩
  · exact nf29_K1a_offOB_of_core hcore N ha2 hb0 hV hO
  · have hv : N.sigma.V = -N.V := by simp only [NF29.sigma, NF29.V]; ring
    have := nf29_K1a_offOB_of_core hcore N.sigma (by exact hb0) (by exact ha2) (by linarith)
      (ob6_sigma hO)
    rwa [image_sigma29] at this

end Minimality.H29K1
