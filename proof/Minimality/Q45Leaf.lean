module

public import Mathlib
public import Minimality.DiagCross
public import Minimality.RimCell
public import Minimality.Slide
public import Minimality.UnimodalCert
public import Minimality.FaceChordFac
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.TheoremP24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.TheoremP

namespace Minimality.T24.Q45

/-- At base direction `e5 = x 5 - x 0`, the weak 6-high inequality `max z4 z2 ≤ z6` together
with tie-breaking contradiction `¬(z2 = z4 ∧ z4 = z6)` forces `min z4 z2 < max z6 z0`. -/
lemma hbase_of_h6hi_htie {x : Fin 7 → ℝ³}
    (h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫)
    (htie : ¬ (⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫)) :
    min ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 0, x 5 - x 0⟫ := by
  set e5 := x 5 - x 0
  set z6 := ⟪x 6, e5⟫
  set z4 := ⟪x 4, e5⟫
  set z0 := ⟪x 0, e5⟫
  set z2 := ⟪x 2, e5⟫
  have h46 : z4 ≤ z6 := (le_max_left z4 z2).trans h6hi
  have h26 : z2 ≤ z6 := (le_max_right z4 z2).trans h6hi
  by_contra h_ge
  have h_le : max z6 z0 ≤ min z4 z2 := not_lt.mp h_ge
  have hz6 : z6 ≤ min z4 z2 := (le_max_left z6 z0).trans h_le
  have hz4 : z6 ≤ z4 := hz6.trans (min_le_left z4 z2)
  have hz2 : z6 ≤ z2 := hz6.trans (min_le_right z4 z2)
  have heq4 : z4 = z6 := le_antisymm h46 hz4
  have heq2 : z2 = z6 := le_antisymm h26 hz2
  apply htie
  exact ⟨heq2.trans heq4.symm, heq4⟩

/-- Negation flips inner products with `e5` to `-e5`, swapping min and max:
`min z4 z2 < max z6 z0` at `e5` becomes `min z6 z0 < max z4 z2` at `b = -e5`. -/
lemma hbase_mirror_of_doc {x : Fin 7 → ℝ³}
    (h : min ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 0, x 5 - x 0⟫) :
    min ⟪x 6, -(x 5 - x 0)⟫ ⟪x 0, -(x 5 - x 0)⟫ < max ⟪x 4, -(x 5 - x 0)⟫ ⟪x 2, -(x 5 - x 0)⟫ := by
  set e5 := x 5 - x 0
  have h6 : ⟪x 6, -e5⟫ = - ⟪x 6, e5⟫ := inner_neg_right _ _
  have h0 : ⟪x 0, -e5⟫ = - ⟪x 0, e5⟫ := inner_neg_right _ _
  have h4 : ⟪x 4, -e5⟫ = - ⟪x 4, e5⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e5⟫ = - ⟪x 2, e5⟫ := inner_neg_right _ _
  rw [h6, h0, h4, h2, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

/-- For any Type 24 solid `F`, the three cap edges `![x 0 - x 1, x 2 - x 1, x 6 - x 1]`
at the obtuse corner `x 1` are unconditionally linearly independent. -/
theorem linearIndependent_cap_edges {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1] := by
  have e0 : ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 0 = x 0 - x 1 := rfl
  have e1 : ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1 = x 2 - x 1 := rfl
  have e2 : ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 2 = x 6 - x 1 := rfl
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc_sum : c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1) = 0 := by
    have h := hc
    rw [Fin.sum_univ_three, e0, e1, e2] at h
    exact h
  have hN5 : ⟪F.N 5, c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1)⟫ = 0 := by
    rw [hc_sum, inner_zero_right]
  have hN1 : ⟪F.N 1, c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1)⟫ = 0 := by
    rw [hc_sum, inner_zero_right]
  have hN0 : ⟪F.N 0, c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1)⟫ = 0 := by
    rw [hc_sum, inner_zero_right]
  have z5_2 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [F.inner_sub 5 2 1, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have z5_6 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by
    rw [F.inner_sub 5 6 1, F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
  have n5_0 : ⟪F.N 5, x 0 - x 1⟫ = F.f 5 (x 0) := by
    rw [F.inner_sub 5 0 1, F.zero 5 1 (by decide), sub_zero]
  have z1_0 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by
    rw [F.inner_sub 1 0 1, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self]
  have z1_6 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by
    rw [F.inner_sub 1 6 1, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self]
  have n1_2 : ⟪F.N 1, x 2 - x 1⟫ = F.f 1 (x 2) := by
    rw [F.inner_sub 1 2 1, F.zero 1 1 (by decide), sub_zero]
  have z0_0 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by
    rw [F.inner_sub 0 0 1, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self]
  have z0_2 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by
    rw [F.inner_sub 0 2 1, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have n0_6 : ⟪F.N 0, x 6 - x 1⟫ = F.f 0 (x 6) := by
    rw [F.inner_sub 0 6 1, F.zero 0 1 (by decide), sub_zero]
  simp only [inner_add_right, real_inner_smul_right, z5_2, z5_6, n5_0, mul_zero, add_zero] at hN5
  simp only [inner_add_right, real_inner_smul_right, z1_0, z1_6, n1_2, mul_zero, add_zero, zero_add] at hN1
  simp only [inner_add_right, real_inner_smul_right, z0_0, z0_2, n0_6, mul_zero, add_zero, zero_add] at hN0
  have c0_eq : c 0 = 0 := by
    have neg5 := F.neg 5 0 (by decide)
    nlinarith [hN5, neg5]
  have c1_eq : c 1 = 0 := by
    have neg1 := F.neg 1 2 (by decide)
    nlinarith [hN1, neg1]
  have c2_eq : c 2 = 0 := by
    have neg0 := F.neg 0 6 (by decide)
    nlinarith [hN0, neg0]
  intro i
  fin_cases i
  · exact c0_eq
  · exact c1_eq
  · exact c2_eq

/-- The signed product `0 < Ω * det3(0-6, 2-6, 4-6)` holds unconditionally for any Type 24 solid. -/
theorem omega_mul_det3_0246_pos_unconditional {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  have hli := linearIndependent_cap_edges F
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  exact omega_mul_det3_0246_pos F p v y hxy rfl rfl rfl rfl


/-- For any Type 24 solid, vertex 3 is strictly behind facet 5, giving positive affine coordinate `0 < y 3 0`. -/
theorem type24_y30_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < y 3 0 := by
  have he5 := s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 5 3
  have hz51 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have hz52 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have hz56 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have hn50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [hz51, hz52, hz56] at he5
  simp only [sub_zero, mul_zero, add_zero] at he5
  by_contra hc
  have hle : y 3 0 ≤ 0 := not_lt.mp hc
  have hge : 0 ≤ y 3 0 * F.f 5 (x 0) := mul_nonneg_of_nonpos_of_nonpos hle hn50.le
  rw [← he5] at hge
  have hn53 : F.f 5 (x 3) < 0 := F.neg 5 3 (by decide)
  linarith

/-- The signed product `0 < Ω * det3(0-6, 2-6, 3-6)` holds unconditionally for any Type 24 solid. -/
theorem omega_mul_det3_0236_pos_unconditional {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6) := by
  have hli := linearIndependent_cap_edges F
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  exact omega_mul_det3_0236_pos F p v y hxy rfl rfl rfl rfl

/-- The signed product `0 < Ω * det3(0-6, 2-6, 5-6)` holds unconditionally for any Type 24 solid. -/
theorem omega_mul_det3_0256_pos_unconditional {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) := by
  have hli := linearIndependent_cap_edges F
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  exact omega_mul_det3_0256_pos F p v y hxy rfl rfl rfl rfl

/-- The signed product `0 < Ω * det3(2-6, 3-6, 5-6)` holds unconditionally for any Type 24 solid. -/
theorem omega_mul_det3_2356_pos_unconditional {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6) := by
  have hli := linearIndependent_cap_edges F
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  have ha3 := type24_y30_pos F p v y hxy rfl rfl rfl rfl
  exact omega_mul_det3_2356_pos F p v y hxy rfl rfl rfl rfl ha3

/-- The signed product `0 < Ω * det3(2-6, 3-6, 4-6)` holds unconditionally for any Type 24 solid. -/
theorem omega_mul_det3_2346_pos_unconditional {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) := by
  have hli := linearIndependent_cap_edges F
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  have ha3 := type24_y30_pos F p v y hxy rfl rfl rfl rfl
  exact omega_mul_det3_2346_pos F p v y hxy rfl rfl rfl rfl ha3

/-- Unimodality helper for direct cornerU (`ρ * κ < 0` and `min13 < max02`). -/
theorem unimodal_quad_direct_of_signs_and_base (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (hbase_u : min ⟪p 1, u⟫ ⟪p 3, u⟫ < max ⟪p 0, u⟫ ⟪p 2, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_high := diagCross_not_high p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_high
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) hbase_u
  have hcyc_uni := Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, u⟫) hinj hn hp
  exact Minimality.strictUnimodal_of_cyclic (by decide) hcyc_uni

/-- Strict unimodality of a 4-cycle projected onto `u` from cyclic signs, positive kappa product,
and the base inequality. -/
theorem unimodal_quad_of_signs_and_base (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (hbase_u : min ⟪p 0, u⟫ ⟪p 2, u⟫ < max ⟪p 1, u⟫ ⟪p 3, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_low := diagCross_not_low p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_low
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) hbase_u
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  have hcyc_uni := Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, u⟫) hinj hn hp
  exact Minimality.strictUnimodal_of_cyclic (by decide) hcyc_uni

lemma middle_B1_x5_chord {x : Fin 7 → ℝ³} (ε : ℝ) :
    x 5 = x 4 + (1 - ε) • (x 0 - x 4) + (-1 : ℝ) • u_B1 x ε := by
  have h := middle_B1_x5 x ε
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_B1_x3_chord {x : Fin 7 → ℝ³} (s t ε : ℝ)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 4 + (1 - (s + ε * t)) • (x 0 - x 4) + (-t) • u_B1 x ε := by
  have h := middle_B1_x3 x s t ε hdecomp
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_vertices_B1 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 0 2 j) : q = 3 ∨ q = 5 := by
  revert q; decide

lemma exterior_vertices_B1 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 0 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_B1 (m : ZMod 4) (hmS : quad 6 4 0 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

/-- Along `u_B1 x ε`, all 7 facet signs hold eventually as `ε → 0⁺`. -/
lemma eventually_signs_B1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : s < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_B1 x ε⟫ = 0 ∧
      0 < ⟪F.N 4, u_B1 x ε⟫ ∧
      ⟪F.N 8, u_B1 x ε⟫ < 0 ∧
      0 < ⟪F.N 0, u_B1 x ε⟫ ∧
      ⟪F.N 2, u_B1 x ε⟫ < 0 ∧
      ⟪F.N 7, u_B1 x ε⟫ < 0 ∧
      0 < ⟪F.N 5, u_B1 x ε⟫ := by
  have hu_pi (ε : ℝ) : u_B1 x ε = u_Pi x (-1) ε := by
    dsimp [u_B1, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_B1 x ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have hN4 (ε : ℝ) : 0 < ⟪F.N 4, u_B1 x ε⟫ := by
    rw [hu_pi, inner_N4_u_Pi]
    have hn4 := inner_N4_e5_neg F
    nlinarith
  have ev_N0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 0, u_B1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 0, u_B1 x ε⟫ = -⟪F.N 0, e5 x⟫ + ε * ⟪F.N 0, e4 x⟫ := by
      intro ε; rw [hu_pi, inner_N0_u_Pi]; ring
    have hpos : 0 < -⟪F.N 0, e5 x⟫ := by
      have := inner_N0_e5_neg F
      linarith
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 0, e5 x⟫) (B := ⟪F.N 0, e4 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 2, u_B1 x ε⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hu_pi, inner_N2_u_Pi]
    have hn2 := inner_N2_e4_neg F
    exact mul_neg_of_pos_of_neg hε hn2
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_B1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_B1 x ε⟫ = -⟪F.N 5, e5 x⟫ + ε * ⟪F.N 5, e4 x⟫ := by
      intro ε; rw [hu_pi, inner_N5_u_Pi]; ring
    have hpos : 0 < -⟪F.N 5, e5 x⟫ := by
      dsimp [e5]
      linarith [ha5]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, e5 x⟫) (B := ⟪F.N 5, e4 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 8, u_B1 x ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, t * ⟪F.N 8, u_B1 x ε⟫ = (-(1 - s) + ε * t) * ⟪F.N 8, e4 x⟫ := by
      intro ε; rw [hu_pi, inner_N8_u_Pi F s t (-1) ε hdecomp]; ring
    have hneg : (-(1 - s) : ℝ) < 0 := by linarith [hs1]
    have hN8_pos : 0 < ⟪F.N 8, e4 x⟫ := inner_N8_e4_pos F
    have hc : ContinuousAt (fun ε : ℝ => -(1 - s) + ε * t) 0 := by fun_prop
    have hval : -(1 - s) + (0 : ℝ) * t < 0 := by rw [zero_mul, add_zero]; exact hneg
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have hprod_neg : (-(1 - s) + ε * t) * ⟪F.N 8, e4 x⟫ < 0 := mul_neg_of_neg_of_pos hε hN8_pos
    rw [← hlin] at hprod_neg
    exact neg_of_mul_neg_right hprod_neg ht.le
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_B1 x ε⟫ < 0 := by
    have hc35 : ContinuousAt (fun ε : ℝ => (-1 : ℝ) * (1 - s) + ε * t) 0 := by fun_prop
    have hc34 : ContinuousAt (fun ε : ℝ => (-1 : ℝ) * s + ε * (1 - t)) 0 := by fun_prop
    have hval35 : (-1 : ℝ) * (1 - s) + (0 : ℝ) * t < 0 := by
      rw [zero_mul, add_zero]; linarith [hs1]
    have hval34 : (-1 : ℝ) * s + (0 : ℝ) * (1 - t) < 0 := by
      rw [zero_mul, add_zero]; linarith [hs0]
    have hev35 := (ContinuousAt.eventually_lt hc35 (continuousAt_const (x := 0)) hval35).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hev34 := (ContinuousAt.eventually_lt hc34 (continuousAt_const (x := 0)) hval34).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev35, hev34] with ε h35 h34
    rw [hu_pi]
    exact inner_N7_u_Pi_neg F s t (-1) ε hdecomp hst h35.le h34.le (Or.inl h35)
  filter_upwards [ev_N0, ev_N2, ev_N5, ev_N8, ev_N7] with ε h0 h2 h5 h8 h7
  exact ⟨hN3 ε, hN4 ε, h8, h0, h2, h7, h5⟩

/--
**Pilot Corner Leaf q45_B1 (Regime B1, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_B1(x, ε) = -(x 5 - x 0) + ε • (x 4 - x 0)` for `ε > 0` sufficiently small.

Meaning of hypotheses in the Type 24 corner frame:
* `ha5`: obtuse corner normal sign at edge 5 (`⟪F.N 5, x 5 - x 0⟫ < 0`), giving `0 < ⟪F.N 5, u_B1⟫`.
  (Note: `ha4` is unused in Regime B1 because base direction `-e5` is orthogonal to `F.N 4` and
  `0 < ⟪F.N 4, u_B1⟫` is strictly positive unconditionally; hence `ha4` is dropped).
* `hs0`, `ht`, `hst`: affine decomposition coefficients `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`
  satisfy `0 < s`, `0 < t`, and `1 < s + t` (forced by Lemma M, required for `⟪F.N 7, u_B1⟫ < 0`).
* `hdecomp`: the affine decomposition of vertex 3 in the quadrilateral face `{0, 3, 4, 5}`.
* `hs1`: upper bound `s < 1` defining Regime B (where vertex 3 is closer to edge 0-5 than 0-4).
* `h6hi`: weak 6-high corner condition `max ⟪x 4, e5⟫ ⟪x 2, e5⟫ ≤ ⟪x 6, e5⟫`.
* `htie`: non-degeneracy tie-breaking `¬(z2 = z4 ∧ z4 = z6)`.
* `hS2`: generic injectivity of the quadrilateral projection along the affine ray.
* `hS3`: non-degeneracy of the facet 3 functional between exterior vertices `x 2` and `x 6`.
* `hS4`: general position chord offset condition at the lower exterior vertex `x w`.
-/
theorem q45_B1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : s < 1)
    (h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫)
    (htie : ¬ (⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫))
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 0 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 0 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 4 - x 0⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 0) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 0 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 5 - x 0)
  set d := x 4 - x 0
  have hbase_doc := hbase_of_h6hi_htie h6hi htie
  have hbase_b := hbase_mirror_of_doc hbase_doc
  have ev_signs := eventually_signs_B1 F ha5 s t hs0 ht hst hdecomp hs1
  have ev_bounds := eventually_B1_middle_bounds s t hs0 hs1 ht
  have ev_base := eventually_min02_lt_max13 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h5 | h4
    · left; rw [inner_neg_right, neg_ne_zero]; exact h5
    · right; exact h4
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.and (ev_base.and ev_inj))))
  obtain ⟨ε, hsigns, hε01, hst01, ht_pos, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_B1 x ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_B1]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]; ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6402_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2.1 hsigns.2.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 0) (x 2) (3 + 1) - quad (x 6) (x 4) (x 0) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 0) (x 2) 0 - quad (x 6) (x 4) (x 0) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 0) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 0) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det4 := omega_mul_det3_0246_pos_unconditional F
  have hkap := kappa_rim6402 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [h_om_det4]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos_of_neg_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ < max ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_of_signs_and_base p_quad u ρ hinj_u h_triD hk_pos hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_B1 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq35 := middle_vertices_B1 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 0 := rfl
    rw [hra, hra1]
    rcases hq35 with rfl | rfl
    · refine ⟨1 - (s + ε * t), -t, by linarith [hst01.2], by linarith [hst01.1], by linarith [ht_pos], ?_⟩
      exact middle_B1_x3_chord s t ε hdecomp
    · refine ⟨1 - ε, -1, by linarith [hε01.2], by linarith [hε01.1], by norm_num, ?_⟩
      exact middle_B1_x5_chord ε
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_B1 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_B1 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 0 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

-- =========================================================================
-- Leaf Bs1 (s = 1)
-- =========================================================================

lemma hbase_of_h6hi_htie_Bs1 {x : Fin 7 → ℝ³}
    (h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫)
    (htie : ⟪x 2, x 5 - x 0⟫ ≠ ⟪x 6, x 5 - x 0⟫) :
    min ⟪x 3, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 0, x 5 - x 0⟫ := by
  set e5 := x 5 - x 0
  have h26 : ⟪x 2, e5⟫ ≤ ⟪x 6, e5⟫ := (le_max_right ⟪x 4, e5⟫ ⟪x 2, e5⟫).trans h6hi
  have h26_lt : ⟪x 2, e5⟫ < ⟪x 6, e5⟫ := lt_of_le_of_ne h26 htie
  by_contra h_ge
  have h_le : max ⟪x 6, e5⟫ ⟪x 0, e5⟫ ≤ min ⟪x 3, e5⟫ ⟪x 2, e5⟫ := not_lt.mp h_ge
  have hz6 : ⟪x 6, e5⟫ ≤ min ⟪x 3, e5⟫ ⟪x 2, e5⟫ := (le_max_left _ _).trans h_le
  have hz2 : ⟪x 6, e5⟫ ≤ ⟪x 2, e5⟫ := hz6.trans (min_le_right _ _)
  linarith

lemma hbase_mirror_Bs1 {x : Fin 7 → ℝ³}
    (h : min ⟪x 3, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 0, x 5 - x 0⟫) :
    min ⟪x 6, -(x 5 - x 0)⟫ ⟪x 0, -(x 5 - x 0)⟫ < max ⟪x 3, -(x 5 - x 0)⟫ ⟪x 2, -(x 5 - x 0)⟫ := by
  set e5 := x 5 - x 0
  have h6 : ⟪x 6, -e5⟫ = - ⟪x 6, e5⟫ := inner_neg_right _ _
  have h0 : ⟪x 0, -e5⟫ = - ⟪x 0, e5⟫ := inner_neg_right _ _
  have h3 : ⟪x 3, -e5⟫ = - ⟪x 3, e5⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e5⟫ = - ⟪x 2, e5⟫ := inner_neg_right _ _
  rw [h6, h0, h3, h2, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

lemma middle_Bs1_x4_chord {x : Fin 7 → ℝ³} (t ε : ℝ) (hden : 1 + ε * t ≠ 0)
    (hdecomp : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 4 = x 3 + (1 - 1 / (1 + ε * t)) • (x 0 - x 3) + (t / (1 + ε * t)) • u_B1 x ε := by
  have h := middle_Bs1_x4 x t ε hden hdecomp
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [u_Bs1, u_B1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_Bs1_x5_chord {x : Fin 7 → ℝ³} (t ε : ℝ) (hden : 1 + ε * t ≠ 0)
    (hdecomp : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 5 = x 3 + (1 - ε / (1 + ε * t)) • (x 0 - x 3) + (-1 / (1 + ε * t)) • u_B1 x ε := by
  have h := middle_Bs1_x5 x t ε hden hdecomp
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [u_Bs1, u_B1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_vertices_Bs1 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 3 0 2 j) : q = 4 ∨ q = 5 := by
  revert q; decide

lemma exterior_vertices_Bs1 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 3 0 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_Bs1 (m : ZMod 4) (hmS : quad 6 3 0 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

lemma eventually_Bs1_middle_bounds (t : ℝ) (ht : 0 < t) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 + ε * t ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - 1 / (1 + ε * t) ∧ 1 - 1 / (1 + ε * t) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - ε / (1 + ε * t) ∧ 1 - ε / (1 + ε * t) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), t / (1 + ε * t) ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), -1 / (1 + ε * t) ≠ 0) := by
  have h_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hD0 : (0 : ℝ) < 1 + (0 : ℝ) * t := by rw [zero_mul, add_zero]; norm_num
  have hcD : ContinuousAt (fun ε : ℝ => 1 + ε * t) 0 := by fun_prop
  have hD_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 + ε * t :=
    (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hcD hD0).filter_mono nhdsWithin_le_nhds
  have hden : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 + ε * t ≠ 0 := hD_pos.mono fun _ hd => hd.ne'
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - 1 / (1 + ε * t) ∧ 1 - 1 / (1 + ε * t) < 1 := by
    refine (hD_pos.and h_eps).mono fun ε ⟨hd, he⟩ => ?_
    have hgt1 : 1 < 1 + ε * t := by linarith [mul_pos he ht]
    have hinv_lt1 : 1 / (1 + ε * t) < 1 := (div_lt_one hd).mpr hgt1
    have hinv_pos : 0 < 1 / (1 + ε * t) := div_pos (by norm_num) hd
    exact ⟨by linarith, by linarith⟩
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - ε / (1 + ε * t) ∧ 1 - ε / (1 + ε * t) < 1 := by
    have hc_sub : ContinuousAt (fun ε : ℝ => 1 - ε / (1 + ε * t)) 0 := by
      exact ContinuousAt.sub continuousAt_const (ContinuousAt.div continuousAt_id hcD (by norm_num [hD0]))
    have hval0 : 0 < 1 - (0 : ℝ) / (1 + (0 : ℝ) * t) := by
      simp only [zero_mul, add_zero, zero_div, sub_zero]; norm_num
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - ε / (1 + ε * t) :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc_sub hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 - ε / (1 + ε * t) < 1 := by
      refine (hD_pos.and h_eps).mono fun ε ⟨hd, he⟩ => ?_
      have : 0 < ε / (1 + ε * t) := div_pos he hd
      linarith
    exact h_gt.and h_lt
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t / (1 + ε * t) ≠ 0 :=
    hD_pos.mono fun _ hd => (div_pos ht hd).ne'
  have h4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -1 / (1 + ε * t) ≠ 0 :=
    hD_pos.mono fun _ hd => (div_neg_of_neg_of_pos (by norm_num) hd).ne
  exact ⟨hden, h1, h2, h3, h4⟩

lemma eventually_signs_Bs1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (t : ℝ) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_B1 x ε⟫ = 0 ∧
      ⟪F.N 7, u_B1 x ε⟫ < 0 ∧
      0 < ⟪F.N 8, u_B1 x ε⟫ ∧
      ⟪F.N 2, u_B1 x ε⟫ < 0 ∧
      0 < ⟪F.N 0, u_B1 x ε⟫ ∧
      0 < ⟪F.N 5, u_B1 x ε⟫ := by
  have hu_pi (ε : ℝ) : u_B1 x ε = u_Pi x (-1) ε := by
    dsimp [u_B1, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_B1 x ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have ev_N0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 0, u_B1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 0, u_B1 x ε⟫ = -⟪F.N 0, e5 x⟫ + ε * ⟪F.N 0, e4 x⟫ := by
      intro ε; rw [hu_pi, inner_N0_u_Pi]; ring
    have hpos : 0 < -⟪F.N 0, e5 x⟫ := by
      have := inner_N0_e5_neg F
      linarith
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 0, e5 x⟫) (B := ⟪F.N 0, e4 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 2, u_B1 x ε⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hu_pi, inner_N2_u_Pi]
    have hn2 := inner_N2_e4_neg F
    exact mul_neg_of_pos_of_neg hε hn2
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_B1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_B1 x ε⟫ = -⟪F.N 5, e5 x⟫ + ε * ⟪F.N 5, e4 x⟫ := by
      intro ε; rw [hu_pi, inner_N5_u_Pi]; ring
    have hpos : 0 < -⟪F.N 5, e5 x⟫ := by
      dsimp [e5]
      linarith [ha5]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, e5 x⟫) (B := ⟪F.N 5, e4 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, u_B1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, t * ⟪F.N 8, u_B1 x ε⟫ = ε * t * ⟪F.N 8, e4 x⟫ := by
      intro ε
      have h := inner_N8_u_Pi F 1 t (-1) ε hdecomp
      rw [hu_pi]
      linarith
    have hN8_pos : 0 < ⟪F.N 8, e4 x⟫ := inner_N8_e4_pos F
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hprod : 0 < ε * t * ⟪F.N 8, e4 x⟫ := mul_pos (mul_pos hε ht) hN8_pos
    have ht_prod : 0 < t * ⟪F.N 8, u_B1 x ε⟫ := by rw [hlin]; exact hprod
    exact pos_of_mul_pos_right ht_prod ht.le
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_B1 x ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, t * ⟪F.N 7, u_B1 x ε⟫ =
        (ε * t) * ⟪F.N 7, e35 x⟫ + (-1 + ε * (1 - t)) * ⟪F.N 7, e34 x⟫ := by
      intro ε
      have h := inner_N7_u_Pi F 1 t (-1) ε hdecomp
      rw [hu_pi]
      have heq : 1 + t - 1 = t := by ring
      have h35 : (-1 : ℝ) * (1 - 1) + ε * t = ε * t := by ring
      have h34 : (-1 : ℝ) * 1 + ε * (1 - t) = -1 + ε * (1 - t) := by ring
      rw [heq, h35, h34] at h
      exact h
    have hc : ContinuousAt (fun ε : ℝ => (ε * t) * ⟪F.N 7, e35 x⟫ + (-1 + ε * (1 - t)) * ⟪F.N 7, e34 x⟫) 0 := by fun_prop
    have hval : (0 * t) * ⟪F.N 7, e35 x⟫ + (-1 + 0 * (1 - t)) * ⟪F.N 7, e34 x⟫ < 0 := by
      have hN34 := inner_N7_e34_pos F
      have : (0 * t) * ⟪F.N 7, e35 x⟫ + (-1 + 0 * (1 - t)) * ⟪F.N 7, e34 x⟫ = - ⟪F.N 7, e34 x⟫ := by ring
      rw [this]
      linarith
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have ht_neg : t * ⟪F.N 7, u_B1 x ε⟫ < 0 := by rw [hlin]; exact hε
    exact neg_of_mul_neg_right ht_neg ht.le
  filter_upwards [ev_N0, ev_N2, ev_N5, ev_N8, ev_N7] with ε h0 h2 h5 h8 h7
  exact ⟨hN3 ε, h7, h8, h2, h0, h5⟩


/--
**Corner Leaf q45_Bs1 (Regime Bs1, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_B1(x, ε) = ε • (x 4 - x 0) - (x 5 - x 0)` for `ε > 0` small.

Corner setting & frame meaning:
* Corner direction: `E = e5 = x 5 - x 0`. Perturbation: `d = e4 = x 4 - x 0`.
* `ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0`: single weakest a-hypothesis at corner direction E.
* `hs1 : s = 1`: case condition of Regime Bs1 (parallel quad sides).
* `hs0 : 0 < s`, `ht : 0 < t`, `hst : 1 < s + t`: forced by Lemma M.
* `hdecomp`: affine decomposition `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`.
* `h6hi`: weak 6-high condition at e5: `max ⟪x 4, e5⟫ ⟪x 2, e5⟫ ≤ ⟪x 6, e5⟫`.
* `htie : ⟪x 2, e5⟫ ≠ ⟪x 6, e5⟫`: exclusion of locus T-Bs1.
* `hS2`: generic injectivity of rim 6302 depths along ray b + ε d.
* `hS3`: non-degeneracy `F.f 3 (x 2) ≠ F.f 3 (x 6)` determining farther vertex w.
* `hS4`: locus S4[3,0] chord offset condition for chord 3-0.

Silhouette signs check at u_ε = -e5 + ε e4:
* `N3 = 0` (edge-on facet 3)
* `0 < N2` (-⟪N2, e5⟫ = 0, + ε e4 gives ε ⟪N2, e4⟫ < 0 in doc frame, so 0 < N2 in our frame)
* `N8 < 0` (along e5, -⟪N8, e5⟫ < 0; + ε e4 gives -ε (1 - s) c8 = 0 since s = 1)
* `0 < N6` (along e5, -⟪N6, e5⟫ > 0)
* `N7 < 0` (⟪N7, -e5⟫ = f7(x0) < 0)
* `0 < N5` (from ha5)
Rim produced: 6 3 0 2 (ridges 6-3, 3-0, 0-2, 2-6). Chord: 3-0. Middles: 4, 5. Farther: w ∈ {2, 6}.
Orientation & kappa: Ω κ < 0 (omega_mul_kappa_rim6302_neg), so 0 < ρ κ; uses `cornerU_mirror`.
-/
theorem q45_Bs1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (_hs0 : 0 < s)
    (ht : 0 < t)
    (_hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : s = 1)
    (h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫)
    (htie : ⟪x 2, x 5 - x 0⟫ ≠ ⟪x 6, x 5 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 0 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 3) (x 0) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 3 0 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 5 - x 0)
  set d := x 4 - x 0
  have hdecomp1 : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0) := by rw [hs1] at hdecomp; exact hdecomp
  have hbase_doc := hbase_of_h6hi_htie_Bs1 h6hi htie
  have hbase_b := hbase_mirror_Bs1 hbase_doc
  have ev_signs := eventually_signs_Bs1 F ha5 t ht hdecomp1
  have ev_bounds := eventually_Bs1_middle_bounds t ht
  have ev_base := eventually_min02_lt_max13 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h5 | h4
    · left; rw [inner_neg_right, neg_ne_zero]; exact h5
    · right; exact h4
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.1.and (ev_bounds.2.2.2.1.and (ev_bounds.2.2.2.2.and (ev_base.and ev_inj))))))
  obtain ⟨ε, hsigns, hden, hs4_bnd, hs5_bnd, ht_pos, hneg1_pos, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_B1 x ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_B1]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]; ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6302_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 3) (x 0) (x 2) (3 + 1) - quad (x 6) (x 3) (x 0) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 3) (x 0) (x 2) 0 - quad (x 6) (x 3) (x 0) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 3) (x 0) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 3) (x 0) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det3 := omega_mul_det3_0236_pos_unconditional F
  have hkap := kappa_rim6302 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [h_om_det3]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos_of_neg_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ < max ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_of_signs_and_base p_quad u ρ hinj_u h_triD hk_pos hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_Bs1 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq45 := middle_vertices_Bs1 q hqS hqr
    have hra : x (r a) = x 3 := rfl
    have hra1 : x (r (a + 1)) = x 0 := rfl
    rw [hra, hra1]
    rcases hq45 with rfl | rfl
    · refine ⟨1 - 1 / (1 + ε * t), t / (1 + ε * t), hs4_bnd.1, hs4_bnd.2, ht_pos, ?_⟩
      exact middle_Bs1_x4_chord t ε hden hdecomp1
    · refine ⟨1 - ε / (1 + ε * t), -1 / (1 + ε * t), hs5_bnd.1, hs5_bnd.2, hneg1_pos, ?_⟩
      exact middle_Bs1_x5_chord t ε hden hdecomp1
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_Bs1 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_Bs1 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 3 := rfl
    have hra1 : x (r (a + 1)) = x 0 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

-- =========================================================================
-- Leaf B2 (1 < s)
-- =========================================================================

lemma hbase_of_h6hi_htie_B2 {x : Fin 7 → ℝ³}
    (h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫)
    (htie : ¬ (⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫)) :
    min ⟪x 3, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ < max ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ := by
  set e34 := x 3 - x 4
  have h2_le_min : ⟪x 2, e34⟫ ≤ min ⟪x 6, e34⟫ ⟪x 5, e34⟫ := (le_max_right _ _).trans h6hi
  have h26 : ⟪x 2, e34⟫ ≤ ⟪x 6, e34⟫ := h2_le_min.trans (min_le_left _ _)
  have h25 : ⟪x 2, e34⟫ ≤ ⟪x 5, e34⟫ := h2_le_min.trans (min_le_right _ _)
  by_contra h_ge
  have h_le : max ⟪x 6, e34⟫ ⟪x 5, e34⟫ ≤ min ⟪x 3, e34⟫ ⟪x 2, e34⟫ := not_lt.mp h_ge
  have hz6 : ⟪x 6, e34⟫ ≤ min ⟪x 3, e34⟫ ⟪x 2, e34⟫ := (le_max_left _ _).trans h_le
  have hz5 : ⟪x 5, e34⟫ ≤ min ⟪x 3, e34⟫ ⟪x 2, e34⟫ := (le_max_right _ _).trans h_le
  have hz6_2 : ⟪x 6, e34⟫ ≤ ⟪x 2, e34⟫ := hz6.trans (min_le_right _ _)
  have hz5_2 : ⟪x 5, e34⟫ ≤ ⟪x 2, e34⟫ := hz5.trans (min_le_right _ _)
  have heq6 : ⟪x 2, e34⟫ = ⟪x 6, e34⟫ := le_antisymm h26 hz6_2
  have heq5 : ⟪x 2, e34⟫ = ⟪x 5, e34⟫ := le_antisymm h25 hz5_2
  apply htie
  exact ⟨heq5, heq5.symm.trans heq6⟩

lemma hbase_mirror_B2 {x : Fin 7 → ℝ³}
    (h : min ⟪x 3, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ < max ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫) :
    min ⟪x 6, -(x 3 - x 4)⟫ ⟪x 5, -(x 3 - x 4)⟫ < max ⟪x 3, -(x 3 - x 4)⟫ ⟪x 2, -(x 3 - x 4)⟫ := by
  set e34 := x 3 - x 4
  have h6 : ⟪x 6, -e34⟫ = - ⟪x 6, e34⟫ := inner_neg_right _ _
  have h5 : ⟪x 5, -e34⟫ = - ⟪x 5, e34⟫ := inner_neg_right _ _
  have h3 : ⟪x 3, -e34⟫ = - ⟪x 3, e34⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e34⟫ = - ⟪x 2, e34⟫ := inner_neg_right _ _
  rw [h6, h5, h3, h2, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

lemma middle_B2_x0_chord {x : Fin 7 → ℝ³} (s t ε : ℝ) (hden : s + t - 1 + s * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 0 = x 3 + (1 - (s - 1) / (s + t - 1 + s * ε)) • (x 5 - x 3) +
          (s / (s + t - 1 + s * ε)) • u_B2 x s t ε := by
  have h := middle_B2_x0 x s t ε hden hdecomp
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [u_B2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_B2_x4_chord {x : Fin 7 → ℝ³} (s t ε : ℝ) (hden : s + t - 1 + s * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 4 = x 3 + (1 - (s + t - 1 + ε) / (s + t - 1 + s * ε)) • (x 5 - x 3) +
          ((s + t - 1) / (s + t - 1 + s * ε)) • u_B2 x s t ε := by
  have h := middle_B2_x4 x s t ε hden hdecomp
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v j) h
  simp only [u_B2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

lemma middle_vertices_B2 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 3 5 2 j) : q = 0 ∨ q = 4 := by
  revert q; decide

lemma exterior_vertices_B2 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 3 5 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_B2 (m : ZMod 4) (hmS : quad 6 3 5 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

lemma eventually_signs_B2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ) (hs : 1 < s) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_B2 x s t ε⟫ = 0 ∧
      ⟪F.N 7, u_B2 x s t ε⟫ < 0 ∧
      0 < ⟪F.N 8, u_B2 x s t ε⟫ ∧
      ⟪F.N 6, u_B2 x s t ε⟫ < 0 ∧
      0 < ⟪F.N 2, u_B2 x s t ε⟫ ∧
      0 < ⟪F.N 5, u_B2 x s t ε⟫ := by
  have hu_pi (ε : ℝ) : u_B2 x s t ε = u_Pi x (-(t + ε)) (-(s - 1)) := by
    dsimp [u_B2, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_B2 x s t ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have ev_N2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 2, u_B2 x s t ε⟫ := by
    filter_upwards [self_mem_nhdsWithin] with ε _
    rw [hu_pi, inner_N2_u_Pi]
    have hn2 := inner_N2_e4_neg F
    have : 0 < -(s - 1) * ⟪F.N 2, e4 x⟫ := mul_pos_of_neg_of_neg (by linarith [hs]) hn2
    exact this
  have ev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, u_B2 x s t ε⟫ := by
    have hlin : ∀ ε : ℝ, t * ⟪F.N 8, u_B2 x s t ε⟫ = ε * (s - 1) * ⟪F.N 8, e4 x⟫ := by
      intro ε
      have h := inner_N8_u_Pi F s t (-(t + ε)) (-(s - 1)) hdecomp
      rw [hu_pi]
      have : (-(t + ε) * (1 - s) + -(s - 1) * t) = ε * (s - 1) := by ring
      rw [this] at h
      exact h
    have hN8_pos : 0 < ⟪F.N 8, e4 x⟫ := inner_N8_e4_pos F
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hprod : 0 < ε * (s - 1) * ⟪F.N 8, e4 x⟫ := mul_pos (mul_pos hε (by linarith [hs])) hN8_pos
    have ht_prod : 0 < t * ⟪F.N 8, u_B2 x s t ε⟫ := by rw [hlin]; exact hprod
    exact pos_of_mul_pos_right ht_prod ht.le
  have ev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 6, u_B2 x s t ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, s * ⟪F.N 6, u_B2 x s t ε⟫ = (-(s - 1) - t - ε * s) * ⟪F.N 6, e5 x⟫ := by
      intro ε
      have h := inner_N6_u_Pi F s t (-(t + ε)) (-(s - 1)) hdecomp
      rw [hu_pi]
      have : (-(t + ε) * s + -(s - 1) * (1 - t)) = -(s - 1) - t - ε * s := by ring
      rw [this] at h
      exact h
    have hN6_pos : 0 < ⟪F.N 6, e5 x⟫ := inner_N6_e5_pos F
    have hc : ContinuousAt (fun ε : ℝ => -(s - 1) - t - ε * s) 0 := by fun_prop
    have hval : -(s - 1) - t - (0 : ℝ) * s < 0 := by
      linarith [hs, ht]
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have hprod_neg : (-(s - 1) - t - ε * s) * ⟪F.N 6, e5 x⟫ < 0 := mul_neg_of_neg_of_pos hε hN6_pos
    have hs_neg : s * ⟪F.N 6, u_B2 x s t ε⟫ < 0 := by rw [hlin]; exact hprod_neg
    exact neg_of_mul_neg_right hs_neg (by linarith [hs])
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_B2 x s t ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_B2 x s t ε⟫ = -⟪F.N 5, x 3 - x 4⟫ - ε * ⟪F.N 5, e5 x⟫ := by
      intro ε
      dsimp [u_B2, e5, e4]
      have hdecomp_sub : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
        have h : x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
        rw [h, hdecomp]
        ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hdecomp_sub]
      simp only [inner_add_right, inner_sub_right, real_inner_smul_right]
      ring
    have hpos : 0 < -⟪F.N 5, x 3 - x 4⟫ := by linarith [ha34]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, x 3 - x 4⟫) (B := -⟪F.N 5, e5 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; linarith [hε]
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_B2 x s t ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, (s + t - 1) * ⟪F.N 7, u_B2 x s t ε⟫ =
        (-(t + ε) * (1 - s) + -(s - 1) * t) * ⟪F.N 7, e35 x⟫ +
        (-(t + ε) * s + -(s - 1) * (1 - t)) * ⟪F.N 7, e34 x⟫ := by
      intro ε
      have h := inner_N7_u_Pi F s t (-(t + ε)) (-(s - 1)) hdecomp
      rw [hu_pi]
      exact h
    have hc : ContinuousAt (fun ε : ℝ => (-(t + ε) * (1 - s) + -(s - 1) * t) * ⟪F.N 7, e35 x⟫ +
        (-(t + ε) * s + -(s - 1) * (1 - t)) * ⟪F.N 7, e34 x⟫) 0 := by fun_prop
    have hval : (-(t + (0:ℝ)) * (1 - s) + -(s - 1) * t) * ⟪F.N 7, e35 x⟫ +
        (-(t + (0:ℝ)) * s + -(s - 1) * (1 - t)) * ⟪F.N 7, e34 x⟫ < 0 := by
      have hN34 := inner_N7_e34_pos F
      have h1 : -(t + (0:ℝ)) * (1 - s) + -(s - 1) * t = 0 := by ring
      have h2 : -(t + (0:ℝ)) * s + -(s - 1) * (1 - t) = -(s + t - 1) := by ring
      rw [h1, zero_mul, zero_add, h2]
      have : -(s + t - 1) < 0 := by linarith [hs, ht]
      exact mul_neg_of_neg_of_pos this hN34
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hD_pos : 0 < s + t - 1 := by linarith [hs, ht]
    filter_upwards [hev] with ε hε
    have ht_neg : (s + t - 1) * ⟪F.N 7, u_B2 x s t ε⟫ < 0 := by rw [hlin]; exact hε
    exact neg_of_mul_neg_right ht_neg hD_pos.le
  filter_upwards [ev_N2, ev_N8, ev_N6, ev_N5, ev_N7] with ε h2 h8 h6 h5 h7
  exact ⟨hN3 ε, h7, h8, h6, h2, h5⟩


/--
**Corner Leaf q45_B2 (Regime B2, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_B2(x, s, t, ε) = -(s - 1) • (x 4 - x 0) - (t + ε) • (x 5 - x 0)` for `ε > 0` small.

Corner setting & frame meaning:
* Corner direction: `E = e34 = x 3 - x 4 = (s - 1) e4 + t e5`. Perturbation: `d = e5 = x 5 - x 0`.
* `ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0`: single weakest a-hypothesis at corner direction E (a3 > a4).
* `hs1 : 1 < s`: case condition of Regime B2 (σ > 1).
* `hs0 : 0 < s`, `ht : 0 < t`, `hst : 1 < s + t`: forced by Lemma M.
* `hdecomp`: affine decomposition `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`.
* `h6hi`: weak 6-high condition at e34: `max ⟪x 4, e34⟫ ⟪x 2, e34⟫ ≤ min ⟪x 6, e34⟫ ⟪x 5, e34⟫`.
* `htie : ¬ (⟪x 2, e34⟫ = ⟪x 5, e34⟫ ∧ ⟪x 5, e34⟫ = ⟪x 6, e34⟫)`: exclusion of locus T-B2.
* `hS2`: generic injectivity of rim 6352 depths along ray b + ε d.
* `hS3`: non-degeneracy `F.f 3 (x 2) ≠ F.f 3 (x 6)` determining farther vertex w.
* `hS4`: locus S4[3,5] chord offset condition for chord 3-5.

Silhouette signs check at u_ε = -e34 - ε e5:
* `N3 = 0` (edge-on facet 3)
* `0 < N2` (-(s - 1) ⟪N2, e4⟫ > 0 since s > 1)
* `0 < N8` (along e34, ⟪N8, e34⟫ = 0; + ε e5 gives ε (s - 1) c8 > 0 in doc frame, so 0 < N8 in our frame)
* `N6 < 0` (L(3) = L(4) > L(5) gives N6 < 0 in our frame)
* `N7 < 0` (⟪N7, -e34⟫ = f7(x4) < 0)
* `0 < N5` (from ha34)
Rim produced: 6 3 5 2 (ridges 6-3, 3-5, 5-2, 2-6). Chord: 3-5. Middles: 0, 4. Farther: w ∈ {2, 6}.
Orientation & kappa: Ω κ < 0 (omega_mul_kappa_rim6352_neg), so 0 < ρ κ; uses `cornerU_mirror`.
-/
theorem q45_B2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (_hs0 : 0 < s)
    (ht : 0 < t)
    (_hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : 1 < s)
    (h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫)
    (htie : ¬ (⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫))
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 5 - x 3⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 3 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 3) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 3 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 3 - x 4)
  set d := -(x 5 - x 0)
  have hbase_doc := hbase_of_h6hi_htie_B2 h6hi htie
  have hbase_b := hbase_mirror_B2 hbase_doc
  have ev_signs := eventually_signs_B2 F ha34 s t hs1 ht hdecomp
  have ev_bounds := eventually_B2_middle_bounds s t hs1 ht
  have ev_base := eventually_min02_lt_max13 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h34 | h5
    · left; rw [inner_neg_right, neg_ne_zero]; exact h34
    · right; rw [inner_neg_right, neg_ne_zero]; exact h5
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.1.and (ev_bounds.2.2.2.1.and (ev_bounds.2.2.2.2.and (ev_base.and ev_inj))))))
  obtain ⟨ε, hsigns, hden, hs0_bnd, hs4_bnd, hdel0_pos, hdel4_pos, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_B2 x s t ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_B2]
    ext j
    have hd_sub : (x 3).ofLp j - (x 4).ofLp j = (s - 1) * ((x 4).ofLp j - (x 0).ofLp j) + t * ((x 5).ofLp j - (x 0).ofLp j) := by
      have hdj := congr_arg (fun (v : Euc(3)) => v.ofLp j) hdecomp
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hdj
      linarith
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
    rw [hd_sub]
    ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6352_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 3) (x 5) (x 2) (3 + 1) - quad (x 6) (x 3) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 3) (x 5) (x 2) 0 - quad (x 6) (x 3) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 3) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 3) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det3 := omega_mul_det3_2356_pos_unconditional F
  have hkap := kappa_rim6352 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [h_om_det3]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos_of_neg_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ < max ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_of_signs_and_base p_quad u ρ hinj_u h_triD hk_pos hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_B2 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq04 := middle_vertices_B2 q hqS hqr
    have hra : x (r a) = x 3 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq04 with rfl | rfl
    · refine ⟨1 - (s - 1) / (s + t - 1 + s * ε), s / (s + t - 1 + s * ε),
              by linarith [hs0_bnd.2], by linarith [hs0_bnd.1], hdel0_pos.ne', ?_⟩
      exact middle_B2_x0_chord s t ε hden hdecomp
    · refine ⟨1 - (s + t - 1 + ε) / (s + t - 1 + s * ε), (s + t - 1) / (s + t - 1 + s * ε),
              by linarith [hs4_bnd.2], by linarith [hs4_bnd.1], hdel4_pos.ne', ?_⟩
      exact middle_B2_x4_chord s t ε hden hdecomp
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_B2 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_B2 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 3 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

-- =========================================================================
-- Leaf C1 (t < 1)
-- =========================================================================

lemma hbase_of_h2hi_htie_C1 {x : Fin 7 → ℝ³}
    (h2hi : max ⟪x 5, x 4 - x 0⟫ ⟪x 6, x 4 - x 0⟫ ≤ min ⟪x 2, x 4 - x 0⟫ ⟪x 0, x 4 - x 0⟫)
    (htie : ¬ (⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫)) :
    min ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ < max ⟪x 0, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ := by
  set e4 := x 4 - x 0
  have h5_le : ⟪x 5, e4⟫ ≤ min ⟪x 2, e4⟫ ⟪x 0, e4⟫ := (le_max_left _ _).trans h2hi
  have h6_le : ⟪x 6, e4⟫ ≤ min ⟪x 2, e4⟫ ⟪x 0, e4⟫ := (le_max_right _ _).trans h2hi
  have h52 : ⟪x 5, e4⟫ ≤ ⟪x 2, e4⟫ := h5_le.trans (min_le_left _ _)
  have h62 : ⟪x 6, e4⟫ ≤ ⟪x 2, e4⟫ := h6_le.trans (min_le_left _ _)
  by_contra h_ge
  have h_le : max ⟪x 0, e4⟫ ⟪x 2, e4⟫ ≤ min ⟪x 6, e4⟫ ⟪x 5, e4⟫ := not_lt.mp h_ge
  have hz2 : ⟪x 2, e4⟫ ≤ min ⟪x 6, e4⟫ ⟪x 5, e4⟫ := (le_max_right _ _).trans h_le
  have hz26 : ⟪x 2, e4⟫ ≤ ⟪x 6, e4⟫ := hz2.trans (min_le_left _ _)
  have hz25 : ⟪x 2, e4⟫ ≤ ⟪x 5, e4⟫ := hz2.trans (min_le_right _ _)
  have heq5 : ⟪x 2, e4⟫ = ⟪x 5, e4⟫ := le_antisymm hz25 h52
  have heq6 : ⟪x 2, e4⟫ = ⟪x 6, e4⟫ := le_antisymm hz26 h62
  apply htie
  exact ⟨heq5, heq5.symm.trans heq6⟩

lemma hbase_mirror_C1 {x : Fin 7 → ℝ³}
    (h : min ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ < max ⟪x 0, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫) :
    min ⟪x 0, -(x 4 - x 0)⟫ ⟪x 2, -(x 4 - x 0)⟫ < max ⟪x 6, -(x 4 - x 0)⟫ ⟪x 5, -(x 4 - x 0)⟫ := by
  set e4 := x 4 - x 0
  have h0 : ⟪x 0, -e4⟫ = - ⟪x 0, e4⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e4⟫ = - ⟪x 2, e4⟫ := inner_neg_right _ _
  have h6 : ⟪x 6, -e4⟫ = - ⟪x 6, e4⟫ := inner_neg_right _ _
  have h5 : ⟪x 5, -e4⟫ = - ⟪x 5, e4⟫ := inner_neg_right _ _
  rw [h0, h2, h6, h5, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

lemma middle_vertices_C1 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 0 5 2 j) : q = 4 ∨ q = 3 := by
  revert q; decide

lemma exterior_vertices_C1 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 0 5 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_C1 (m : ZMod 4) (hmS : quad 6 0 5 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

lemma eventually_signs_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t) (ht1 : t < 1)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_C1 x ε⟫ = 0 ∧
      ⟪F.N 4, u_C1 x ε⟫ < 0 ∧
      0 < ⟪F.N 1, u_C1 x ε⟫ ∧
      ⟪F.N 6, u_C1 x ε⟫ < 0 ∧
      0 < ⟪F.N 2, u_C1 x ε⟫ ∧
      ⟪F.N 7, u_C1 x ε⟫ < 0 ∧
      0 < ⟪F.N 5, u_C1 x ε⟫ := by
  have hu_pi (ε : ℝ) : u_C1 x ε = u_Pi x ε (-1) := by
    dsimp [u_C1, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_C1 x ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have ev_N2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 2, u_C1 x ε⟫ := by
    filter_upwards [self_mem_nhdsWithin] with ε _
    rw [hu_pi, inner_N2_u_Pi]
    have hn2 := inner_N2_e4_neg F
    have : 0 < (-1 : ℝ) * ⟪F.N 2, e4 x⟫ := by linarith [hn2]
    exact this
  have ev_N4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 4, u_C1 x ε⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hu_pi, inner_N4_u_Pi]
    have hn4 := inner_N4_e5_neg F
    exact mul_neg_of_pos_of_neg hε hn4
  have ev_N1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 1, u_C1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 1, u_C1 x ε⟫ = -⟪F.N 1, e4 x⟫ + ε * ⟪F.N 1, e5 x⟫ := by
      intro ε; rw [hu_pi, inner_N1_u_Pi]; ring
    have hpos : 0 < -⟪F.N 1, e4 x⟫ := by linarith [inner_N1_e4_neg F]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 1, e4 x⟫) (B := ⟪F.N 1, e5 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 6, u_C1 x ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, s * ⟪F.N 6, u_C1 x ε⟫ = (ε * s - (1 - t)) * ⟪F.N 6, e5 x⟫ := by
      intro ε
      have h := inner_N6_u_Pi F s t ε (-1) hdecomp
      rw [hu_pi]
      have : ε * s + (-1) * (1 - t) = ε * s - (1 - t) := by ring
      rw [this] at h
      exact h
    have hN6_pos : 0 < ⟪F.N 6, e5 x⟫ := inner_N6_e5_pos F
    have hc : ContinuousAt (fun ε : ℝ => ε * s - (1 - t)) 0 := by fun_prop
    have hval : (0 : ℝ) * s - (1 - t) < 0 := by linarith [ht1]
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have hprod_neg : (ε * s - (1 - t)) * ⟪F.N 6, e5 x⟫ < 0 := mul_neg_of_neg_of_pos hε hN6_pos
    have hs_neg : s * ⟪F.N 6, u_C1 x ε⟫ < 0 := by rw [hlin]; exact hprod_neg
    exact neg_of_mul_neg_right hs_neg hs.le
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_C1 x ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, (s + t - 1) * ⟪F.N 7, u_C1 x ε⟫ =
        (ε * (1 - s) - t) * ⟪F.N 7, e35 x⟫ +
        (ε * s - (1 - t)) * ⟪F.N 7, e34 x⟫ := by
      intro ε
      have h := inner_N7_u_Pi F s t ε (-1) hdecomp
      rw [hu_pi]
      have h1 : ε * (1 - s) + (-1) * t = ε * (1 - s) - t := by ring
      have h2 : ε * s + (-1) * (1 - t) = ε * s - (1 - t) := by ring
      rw [h1, h2] at h
      exact h
    have hc : ContinuousAt (fun ε : ℝ => (ε * (1 - s) - t) * ⟪F.N 7, e35 x⟫ +
        (ε * s - (1 - t)) * ⟪F.N 7, e34 x⟫) 0 := by fun_prop
    have hval : ((0 : ℝ) * (1 - s) - t) * ⟪F.N 7, e35 x⟫ +
        ((0 : ℝ) * s - (1 - t)) * ⟪F.N 7, e34 x⟫ < 0 := by
      have hN35 := inner_N7_e35_pos F
      have hN34 := inner_N7_e34_pos F
      have h1 : (0 : ℝ) * (1 - s) - t = -t := by ring
      have h2 : (0 : ℝ) * s - (1 - t) = -(1 - t) := by ring
      rw [h1, h2]
      have p1 : -t * ⟪F.N 7, e35 x⟫ < 0 := mul_neg_of_neg_of_pos (by linarith [ht]) hN35
      have p2 : -(1 - t) * ⟪F.N 7, e34 x⟫ < 0 := mul_neg_of_neg_of_pos (by linarith [ht1]) hN34
      linarith
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hD_pos : 0 < s + t - 1 := by linarith [hst]
    filter_upwards [hev] with ε hε
    have ht_neg : (s + t - 1) * ⟪F.N 7, u_C1 x ε⟫ < 0 := by rw [hlin]; exact hε
    exact neg_of_mul_neg_right ht_neg hD_pos.le
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_C1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_C1 x ε⟫ = -⟪F.N 5, e4 x⟫ + ε * ⟪F.N 5, e5 x⟫ := by
      intro ε; rw [hu_pi, inner_N5_u_Pi]; ring
    have hpos : 0 < -⟪F.N 5, e4 x⟫ := by
      change 0 < -⟪F.N 5, x 4 - x 0⟫; linarith [ha4]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, e4 x⟫) (B := ⟪F.N 5, e5 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  filter_upwards [ev_N4, ev_N1, ev_N6, ev_N2, ev_N7, ev_N5] with ε h4 h1 h6 h2 h7 h5
  exact ⟨hN3 ε, h4, h1, h6, h2, h7, h5⟩


/--
**Corner Leaf q45_C1 (Regime C1, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_C1(x, ε) = ε • (x 5 - x 0) - (x 4 - x 0)` for `ε > 0` small.

Corner setting & frame meaning:
* Corner direction: `E = e4 = x 4 - x 0`. Perturbation: `d = e5 = x 5 - x 0`.
* `ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0`: single weakest a-hypothesis at corner direction E.
* `ht1 : t < 1`: case condition of Regime C1 (τ < 1).
* `hs0 : 0 < s`, `ht : 0 < t`, `hst : 1 < s + t`: forced by Lemma M.
* `hdecomp`: affine decomposition `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`.
* `h2hi`: weak 2-high condition at e4: `max ⟪x 5, e4⟫ ⟪x 6, e4⟫ ≤ min ⟪x 2, e4⟫ ⟪x 0, e4⟫`.
* `htie : ¬ (⟪x 2, e4⟫ = ⟪x 5, e4⟫ ∧ ⟪x 5, e4⟫ = ⟪x 6, e4⟫)`: exclusion of locus T-C1.
* `hS2`: generic injectivity of rim 6052 depths along ray b + ε d.
* `hS3`: non-degeneracy `F.f 3 (x 2) ≠ F.f 3 (x 6)` determining farther vertex w.
* `hS4`: locus S4[0,5] chord offset condition for chord 0-5.

Silhouette signs check at u_ε = -e4 + ε e5:
* `N3 = 0` (edge-on facet 3)
* `N4 < 0` (-⟪N4, e4⟫ = 0, + ε e5 gives ε ⟪N4, e5⟫ < 0 in doc frame, so N4 < 0 in our frame)
* `0 < N1` (-⟪N1, e4⟫ > 0)
* `N6 < 0` (along e4, -⟪N6, e4⟫ < 0 since t < 1)
* `0 < N2` (-⟪N2, e4⟫ > 0)
* `N7 < 0` (⟪N7, -e4⟫ = f7(x0) < 0)
* `0 < N5` (from ha4)
Rim produced: 6 0 5 2 (ridges 6-0, 0-5, 5-2, 2-6). Chord: 0-5. Middles: 4, 3. Farther: w ∈ {2, 6}.
Orientation & kappa: 0 < Ω κ (omega_mul_kappa_rim6052_pos), so ρ κ < 0; uses `cornerU`.
-/
theorem q45_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : t < 1)
    (h2hi : max ⟪x 5, x 4 - x 0⟫ ⟪x 6, x 4 - x 0⟫ ≤ min ⟪x 2, x 4 - x 0⟫ ⟪x 0, x 4 - x 0⟫)
    (htie : ¬ (⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫))
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 5 - x 0⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 0 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad : ZMod 4 → ℝ³ := quad (x 6) (x 0) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 0 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 4 - x 0)
  set d := x 5 - x 0
  have hbase_doc := hbase_of_h2hi_htie_C1 h2hi htie
  have hbase_b := hbase_mirror_C1 hbase_doc
  have ev_signs := eventually_signs_C1 F ha4 s t hs0 ht hst ht1 hdecomp
  have ev_bounds := eventually_C1_middle_bounds s t hs0 ht ht1
  have ev_base := eventually_min13_lt_max02 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h4 | h5
    · left; rw [inner_neg_right, neg_ne_zero]; exact h4
    · right; exact h5
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.and (ev_base.and ev_inj))))
  obtain ⟨ε, hsigns, hε01, hst01, _hdel3_neg, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_C1 x ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_C1]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]; ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6052_canonical_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2.1 hsigns.2.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 0) (x 5) (x 2) (3 + 1) - quad (x 6) (x 0) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 0) (x 5) (x 2) 0 - quad (x 6) (x 0) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 0) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 0) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det3 := omega_mul_det3_0256_pos_unconditional F
  have hkap := kappa_rim6052_canonical x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    exact h_om_det3
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_neg_of_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ < max ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_direct_of_signs_and_base p_quad u ρ hinj_u h_triD hk_neg hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_C1 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq43 := middle_vertices_C1 q hqS hqr
    have hra : x (r a) = x 0 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq43 with rfl | rfl
    · refine ⟨ε, -1, by linarith [hε01.1], by linarith [hε01.2], by norm_num, ?_⟩
      exact middle_C1_x4 x ε
    · refine ⟨t + ε * s, -s, by linarith [hst01.1], by linarith [hst01.2], by linarith [hs0], ?_⟩
      exact middle_C1_x3 x s t ε hdecomp
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_C1 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_C1 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 0 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

-- =========================================================================
-- Leaf Ct1 (t = 1)
-- =========================================================================

lemma hbase_of_h2hi_htie_Ct1 {x : Fin 7 → ℝ³}
    (h2hi : max ⟪x 4, x 4 - x 0⟫ ⟪x 6, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫)
    (htie : ⟪x 2, x 4 - x 0⟫ ≠ ⟪x 6, x 4 - x 0⟫) :
    min ⟪x 6, x 4 - x 0⟫ ⟪x 3, x 4 - x 0⟫ < max ⟪x 0, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ := by
  set e4 := x 4 - x 0
  have h62 : ⟪x 6, e4⟫ ≤ ⟪x 2, e4⟫ := (le_max_right _ _).trans h2hi
  have h62_lt : ⟪x 6, e4⟫ < ⟪x 2, e4⟫ := lt_of_le_of_ne h62 htie.symm
  have h_min : min ⟪x 6, e4⟫ ⟪x 3, e4⟫ ≤ ⟪x 6, e4⟫ := min_le_left _ _
  have h_max : ⟪x 2, e4⟫ ≤ max ⟪x 0, e4⟫ ⟪x 2, e4⟫ := le_max_right _ _
  exact h_min.trans_lt (h62_lt.trans_le h_max)

lemma hbase_mirror_Ct1 {x : Fin 7 → ℝ³}
    (h : min ⟪x 6, x 4 - x 0⟫ ⟪x 3, x 4 - x 0⟫ < max ⟪x 0, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫) :
    min ⟪x 0, -(x 4 - x 0)⟫ ⟪x 2, -(x 4 - x 0)⟫ < max ⟪x 6, -(x 4 - x 0)⟫ ⟪x 3, -(x 4 - x 0)⟫ := by
  set e4 := x 4 - x 0
  have h0 : ⟪x 0, -e4⟫ = - ⟪x 0, e4⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e4⟫ = - ⟪x 2, e4⟫ := inner_neg_right _ _
  have h6 : ⟪x 6, -e4⟫ = - ⟪x 6, e4⟫ := inner_neg_right _ _
  have h3 : ⟪x 3, -e4⟫ = - ⟪x 3, e4⟫ := inner_neg_right _ _
  rw [h0, h2, h6, h3, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

lemma middle_vertices_Ct1 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 0 3 2 j) : q = 5 ∨ q = 4 := by
  revert q; decide

lemma exterior_vertices_Ct1 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 0 3 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_Ct1 (m : ZMod 4) (hmS : quad 6 0 3 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

lemma eventually_Ct1_middle_bounds (s : ℝ) (hs : 0 < s) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 + ε * s ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 / (1 + ε * s) ∧ 1 / (1 + ε * s) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε / (1 + ε * s) ∧ ε / (1 + ε * s) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), s / (1 + ε * s) ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), -1 / (1 + ε * s) ≠ 0) := by
  have h_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hD0 : (0 : ℝ) < 1 + (0 : ℝ) * s := by rw [zero_mul, add_zero]; norm_num
  have hcD : ContinuousAt (fun ε : ℝ => 1 + ε * s) 0 := by fun_prop
  have hD_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 + ε * s :=
    (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hcD hD0).filter_mono nhdsWithin_le_nhds
  have hden : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 + ε * s ≠ 0 := hD_pos.mono fun _ hd => hd.ne'
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 / (1 + ε * s) ∧ 1 / (1 + ε * s) < 1 := by
    refine (hD_pos.and h_eps).mono fun ε ⟨hd, he⟩ => ?_
    have hgt1 : 1 < 1 + ε * s := by linarith [mul_pos he hs]
    have hinv_lt1 : 1 / (1 + ε * s) < 1 := (div_lt_one hd).mpr hgt1
    have hinv_pos : 0 < 1 / (1 + ε * s) := div_pos (by norm_num) hd
    exact ⟨hinv_pos, hinv_lt1⟩
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε / (1 + ε * s) ∧ ε / (1 + ε * s) < 1 := by
    have hc_sub : ContinuousAt (fun ε : ℝ => ε / (1 + ε * s)) 0 := by
      exact ContinuousAt.div continuousAt_id hcD (by norm_num [hD0])
    have hval1 : (0 : ℝ) / (1 + (0 : ℝ) * s) < 1 := by
      simp only [zero_mul, add_zero, zero_div]; norm_num
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε / (1 + ε * s) < 1 :=
      (ContinuousAt.eventually_lt hc_sub (continuousAt_const (x := 0)) hval1).filter_mono nhdsWithin_le_nhds
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε / (1 + ε * s) := by
      refine (hD_pos.and h_eps).mono fun ε ⟨hd, he⟩ => div_pos he hd
    exact h_gt.and h_lt
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), s / (1 + ε * s) ≠ 0 :=
    hD_pos.mono fun _ hd => (div_pos hs hd).ne'
  have h4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -1 / (1 + ε * s) ≠ 0 :=
    hD_pos.mono fun _ hd => (div_neg_of_neg_of_pos (by norm_num) hd).ne
  exact ⟨hden, h1, h2, h3, h4⟩

lemma eventually_signs_Ct1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s : ℝ) (hs : 0 < s)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + (1 : ℝ) • (x 5 - x 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_Ct1 x ε⟫ = 0 ∧
      ⟪F.N 4, u_Ct1 x ε⟫ < 0 ∧
      0 < ⟪F.N 1, u_Ct1 x ε⟫ ∧
      ⟪F.N 7, u_Ct1 x ε⟫ < 0 ∧
      0 < ⟪F.N 6, u_Ct1 x ε⟫ ∧
      0 < ⟪F.N 5, u_Ct1 x ε⟫ := by
  have hu_pi (ε : ℝ) : u_Ct1 x ε = u_Pi x ε (-1) := by
    dsimp [u_Ct1, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_Ct1 x ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have ev_N4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 4, u_Ct1 x ε⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hu_pi, inner_N4_u_Pi]
    have hn4 := inner_N4_e5_neg F
    exact mul_neg_of_pos_of_neg hε hn4
  have ev_N1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 1, u_Ct1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 1, u_Ct1 x ε⟫ = -⟪F.N 1, e4 x⟫ + ε * ⟪F.N 1, e5 x⟫ := by
      intro ε; rw [hu_pi, inner_N1_u_Pi]; ring
    have hpos : 0 < -⟪F.N 1, e4 x⟫ := by linarith [inner_N1_e4_neg F]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 1, e4 x⟫) (B := ⟪F.N 1, e5 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  have ev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 6, u_Ct1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, s * ⟪F.N 6, u_Ct1 x ε⟫ = (ε * s) * ⟪F.N 6, e5 x⟫ := by
      intro ε
      have h := inner_N6_u_Pi F s 1 ε (-1) hdecomp
      rw [hu_pi]
      have : ε * s + (-1) * (1 - (1 : ℝ)) = ε * s := by ring
      rw [this] at h
      exact h
    have hN6_pos : 0 < ⟪F.N 6, e5 x⟫ := inner_N6_e5_pos F
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hprod_pos : 0 < (ε * s) * ⟪F.N 6, e5 x⟫ := mul_pos (mul_pos hε hs) hN6_pos
    have hs_pos : 0 < s * ⟪F.N 6, u_Ct1 x ε⟫ := by rw [hlin]; exact hprod_pos
    exact pos_of_mul_pos_right hs_pos hs.le
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_Ct1 x ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, s * ⟪F.N 7, u_Ct1 x ε⟫ =
        (ε * (1 - s) - 1) * ⟪F.N 7, e35 x⟫ +
        (ε * s) * ⟪F.N 7, e34 x⟫ := by
      intro ε
      have h := inner_N7_u_Pi F s 1 ε (-1) hdecomp
      rw [hu_pi]
      have h1 : ε * (1 - s) + (-1) * (1 : ℝ) = ε * (1 - s) - 1 := by ring
      have h2 : ε * s + (-1) * (1 - (1 : ℝ)) = ε * s := by ring
      have h3 : s + (1 : ℝ) - 1 = s := by ring
      rw [h1, h2, h3] at h
      exact h
    have hc : ContinuousAt (fun ε : ℝ => (ε * (1 - s) - 1) * ⟪F.N 7, e35 x⟫ +
        (ε * s) * ⟪F.N 7, e34 x⟫) 0 := by fun_prop
    have hval : ((0 : ℝ) * (1 - s) - 1) * ⟪F.N 7, e35 x⟫ +
        ((0 : ℝ) * s) * ⟪F.N 7, e34 x⟫ < 0 := by
      have hN35 := inner_N7_e35_pos F
      have h1 : (0 : ℝ) * (1 - s) - 1 = -1 := by ring
      have h2 : (0 : ℝ) * s = 0 := by ring
      rw [h1, h2, zero_mul, add_zero]
      linarith [hN35]
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have ht_neg : s * ⟪F.N 7, u_Ct1 x ε⟫ < 0 := by rw [hlin]; exact hε
    exact neg_of_mul_neg_right ht_neg hs.le
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_Ct1 x ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_Ct1 x ε⟫ = -⟪F.N 5, e4 x⟫ + ε * ⟪F.N 5, e5 x⟫ := by
      intro ε; rw [hu_pi, inner_N5_u_Pi]; ring
    have hpos : 0 < -⟪F.N 5, e4 x⟫ := by
      change 0 < -⟪F.N 5, x 4 - x 0⟫; linarith [ha4]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, e4 x⟫) (B := ⟪F.N 5, e5 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; exact hε
  filter_upwards [ev_N4, ev_N1, ev_N7, ev_N6, ev_N5] with ε h4 h1 h7 h6 h5
  exact ⟨hN3 ε, h4, h1, h7, h6, h5⟩


/--
**Corner Leaf q45_Ct1 (Regime Ct1, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_Ct1(x, ε) = ε • (x 5 - x 0) - (x 4 - x 0)` for `ε > 0` small.

Corner setting & frame meaning:
* Corner direction: `E = e4 = x 4 - x 0`. Perturbation: `d = e5 = x 5 - x 0`.
* `ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0`: single weakest a-hypothesis at corner direction E.
* `ht1 : t = 1`: case condition of Regime Ct1 (parallel quad sides).
* `hs0 : 0 < s`, `ht : 0 < t`, `hst : 1 < s + t`: forced by Lemma M.
* `hdecomp`: affine decomposition `x 3 - x 0 = s • (x 4 - x 0) + (1 : ℝ) • (x 5 - x 0)`.
* `h2hi`: weak 2-high condition at e4: `max ⟪x 4, e4⟫ ⟪x 6, e4⟫ ≤ ⟪x 2, e4⟫`.
* `htie : ⟪x 2, e4⟫ ≠ ⟪x 6, e4⟫`: exclusion of locus T-Ct1.
* `hS2`: generic injectivity of rim 6032 depths along ray b + ε d.
* `hS3`: non-degeneracy `F.f 3 (x 2) ≠ F.f 3 (x 6)` determining farther vertex w.
* `hS4`: locus S4[0,3] chord offset condition for chord 0-3.

Silhouette signs check at u_ε = -e4 + ε e5:
* `N3 = 0` (edge-on facet 3)
* `N4 < 0` (-⟪N4, e4⟫ = 0, + ε e5 gives ε ⟪N4, e5⟫ < 0 in doc frame, so N4 < 0 in our frame)
* `0 < N1` (-⟪N1, e4⟫ > 0)
* `0 < N6` (along e4, -⟪N6, e4⟫ = 0 since t = 1; + ε e5 gives -ε c6 < 0 in doc frame, so 0 < N6 in our frame)
* `N7 < 0` (⟪N7, -e4⟫ = f7(x0) < 0)
* `0 < N5` (from ha4)
Rim produced: 6 0 3 2 (ridges 6-0, 0-3, 3-2, 2-6). Chord: 0-3. Middles: 5, 4. Farther: w ∈ {2, 6}.
Orientation & kappa: 0 < Ω κ (omega_mul_kappa_rim6032_pos), so ρ κ < 0; uses `cornerU`.
-/
theorem q45_Ct1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (_ht : 0 < t)
    (_hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + (1 : ℝ) • (x 5 - x 0))
    (_ht1 : t = 1)
    (h2hi : max ⟪x 4, x 4 - x 0⟫ ⟪x 6, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫)
    (htie : ⟪x 2, x 4 - x 0⟫ ≠ ⟪x 6, x 4 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 3 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad : ZMod 4 → ℝ³ := quad (x 6) (x 0) (x 3) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 0 3 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 4 - x 0)
  set d := x 5 - x 0
  have hbase_doc := hbase_of_h2hi_htie_Ct1 h2hi htie
  have hbase_b := hbase_mirror_Ct1 hbase_doc
  have ev_signs := eventually_signs_Ct1 F ha4 s hs0 hdecomp
  have ev_bounds := eventually_Ct1_middle_bounds s hs0
  have ev_base := eventually_min13_lt_max02 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h4 | h5
    · left; rw [inner_neg_right, neg_ne_zero]; exact h4
    · right; exact h5
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.1.and (ev_bounds.2.2.2.1.and (ev_bounds.2.2.2.2.and (ev_base.and ev_inj))))))
  obtain ⟨ε, hsigns, hden, hs5_bnd, hs4_bnd, hdel5_pos, hdel4_pos, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_Ct1 x ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_Ct1]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]; ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6032_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 0) (x 3) (x 2) (3 + 1) - quad (x 6) (x 0) (x 3) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 0) (x 3) (x 2) 0 - quad (x 6) (x 0) (x 3) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 0) (x 3) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 0) (x 3) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det3 := omega_mul_det3_0236_pos_unconditional F
  have hkap := kappa_rim6032 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    exact h_om_det3
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_neg_of_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ < max ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_direct_of_signs_and_base p_quad u ρ hinj_u h_triD hk_neg hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_Ct1 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq54 := middle_vertices_Ct1 q hqS hqr
    have hra : x (r a) = x 0 := rfl
    have hra1 : x (r (a + 1)) = x 3 := rfl
    rw [hra, hra1]
    rcases hq54 with rfl | rfl
    · refine ⟨1 / (1 + ε * s), s / (1 + ε * s),
              hs5_bnd.1, hs5_bnd.2, hdel5_pos, ?_⟩
      exact middle_Ct1_x5 x s ε hden hdecomp
    · refine ⟨ε / (1 + ε * s), -1 / (1 + ε * s),
              hs4_bnd.1, hs4_bnd.2, hdel4_pos, ?_⟩
      exact middle_Ct1_x4 x s ε hden hdecomp
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_Ct1 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_Ct1 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 0 := rfl
    have hra1 : x (r (a + 1)) = x 3 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

-- =========================================================================
-- Leaf C2 (1 < t)
-- =========================================================================

lemma hbase_of_h2hi_htie_C2 {x : Fin 7 → ℝ³}
    (h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫)
    (htie : ¬ (⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫)) :
    min ⟪x 6, x 3 - x 5⟫ ⟪x 3, x 3 - x 5⟫ < max ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ := by
  set e35 := x 3 - x 5
  by_contra h_ge
  have h_le : max ⟪x 4, e35⟫ ⟪x 2, e35⟫ ≤ min ⟪x 6, e35⟫ ⟪x 3, e35⟫ := not_lt.mp h_ge
  have hz4 : ⟪x 4, e35⟫ ≤ ⟪x 6, e35⟫ := (le_max_left _ _).trans (h_le.trans (min_le_left _ _))
  have hz2 : ⟪x 2, e35⟫ ≤ ⟪x 6, e35⟫ := (le_max_right _ _).trans (h_le.trans (min_le_left _ _))
  have h6_le : ⟪x 6, e35⟫ ≤ min ⟪x 2, e35⟫ ⟪x 4, e35⟫ := (le_max_left _ _).trans h2hi
  have hz62 : ⟪x 6, e35⟫ ≤ ⟪x 2, e35⟫ := h6_le.trans (min_le_left _ _)
  have hz64 : ⟪x 6, e35⟫ ≤ ⟪x 4, e35⟫ := h6_le.trans (min_le_right _ _)
  have heq2 : ⟪x 2, e35⟫ = ⟪x 6, e35⟫ := le_antisymm hz2 hz62
  have heq4 : ⟪x 4, e35⟫ = ⟪x 6, e35⟫ := le_antisymm hz4 hz64
  apply htie
  exact ⟨heq2.trans heq4.symm, heq4⟩

lemma hbase_mirror_C2 {x : Fin 7 → ℝ³}
    (h : min ⟪x 6, x 3 - x 5⟫ ⟪x 3, x 3 - x 5⟫ < max ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫) :
    min ⟪x 4, -(x 3 - x 5)⟫ ⟪x 2, -(x 3 - x 5)⟫ < max ⟪x 6, -(x 3 - x 5)⟫ ⟪x 3, -(x 3 - x 5)⟫ := by
  set e35 := x 3 - x 5
  have h4 : ⟪x 4, -e35⟫ = - ⟪x 4, e35⟫ := inner_neg_right _ _
  have h2 : ⟪x 2, -e35⟫ = - ⟪x 2, e35⟫ := inner_neg_right _ _
  have h6 : ⟪x 6, -e35⟫ = - ⟪x 6, e35⟫ := inner_neg_right _ _
  have h3 : ⟪x 3, -e35⟫ = - ⟪x 3, e35⟫ := inner_neg_right _ _
  rw [h4, h2, h6, h3, min_neg_neg, max_neg_neg]
  exact neg_lt_neg h

lemma middle_vertices_C2 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 3 2 j) : q = 0 ∨ q = 5 := by
  revert q; decide

lemma exterior_vertices_C2 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 3 2 j) : q = 1 := by
  revert q; decide

lemma w_candidates_C2 (m : ZMod 4) (hmS : quad 6 4 3 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m; decide

lemma eventually_signs_C2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ) (hs : 0 < s) (ht : 1 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪F.N 3, u_C2 x s t ε⟫ = 0 ∧
      ⟪F.N 8, u_C2 x s t ε⟫ < 0 ∧
      0 < ⟪F.N 4, u_C2 x s t ε⟫ ∧
      ⟪F.N 7, u_C2 x s t ε⟫ < 0 ∧
      0 < ⟪F.N 6, u_C2 x s t ε⟫ ∧
      0 < ⟪F.N 5, u_C2 x s t ε⟫ := by
  have hu_pi (ε : ℝ) : u_C2 x s t ε = u_Pi x (-(t - 1)) (-(s + ε)) := by
    dsimp [u_C2, u_Pi, e4, e5]
    ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 (ε : ℝ) : ⟪F.N 3, u_C2 x s t ε⟫ = 0 := by
    rw [hu_pi, inner_N3_u_Pi]
  have ev_N4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 4, u_C2 x s t ε⟫ := by
    filter_upwards [self_mem_nhdsWithin] with ε _
    rw [hu_pi, inner_N4_u_Pi]
    have hn4 := inner_N4_e5_neg F
    have : 0 < -(t - 1) * ⟪F.N 4, e5 x⟫ := mul_pos_of_neg_of_neg (by linarith [ht]) hn4
    exact this
  have ev_N8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 8, u_C2 x s t ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, t * ⟪F.N 8, u_C2 x s t ε⟫ = (-(s + t - 1) - ε * t) * ⟪F.N 8, e4 x⟫ := by
      intro ε
      have h := inner_N8_u_Pi F s t (-(t - 1)) (-(s + ε)) hdecomp
      rw [hu_pi]
      have : -(t - 1) * (1 - s) + -(s + ε) * t = -(s + t - 1) - ε * t := by ring
      rw [this] at h
      exact h
    have hN8_pos : 0 < ⟪F.N 8, e4 x⟫ := inner_N8_e4_pos F
    have hc : ContinuousAt (fun ε : ℝ => -(s + t - 1) - ε * t) 0 := by fun_prop
    have hval : -(s + t - 1) - (0 : ℝ) * t < 0 := by
      linarith [hs, ht]
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hev] with ε hε
    have hprod_neg : (-(s + t - 1) - ε * t) * ⟪F.N 8, e4 x⟫ < 0 := mul_neg_of_neg_of_pos hε hN8_pos
    have ht_neg : t * ⟪F.N 8, u_C2 x s t ε⟫ < 0 := by rw [hlin]; exact hprod_neg
    exact neg_of_mul_neg_right ht_neg (by linarith [ht])
  have ev_N6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 6, u_C2 x s t ε⟫ := by
    have hlin : ∀ ε : ℝ, s * ⟪F.N 6, u_C2 x s t ε⟫ = (ε * (t - 1)) * ⟪F.N 6, e5 x⟫ := by
      intro ε
      have h := inner_N6_u_Pi F s t (-(t - 1)) (-(s + ε)) hdecomp
      rw [hu_pi]
      have : -(t - 1) * s + -(s + ε) * (1 - t) = ε * (t - 1) := by ring
      rw [this] at h
      exact h
    have hN6_pos : 0 < ⟪F.N 6, e5 x⟫ := inner_N6_e5_pos F
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hprod_pos : 0 < (ε * (t - 1)) * ⟪F.N 6, e5 x⟫ := mul_pos (mul_pos hε (by linarith [ht])) hN6_pos
    have hs_pos : 0 < s * ⟪F.N 6, u_C2 x s t ε⟫ := by rw [hlin]; exact hprod_pos
    exact pos_of_mul_pos_right hs_pos hs.le
  have ev_N7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u_C2 x s t ε⟫ < 0 := by
    have hlin : ∀ ε : ℝ, (s + t - 1) * ⟪F.N 7, u_C2 x s t ε⟫ =
        (-(s + t - 1) - ε * t) * ⟪F.N 7, e35 x⟫ +
        (ε * (t - 1)) * ⟪F.N 7, e34 x⟫ := by
      intro ε
      have h := inner_N7_u_Pi F s t (-(t - 1)) (-(s + ε)) hdecomp
      rw [hu_pi]
      have h1 : -(t - 1) * (1 - s) + -(s + ε) * t = -(s + t - 1) - ε * t := by ring
      have h2 : -(t - 1) * s + -(s + ε) * (1 - t) = ε * (t - 1) := by ring
      rw [h1, h2] at h
      exact h
    have hc : ContinuousAt (fun ε : ℝ => (-(s + t - 1) - ε * t) * ⟪F.N 7, e35 x⟫ +
        (ε * (t - 1)) * ⟪F.N 7, e34 x⟫) 0 := by fun_prop
    have hval : (-(s + t - 1) - (0 : ℝ) * t) * ⟪F.N 7, e35 x⟫ +
        ((0 : ℝ) * (t - 1)) * ⟪F.N 7, e34 x⟫ < 0 := by
      have hN35 := inner_N7_e35_pos F
      have h1 : -(s + t - 1) - (0 : ℝ) * t = -(s + t - 1) := by ring
      have h2 : (0 : ℝ) * (t - 1) = 0 := by ring
      rw [h1, h2, zero_mul, add_zero]
      have : -(s + t - 1) < 0 := by linarith [hs, ht]
      exact mul_neg_of_neg_of_pos this hN35
    have hev := (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hD_pos : 0 < s + t - 1 := by linarith [hs, ht]
    filter_upwards [hev] with ε hε
    have ht_neg : (s + t - 1) * ⟪F.N 7, u_C2 x s t ε⟫ < 0 := by rw [hlin]; exact hε
    exact neg_of_mul_neg_right ht_neg hD_pos.le
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 5, u_C2 x s t ε⟫ := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, u_C2 x s t ε⟫ = -⟪F.N 5, x 3 - x 5⟫ - ε * ⟪F.N 5, e4 x⟫ := by
      intro ε
      dsimp [u_C2, e4, e5]
      have hdecomp_sub : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
        have h : x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
        rw [h, hdecomp]
        ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hdecomp_sub]
      simp only [inner_add_right, inner_sub_right, real_inner_smul_right]
      ring
    have hpos : 0 < -⟪F.N 5, x 3 - x 5⟫ := by linarith [ha35]
    filter_upwards [Minimality.eventually_pos_affine (A := -⟪F.N 5, x 3 - x 5⟫) (B := -⟪F.N 5, e4 x⟫) (Or.inl hpos)] with ε hε
    rw [hlin]; linarith [hε]
  filter_upwards [ev_N8, ev_N4, ev_N7, ev_N6, ev_N5] with ε h8 h4 h7 h6 h5
  exact ⟨hN3 ε, h8, h4, h7, h6, h5⟩


/--
**Corner Leaf q45_C2 (Regime C2, Facet 3)**:
Constructs a valid `FaceChordView F 3` along the perturbation ray
`u_C2(x, s, t, ε) = -(s + ε) • (x 4 - x 0) - (t - 1) • (x 5 - x 0)` for `ε > 0` small.

Corner setting & frame meaning:
* Corner direction: `E = e35 = x 3 - x 5 = s e4 + (t - 1) e5`. Perturbation: `d = e4 = x 4 - x 0`.
* `ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0`: single weakest a-hypothesis at corner direction E (a3 > a5).
* `ht1 : 1 < t`: case condition of Regime C2 (τ > 1).
* `hs0 : 0 < s`, `ht : 0 < t`, `hst : 1 < s + t`: forced by Lemma M.
* `hdecomp`: affine decomposition `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`.
* `h2hi`: weak 2-high condition at e35: `max ⟪x 6, e35⟫ ⟪x 5, e35⟫ ≤ min ⟪x 2, e35⟫ ⟪x 4, e35⟫`.
* `htie : ¬ (⟪x 2, e35⟫ = ⟪x 4, e35⟫ ∧ ⟪x 4, e35⟫ = ⟪x 6, e35⟫)`: exclusion of locus T-C2.
* `hS2`: generic injectivity of rim 6432 depths along ray b + ε d.
* `hS3`: non-degeneracy `F.f 3 (x 2) ≠ F.f 3 (x 6)` determining farther vertex w.
* `hS4`: locus S4[3,4] chord offset condition for chord 3-4.

Silhouette signs check at u_ε = -e35 - ε e4:
* `N3 = 0` (edge-on facet 3)
* `0 < N4` (-(t - 1) ⟪N4, e5⟫ > 0 since t > 1)
* `N8 < 0` (L(3) = L(5) > L(4) gives N8 < 0 in our frame)
* `0 < N6` (along e35, ⟪N6, e35⟫ = 0; + ε e4 gives -ε (t - 1) c6 < 0 in doc frame, so 0 < N6 in our frame)
* `N7 < 0` (⟪N7, -e35⟫ = f7(x5) < 0)
* `0 < N5` (from ha35)
Rim produced: 6 4 3 2 (ridges 6-4, 4-3, 3-2, 2-6). Chord: 3-4. Middles: 0, 5. Farther: w ∈ {2, 6}.
Orientation & kappa: 0 < Ω κ (omega_mul_kappa_rim6432_pos), so ρ κ < 0; uses `cornerU`.
-/
theorem q45_C2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (_ht : 0 < t)
    (_hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : 1 < t)
    (h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫)
    (htie : ¬ (⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫))
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 3 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 3 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 4 - x 3⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad : ZMod 4 → ℝ³ := quad (x 6) (x 4) (x 3) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 3 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := -(x 3 - x 5)
  set d := -(x 4 - x 0)
  have hbase_doc := hbase_of_h2hi_htie_C2 h2hi htie
  have hbase_b := hbase_mirror_C2 hbase_doc
  have ev_signs := eventually_signs_C2 F ha35 s t hs0 ht1 hdecomp
  have ev_bounds := eventually_C2_middle_bounds s t hs0 ht1
  have ev_base := eventually_min13_lt_max02 p_quad b d hbase_b
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    rcases hs2 with h35 | h4
    · left; rw [inner_neg_right, neg_ne_zero]; exact h35
    · right; rw [inner_neg_right, neg_ne_zero]; exact h4
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_signs.and (ev_bounds.1.and (ev_bounds.2.1.and (ev_bounds.2.2.1.and (ev_bounds.2.2.2.1.and (ev_bounds.2.2.2.2.and (ev_base.and ev_inj))))))
  obtain ⟨ε, hsigns, hden, hs0_bnd, hs5_bnd, hdel0_pos, hdel5_pos, hbase_ε, hinj_ε⟩ := ev_all.exists
  set u := u_C2 x s t ε
  have hu_bd : u = b + ε • d := by
    dsimp [u, b, d, u_C2]
    ext j
    have hd_sub : (x 3).ofLp j - (x 5).ofLp j = s * ((x 4).ofLp j - (x 0).ofLp j) + (t - 1) * ((x 5).ofLp j - (x 0).ofLp j) := by
      have hdj := congr_arg (fun (v : Euc(3)) => v.ofLp j) hdecomp
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hdj
      linarith
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
    rw [hd_sub]
    ring
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := rim6432_of_signs F hsigns.1 hsigns.2.1 hsigns.2.2.1 hsigns.2.2.2.1 hsigns.2.2.2.2.1 hsigns.2.2.2.2.2
  have hN5_pos : 0 < ⟪F.N 5, u⟫ := hsigns.2.2.2.2.2
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 3) (x 2) (3 + 1) - quad (x 6) (x 4) (x 3) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 3) (x 2) 0 - quad (x 6) (x 4) (x 3) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 3) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 3) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rim_orient := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_rho_om : ρ * Ω < 0 := by
    nlinarith [h_rim_orient, hN5_pos]
  have h_om_det3 := omega_mul_det3_2346_pos_unconditional F
  have hkap := kappa_rim6432 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    exact h_om_det3
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_neg_of_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hbase_u : min ⟪p_quad 1, u⟫ ⟪p_quad 3, u⟫ < max ⟪p_quad 0, u⟫ ⟪p_quad 2, u⟫ := by
    rw [hu_bd]; exact hbase_ε
  have hinj_u : Function.Injective (fun i => ⟪p_quad i, u⟫) := by
    rw [hu_bd]; exact hinj_ε
  have h_uni := unimodal_quad_direct_of_signs_and_base p_quad u ρ hinj_u h_triD hk_neg hbase_u
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_C2 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq05 := middle_vertices_C2 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 3 := rfl
    rw [hra, hra1]
    rcases hq05 with rfl | rfl
    · refine ⟨(t - 1) / (s + t - 1 + t * ε), t / (s + t - 1 + t * ε),
              hs0_bnd.1, hs0_bnd.2, hdel0_pos.ne', ?_⟩
      exact middle_C2_x0 x s t ε hden hdecomp
    · refine ⟨(s + t - 1 + ε) / (s + t - 1 + t * ε), (s + t - 1) / (s + t - 1 + t * ε),
              hs5_bnd.1, hs5_bnd.2, hdel5_pos.ne', ?_⟩
      exact middle_C2_x5 x s t ε hden hdecomp
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_C2 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_C2 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 3 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

end Minimality.T24.Q45
