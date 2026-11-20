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

end Minimality.T24.Q45
