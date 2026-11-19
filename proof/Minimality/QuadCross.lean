module

public import Minimality.OrthoView2
public import Minimality.SilS0XC
public import Minimality.Type24SAT.Facets24
public import Minimality.HiddenCap

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.H21

theorem indep3_of_inner {u w n : ℝ³} (hn : n ≠ 0) (hnu : ⟪n, u⟫ = 0) (hnw : ⟪n, w⟫ = 0)
    {n4 : ℝ³} (hn4w : ⟪n4, w⟫ = 0) (hn4u : ⟪n4, u⟫ < 0)
    {n2 : ℝ³} (hn2w : ⟪n2, w⟫ < 0) :
    LinearIndependent ℝ ![u, w, n] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • u + g 1 • w + g 2 • n = 0 := by
    have h := hg
    rw [Fin.sum_univ_three] at h
    exact h
  have h_dot_n : ⟪n, g 0 • u + g 1 • w + g 2 • n⟫ = 0 := by rw [hsum, inner_zero_right]
  simp only [inner_add_right, inner_smul_right, hnu, hnw, mul_zero, add_zero, zero_add] at h_dot_n
  have hpos : 0 < ⟪n, n⟫ := real_inner_self_pos.2 hn
  have g2_zero : g 2 = 0 := by
    cases mul_eq_zero.mp h_dot_n with
    | inl h => exact h
    | inr h => exact False.elim (hpos.ne' h)
  rw [g2_zero, zero_smul, add_zero] at hsum
  have h_dot_4 : ⟪n4, g 0 • u + g 1 • w⟫ = 0 := by rw [hsum, inner_zero_right]
  simp only [inner_add_right, inner_smul_right, hn4w, mul_zero, add_zero] at h_dot_4
  have g0_zero : g 0 = 0 := by
    cases mul_eq_zero.mp h_dot_4 with
    | inl h => exact h
    | inr h => exact False.elim (hn4u.ne (by rw [h]))
  rw [g0_zero, zero_smul, zero_add] at hsum
  have h_dot_2 : ⟪n2, g 1 • w⟫ = 0 := by rw [hsum, inner_zero_right]
  simp only [inner_smul_right] at h_dot_2
  have g1_zero : g 1 = 0 := by
    cases mul_eq_zero.mp h_dot_2 with
    | inl h => exact h
    | inr h => exact False.elim (hn2w.ne (by rw [h]))
  intro i
  fin_cases i
  · exact g0_zero
  · exact g1_zero
  · exact g2_zero

/-- **Crossing of diagonals in a planar quadrilateral from parameter signs.**
Given four points `x0, x3, x4, x5` in `ℝ³` such that `x5 - x0 = al • (x3 - x0) + be • (x4 - x0)`
with `0 < al`, `be < 0`, and `al + be < 1`, the diagonals `[x0, x3]` and `[x4, x5]` cross:
there exist `s, t ∈ (0, 1)` such that `(1 - s) • x0 + s • x3 = (1 - t) • x4 + t • x5`. -/
theorem quad_cross_of_param (x0 x3 x4 x5 : ℝ³) {al be : ℝ}
    (hal : 0 < al) (hbe : be < 0) (hsum : al + be < 1)
    (hparam : x5 - x0 = al • (x3 - x0) + be • (x4 - x0)) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (1 - s) • x0 + s • x3 = (1 - t) • x4 + t • x5 := by
  have hden : 0 < 1 - be := by linarith
  set t := 1 / (1 - be)
  set s := al / (1 - be)
  have ht0 : 0 < t := div_pos one_pos hden
  have ht1 : t < 1 := by
    rw [div_lt_one hden]
    linarith
  have hs0 : 0 < s := div_pos hal hden
  have hs1 : s < 1 := by
    rw [div_lt_one hden]
    linarith
  refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hparam_i : x5 i - x0 i = al * (x3 i - x0 i) + be * (x4 i - x0 i) := by
    have := congr_arg (fun (v : ℝ³) => v i) hparam
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    exact this
  have hx5_i : x5 i = (x5 i - x0 i) + x0 i := by ring
  rw [hx5_i, hparam_i]
  dsimp [s, t]
  have e : (1 - al / (1 - be)) * x0 i + al / (1 - be) * x3 i =
      (1 - 1 / (1 - be)) * x4 i +
        1 / (1 - be) * (al * (x3 i - x0 i) + be * (x4 i - x0 i) + x0 i) := by
    field_simp
    ring
  exact e

/-- **Same-side conditions for edge 43 from facet 8 (346).**
Facet 8 vanishes on vertices 3 and 4, and is strictly negative at vertices 0 and 5. -/
theorem type24_edge43_sameside {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    F.f 8 (x 4) = 0 ∧ F.f 8 (x 3) = 0 ∧ F.f 8 (x 0) < 0 ∧ F.f 8 (x 5) < 0 := by
  refine ⟨F.zero 8 4 (by decide), F.zero 8 3 (by decide),
          F.neg 8 0 (by decide), F.neg 8 5 (by decide)⟩

/-- **Same-side conditions for edge 35 from facet 6 (235).**
Facet 6 vanishes on vertices 3 and 5, and is strictly negative at vertices 0 and 4. -/
theorem type24_edge35_sameside {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    F.f 6 (x 3) = 0 ∧ F.f 6 (x 5) = 0 ∧ F.f 6 (x 0) < 0 ∧ F.f 6 (x 4) < 0 := by
  refine ⟨F.zero 6 3 (by decide), F.zero 6 5 (by decide),
          F.neg 6 0 (by decide), F.neg 6 4 (by decide)⟩

/-- **Same-side conditions for edge 50 from facet 2 (025).**
Facet 2 vanishes on vertices 0 and 5, and is strictly negative at vertices 3 and 4. -/
theorem type24_edge50_sameside {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    F.f 2 (x 5) = 0 ∧ F.f 2 (x 0) = 0 ∧ F.f 2 (x 3) < 0 ∧ F.f 2 (x 4) < 0 := by
  refine ⟨F.zero 2 5 (by decide), F.zero 2 0 (by decide),
          F.neg 2 3 (by decide), F.neg 2 4 (by decide)⟩

/-- **Same-side conditions for edge 04 from facet 4 (046).**
Facet 4 vanishes on vertices 0 and 4, and is strictly negative at vertices 3 and 5. -/
theorem type24_edge04_sameside {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    F.f 4 (x 0) = 0 ∧ F.f 4 (x 4) = 0 ∧ F.f 4 (x 3) < 0 ∧ F.f 4 (x 5) < 0 := by
  refine ⟨F.zero 4 0 (by decide), F.zero 4 4 (by decide),
          F.neg 4 3 (by decide), F.neg 4 5 (by decide)⟩

/-- **Type 24 quad coplanarity from facet 3 (0345).** -/
theorem type24_quad_coplanar {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    ⟪F.N 3, x 3 - x 0⟫ = 0 ∧ ⟪F.N 3, x 4 - x 0⟫ = 0 ∧ ⟪F.N 3, x 5 - x 0⟫ = 0 := by
  have z0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have z3 : F.f 3 (x 3) = 0 := F.zero 3 3 (by decide)
  have z4 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have z5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  refine ⟨by rw [F.inner_sub, z3, z0, sub_self],
          by rw [F.inner_sub, z4, z0, sub_self],
          by rw [F.inner_sub, z5, z0, sub_self]⟩

/-- **Planar parametrization of vertex 5 in the basis `x 3 - x 0, x 4 - x 0`.**
Vertices 0, 3, 4, 5 all lie on facet 3 (0345), and the vectors `x 3 - x 0` and `x 4 - x 0`
are linearly independent within the plane of facet 3. -/
theorem type24_param {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    ∃ al be : ℝ, x 5 - x 0 = al • (x 3 - x 0) + be • (x 4 - x 0) := by
  set u := x 3 - x 0
  set w := x 4 - x 0
  set v := x 5 - x 0
  set n := F.N 3
  have hn_ne : n ≠ 0 := by
    intro h0
    have hdot : ⟪n, x 1 - x 0⟫ = 0 := by rw [h0, inner_zero_left]
    have hsub : ⟪n, x 1 - x 0⟫ = F.f 3 (x 1) - F.f 3 (x 0) := by rw [F.inner_sub]
    have z0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
    have n1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    rw [z0, sub_zero] at hsub
    linarith [hdot, hsub, n1]
  obtain ⟨hnu, hnw, hnv⟩ := type24_quad_coplanar F
  have hn4w : ⟪F.N 4, w⟫ = 0 := by
    rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
  have hn4u : ⟪F.N 4, u⟫ < 0 := by
    rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 3 (by decide)
  have hn2w : ⟪F.N 2, w⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide), sub_zero]
    exact F.neg 2 4 (by decide)
  have hli : LinearIndependent ℝ ![u, w, n] :=
    indep3_of_inner hn_ne hnu hnw hn4w hn4u hn2w
  obtain ⟨x₁, x₂, x₃, hx⟩ := span_of_indep3 hli v
  have h_dot_n : ⟪n, v⟫ = ⟪n, x₁ • u + x₂ • w + x₃ • n⟫ := by rw [hx]
  rw [hnv, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, hnu, hnw] at h_dot_n
  have hpos : 0 < ⟪n, n⟫ := real_inner_self_pos.2 hn_ne
  have h_mul : x₃ * ⟪n, n⟫ = 0 := by linarith [h_dot_n]
  have x3_zero : x₃ = 0 := by
    cases mul_eq_zero.mp h_mul with
    | inl h => exact h
    | inr h => exact False.elim (hpos.ne' h)
  rw [x3_zero, zero_smul, add_zero] at hx
  exact ⟨x₁, x₂, hx⟩

/-- **Parameter sign derivation from the facet normals and values.**
From a planar representation `x 5 - x 0 = al • (x 3 - x 0) + be • (x 4 - x 0)`,
the facet inequalities of type 24 force `0 < al`, `be < 0`, and `al + be < 1`. -/
theorem type24_param_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x)
    {al be : ℝ} (hparam : x 5 - x 0 = al • (x 3 - x 0) + be • (x 4 - x 0))
    (h_n04 : ⟪F.N 4, x 3 - x 0⟫ < 0)
    (h_n50_w : ⟪F.N 2, x 4 - x 0⟫ < 0)
    (h_n43_u : 0 < ⟪F.N 8, x 3 - x 0⟫) :
    0 < al ∧ be < 0 ∧ al + be < 1 := by
  have e4 : ⟪F.N 4, x 4 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
  have h5_4 : ⟪F.N 4, x 5 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 5 (by decide)
  have hal : 0 < al := by
    have h_dot : ⟪F.N 4, x 5 - x 0⟫ = al * ⟪F.N 4, x 3 - x 0⟫ := by
      rw [hparam, inner_add_right, inner_smul_right, inner_smul_right, e4, mul_zero, add_zero]
    rw [h_dot] at h5_4
    by_contra! hal_le
    have : 0 ≤ al * ⟪F.N 4, x 3 - x 0⟫ := mul_nonneg_of_nonpos_of_nonpos hal_le h_n04.le
    linarith
  have e2 : ⟪F.N 2, x 5 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have h3_2 : ⟪F.N 2, x 3 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide), sub_zero]
    exact F.neg 2 3 (by decide)
  have hbe : be < 0 := by
    have h_dot : 0 = al * ⟪F.N 2, x 3 - x 0⟫ + be * ⟪F.N 2, x 4 - x 0⟫ := by
      have := e2.symm
      rwa [hparam, inner_add_right, inner_smul_right, inner_smul_right] at this
    have h1 : al * ⟪F.N 2, x 3 - x 0⟫ < 0 := mul_neg_of_pos_of_neg hal h3_2
    have h2 : 0 < be * ⟪F.N 2, x 4 - x 0⟫ := by linarith
    by_contra! hbe_nonneg
    have : be * ⟪F.N 2, x 4 - x 0⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbe_nonneg h_n50_w.le
    linarith
  have e8 : ⟪F.N 8, x 4 - x 3⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 3 (by decide), sub_self]
  have e8_eq : ⟪F.N 8, x 4 - x 0⟫ = ⟪F.N 8, x 3 - x 0⟫ := by
    have : x 4 - x 0 = (x 4 - x 3) + (x 3 - x 0) := by abel
    rw [this, inner_add_right, e8, zero_add]
  have h5_8 : ⟪F.N 8, x 5 - x 0⟫ < ⟪F.N 8, x 3 - x 0⟫ := by
    rw [F.inner_sub, F.inner_sub]
    have z3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
    have n5 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
    linarith
  have hsum : al + be < 1 := by
    have h_dot : ⟪F.N 8, x 5 - x 0⟫ = (al + be) * ⟪F.N 8, x 3 - x 0⟫ := by
      rw [hparam, inner_add_right, inner_smul_right, inner_smul_right, e8_eq, ← add_mul]
    rw [h_dot] at h5_8
    by_contra! hsum_ge
    have : 1 * ⟪F.N 8, x 3 - x 0⟫ ≤ (al + be) * ⟪F.N 8, x 3 - x 0⟫ :=
      mul_le_mul_of_nonneg_right hsum_ge h_n43_u.le
    linarith
  exact ⟨hal, hbe, hsum⟩

/-- Rim cycle `0 4 3 5` for the EVVV orthocentre view of type 24. -/
def c0435 : ZMod 4 → Fin 7 := ![0, 4, 3, 5]

theorem inj_c0435 : Function.Injective c0435 := by decide

/-- **Type 24 Quad Crossing for `isRupert_of_orthocentre_evvv`.**
For `c0435 = (0, 4, 3, 5)`, the diagonals `c 0 - c 2` (0 to 3)
and `c 1 - c 3` (4 to 5) cross strictly:
there exist `s, t ∈ (0, 1)` with `(1 - s) • x (c 0) + s • x (c 2) = (1 - t) • x (c 1) + t • x (c 3)`. -/
theorem type24_quad_cross (x : Fin 7 → ℝ³)
    (F : S0xFac 9 T24.SAT.s0x_S24 x) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (1 - s) • x (c0435 0) + s • x (c0435 2) = (1 - t) • x (c0435 1) + t • x (c0435 3) := by
  obtain ⟨al, be, hparam⟩ := type24_param F
  have h_n04 : ⟪F.N 4, x 3 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 3 (by decide)
  have h_n50_w : ⟪F.N 2, x 4 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide), sub_zero]
    exact F.neg 2 4 (by decide)
  have h_n43_u : 0 < ⟪F.N 8, x 3 - x 0⟫ := by
    rw [F.inner_sub, F.zero 8 3 (by decide)]
    have := F.neg 8 0 (by decide)
    linarith
  obtain ⟨hal, hbe, hsum⟩ := type24_param_signs F hparam h_n04 h_n50_w h_n43_u
  obtain ⟨s, t, hs0, hs1, ht0, ht1, hcross⟩ := quad_cross_of_param (x 0) (x 3) (x 4) (x 5)
    hal hbe hsum hparam
  refine ⟨s, t, hs0, hs1.le, ht0.le, ht1.le, hcross⟩

/-- **Theorem P, EVVV case for Type 24.**
The EVVV case of Theorem P with the quad diagonal crossing hypothesis `hX` discharged
from the facet data `F`. -/
theorem isRupert_of_orthocentre_evvv_t24 {k : ℕ} {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x)
    (hx : Function.Injective x) {U Dn : Finset (Fin 9)}
    (hcyc : S0xCycUD T24.SAT.s0x_S24 c0435 U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin 7 → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (h01 : (∑ e, y 0 e) < ∑ e, y 4 e) (h03 : (∑ e, y 0 e) < ∑ e, y 5 e)
    (d : ℝ³)
    (d1 : (∑ e, y 3 e) = ∑ e, y 4 e → 0 < ⟪x 3 - x 4, d⟫)
    (d3 : (∑ e, y 3 e) = ∑ e, y 5 e → 0 < ⟪x 3 - x 5, d⟫) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨s, t, hs, hs1, ht, ht1, hX⟩ := type24_quad_cross x F
  exact isRupert_of_orthocentre_evvv F hx inj_c0435 hcyc hu p v y hxy hv h01 h03 hs hs1 ht ht1 hX d d1 d3

end Minimality.H21
