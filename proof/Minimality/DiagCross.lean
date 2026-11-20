module

public import Minimality.RimFromSigns

@[expose] public section

open scoped RealInnerProductSpace

namespace Minimality.T24.Q45

/-- Corner triangle determinant along view `u` for index `i : ZMod 4`. -/
noncomputable def triD (p : ZMod 4 → ℝ³) (u : ℝ³) (i : ZMod 4) : ℝ :=
  det3 (p (i + 1) - p i) (p (i + 2) - p i) u

/-- **Lemma K (Diagonal Crossing Identity, Q45THEOREM24.md 2.4).**
Exact algebraic relation between quad rim corner determinants and depth values along `u`. -/
theorem diagCross_identity (p : ZMod 4 → ℝ³) (u : ℝ³) :
    triD p u 1 * ⟪p 0, u⟫ + triD p u 3 * ⟪p 2, u⟫ - triD p u 2 * ⟪p 1, u⟫ - triD p u 0 * ⟪p 3, u⟫ =
      det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) * ⟪u, u⟫ := by
  have e : ∀ a b : ℝ³, ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  have h0 : (0 : ZMod 4) + 1 = 1 := rfl
  have h02 : (0 : ZMod 4) + 2 = 2 := rfl
  have h1 : (1 : ZMod 4) + 1 = 2 := rfl
  have h12 : (1 : ZMod 4) + 2 = 3 := rfl
  have h2 : (2 : ZMod 4) + 1 = 3 := rfl
  have h22 : (2 : ZMod 4) + 2 = 0 := rfl
  have h3 : (3 : ZMod 4) + 1 = 0 := rfl
  have h32 : (3 : ZMod 4) + 2 = 1 := rfl
  simp only [triD, h0, h02, h1, h12, h2, h22, h3, h32, det3_expand, e, PiLp.sub_apply]
  ring

/-- Weight balance between opposite corner pairs of any quad rim. -/
theorem diagCross_weights (p : ZMod 4 → ℝ³) (u : ℝ³) :
    triD p u 1 + triD p u 3 = triD p u 0 + triD p u 2 := by
  have h0 : (0 : ZMod 4) + 1 = 1 := rfl
  have h02 : (0 : ZMod 4) + 2 = 2 := rfl
  have h1 : (1 : ZMod 4) + 1 = 2 := rfl
  have h12 : (1 : ZMod 4) + 2 = 3 := rfl
  have h2 : (2 : ZMod 4) + 1 = 3 := rfl
  have h22 : (2 : ZMod 4) + 2 = 0 := rfl
  have h3 : (3 : ZMod 4) + 1 = 0 := rfl
  have h32 : (3 : ZMod 4) + 2 = 1 := rfl
  simp only [triD, h0, h02, h1, h12, h2, h22, h3, h32, det3_expand, PiLp.sub_apply]
  ring

/-- When `ρ * κ < 0`, pair `{1, 3}` cannot be completely below pair `{0, 2}`. -/
theorem diagCross_not_high (p : ZMod 4 → ℝ³) (u : ℝ³) {ρ : ℝ}
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0) :
    ¬ (max ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ min ⟪p 0, u⟫ ⟪p 2, u⟫) := by
  intro hle
  have hu_ne : u ≠ 0 := by
    intro hu
    have h0 := hcyc 0
    rw [hu] at h0
    have hz : triD p 0 0 = 0 := by
      simp only [triD, det3_expand, PiLp.sub_apply, PiLp.zero_apply]
      ring
    rw [hz, mul_zero] at h0
    exact lt_irrefl 0 h0
  have hu_sq : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu_ne
  have h_rhs_neg : (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ < 0 :=
    mul_neg_of_neg_of_pos hk hu_sq
  have hid := diagCross_identity p u
  have hw := diagCross_weights p u
  set w0 := ρ * triD p u 0
  set w1 := ρ * triD p u 1
  set w2 := ρ * triD p u 2
  set w3 := ρ * triD p u 3
  have hw0 : 0 < w0 := hcyc 0
  have hw1 : 0 < w1 := hcyc 1
  have hw2 : 0 < w2 := hcyc 2
  have hw3 : 0 < w3 := hcyc 3
  have h_rho_id : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ =
      (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ := by
    calc
      w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ =
        ρ * (triD p u 1 * ⟪p 0, u⟫ + triD p u 3 * ⟪p 2, u⟫ - triD p u 2 * ⟪p 1, u⟫ - triD p u 0 * ⟪p 3, u⟫) := by ring
      _ = ρ * (det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) * ⟪u, u⟫) := by rw [hid]
      _ = (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ := by ring
  have h_rho_w : w1 + w3 = w0 + w2 := by
    dsimp [w0, w1, w2, w3]
    linear_combination ρ * hw
  have h1_le : ⟪p 1, u⟫ ≤ max ⟪p 1, u⟫ ⟪p 3, u⟫ := le_max_left _ _
  have h3_le : ⟪p 3, u⟫ ≤ max ⟪p 1, u⟫ ⟪p 3, u⟫ := le_max_right _ _
  have min_le_0 : min ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ ⟪p 0, u⟫ := min_le_left _ _
  have min_le_2 : min ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ ⟪p 2, u⟫ := min_le_right _ _
  set M := max ⟪p 1, u⟫ ⟪p 3, u⟫
  set m := min ⟪p 0, u⟫ ⟪p 2, u⟫
  have hm_le : M ≤ m := hle
  have h_pos : 0 ≤ (w0 + w2) * (m - M) :=
    mul_nonneg (by linarith [hw0, hw2]) (by linarith [hm_le])
  have h_left : (w0 + w2) * m ≤ w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ := by
    rw [← h_rho_w]
    nlinarith [min_le_0, min_le_2, hw1, hw3]
  have h_right : w2 * ⟪p 1, u⟫ + w0 * ⟪p 3, u⟫ ≤ (w0 + w2) * M := by
    nlinarith [h1_le, h3_le, hw0, hw2]
  have h_ge : 0 ≤ w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ := by
    linarith [h_pos, h_left, h_right]
  linarith [h_rho_id, h_rhs_neg, h_ge]

/-- Mirror: when `0 < ρ * κ`, pair `{0, 2}` cannot be completely below pair `{1, 3}`. -/
theorem diagCross_not_low (p : ZMod 4 → ℝ³) (u : ℝ³) {ρ : ℝ}
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) :
    ¬ (max ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ min ⟪p 1, u⟫ ⟪p 3, u⟫) := by
  intro hle
  have hu_ne : u ≠ 0 := by
    intro hu
    have h0 := hcyc 0
    rw [hu] at h0
    have hz : triD p 0 0 = 0 := by
      simp only [triD, det3_expand, PiLp.sub_apply, PiLp.zero_apply]
      ring
    rw [hz, mul_zero] at h0
    exact lt_irrefl 0 h0
  have hu_sq : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu_ne
  have h_rhs_pos : 0 < (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ :=
    mul_pos hk hu_sq
  have hid := diagCross_identity p u
  have hw := diagCross_weights p u
  set w0 := ρ * triD p u 0
  set w1 := ρ * triD p u 1
  set w2 := ρ * triD p u 2
  set w3 := ρ * triD p u 3
  have hw0 : 0 < w0 := hcyc 0
  have hw1 : 0 < w1 := hcyc 1
  have hw2 : 0 < w2 := hcyc 2
  have hw3 : 0 < w3 := hcyc 3
  have h_rho_id : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ =
      (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ := by
    calc
      w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ =
        ρ * (triD p u 1 * ⟪p 0, u⟫ + triD p u 3 * ⟪p 2, u⟫ - triD p u 2 * ⟪p 1, u⟫ - triD p u 0 * ⟪p 3, u⟫) := by ring
      _ = ρ * (det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) * ⟪u, u⟫) := by rw [hid]
      _ = (ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) * ⟪u, u⟫ := by ring
  have h_rho_w : w1 + w3 = w0 + w2 := by
    dsimp [w0, w1, w2, w3]
    linear_combination ρ * hw
  have h0_le : ⟪p 0, u⟫ ≤ max ⟪p 0, u⟫ ⟪p 2, u⟫ := le_max_left _ _
  have h2_le : ⟪p 2, u⟫ ≤ max ⟪p 0, u⟫ ⟪p 2, u⟫ := le_max_right _ _
  have min_le_1 : min ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ ⟪p 1, u⟫ := min_le_left _ _
  have min_le_3 : min ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ ⟪p 3, u⟫ := min_le_right _ _
  set M := max ⟪p 0, u⟫ ⟪p 2, u⟫
  set m := min ⟪p 1, u⟫ ⟪p 3, u⟫
  have hm_le : M ≤ m := hle
  have h_nonpos : (w0 + w2) * (M - m) ≤ 0 := by
    have : (w0 + w2) * (m - M) ≥ 0 := mul_nonneg (by linarith [hw0, hw2]) (by linarith [hm_le])
    linarith
  have h_left : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ ≤ (w0 + w2) * M := by
    rw [← h_rho_w]
    nlinarith [h0_le, h2_le, hw1, hw3]
  have h_right : (w0 + w2) * m ≤ w2 * ⟪p 1, u⟫ + w0 * ⟪p 3, u⟫ := by
    nlinarith [min_le_1, min_le_3, hw0, hw2]
  have h_le : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ ≤ 0 := by
    linarith [h_nonpos, h_left, h_right]
  linarith [h_rho_id, h_rhs_pos, h_le]

/-- Planar case `κ = 0`: neither pair can strictly alternate below the other. -/
theorem diagCross_zero (p : ZMod 4 → ℝ³) (u : ℝ³) {ρ : ℝ}
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) = 0) :
    ¬ (max ⟪p 1, u⟫ ⟪p 3, u⟫ < min ⟪p 0, u⟫ ⟪p 2, u⟫) ∧
    ¬ (max ⟪p 0, u⟫ ⟪p 2, u⟫ < min ⟪p 1, u⟫ ⟪p 3, u⟫) := by
  have hid := diagCross_identity p u
  have hw := diagCross_weights p u
  set w0 := ρ * triD p u 0
  set w1 := ρ * triD p u 1
  set w2 := ρ * triD p u 2
  set w3 := ρ * triD p u 3
  have hw0 : 0 < w0 := hcyc 0
  have hw1 : 0 < w1 := hcyc 1
  have hw2 : 0 < w2 := hcyc 2
  have hw3 : 0 < w3 := hcyc 3
  have h_rho_id : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ = 0 := by
    calc
      w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ =
        ρ * (triD p u 1 * ⟪p 0, u⟫ + triD p u 3 * ⟪p 2, u⟫ - triD p u 2 * ⟪p 1, u⟫ - triD p u 0 * ⟪p 3, u⟫) := by ring
      _ = ρ * (det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) * ⟪u, u⟫) := by rw [hid]
      _ = 0 := by rw [hk, zero_mul, mul_zero]
  have h_rho_w : w1 + w3 = w0 + w2 := by
    dsimp [w0, w1, w2, w3]
    linear_combination ρ * hw
  constructor
  · intro hlt
    have h1_le : ⟪p 1, u⟫ ≤ max ⟪p 1, u⟫ ⟪p 3, u⟫ := le_max_left _ _
    have h3_le : ⟪p 3, u⟫ ≤ max ⟪p 1, u⟫ ⟪p 3, u⟫ := le_max_right _ _
    have min_le_0 : min ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ ⟪p 0, u⟫ := min_le_left _ _
    have min_le_2 : min ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ ⟪p 2, u⟫ := min_le_right _ _
    set M := max ⟪p 1, u⟫ ⟪p 3, u⟫
    set m := min ⟪p 0, u⟫ ⟪p 2, u⟫
    have hm_lt : M < m := hlt
    have h_pos : 0 < (w0 + w2) * (m - M) :=
      mul_pos (by linarith [hw0, hw2]) (by linarith [hm_lt])
    have h_left : (w0 + w2) * m ≤ w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ := by
      rw [← h_rho_w]
      nlinarith [min_le_0, min_le_2, hw1, hw3]
    have h_right : w2 * ⟪p 1, u⟫ + w0 * ⟪p 3, u⟫ ≤ (w0 + w2) * M := by
      nlinarith [h1_le, h3_le, hw0, hw2]
    have h_gt : 0 < w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ := by
      linarith [h_pos, h_left, h_right]
    linarith [h_rho_id, h_gt]
  · intro hlt
    have h0_le : ⟪p 0, u⟫ ≤ max ⟪p 0, u⟫ ⟪p 2, u⟫ := le_max_left _ _
    have h2_le : ⟪p 2, u⟫ ≤ max ⟪p 0, u⟫ ⟪p 2, u⟫ := le_max_right _ _
    have min_le_1 : min ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ ⟪p 1, u⟫ := min_le_left _ _
    have min_le_3 : min ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ ⟪p 3, u⟫ := min_le_right _ _
    set M := max ⟪p 0, u⟫ ⟪p 2, u⟫
    set m := min ⟪p 1, u⟫ ⟪p 3, u⟫
    have hm_lt : M < m := hlt
    have h_pos : 0 < (w0 + w2) * (m - M) :=
      mul_pos (by linarith [hw0, hw2]) (by linarith [hm_lt])
    have h_left : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ ≤ (w0 + w2) * M := by
      rw [← h_rho_w]
      nlinarith [h0_le, h2_le, hw1, hw3]
    have h_right : (w0 + w2) * m ≤ w2 * ⟪p 1, u⟫ + w0 * ⟪p 3, u⟫ := by
      nlinarith [min_le_1, min_le_3, hw0, hw2]
    have h_lt : w1 * ⟪p 0, u⟫ + w3 * ⟪p 2, u⟫ - w2 * ⟪p 1, u⟫ - w0 * ⟪p 3, u⟫ < 0 := by
      linarith [h_pos, h_left, h_right]
    linarith [h_rho_id, h_lt]

end Minimality.T24.Q45
