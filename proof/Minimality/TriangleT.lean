module

public import Minimality.TheoremP24

@[expose] public section

open scoped RealInnerProductSpace BigOperators
open Minimality.RimCell

namespace Minimality.T24.Hexagon

noncomputable section

variable {x : Fin 7 → ℝ³}

/-- The three Cevian ratios of Type 24 in corner coordinates at vertex 1. -/
def theta0 (y : Fin 7 → Fin 3 → ℝ) : ℝ :=
  y 3 0 / ((∑ e, y 3 e) - 1)

def theta2 (y : Fin 7 → Fin 3 → ℝ) : ℝ :=
  y 4 1 / ((∑ e, y 4 e) - 1)

def theta6 (y : Fin 7 → Fin 3 → ℝ) : ℝ :=
  y 5 2 / ((∑ e, y 5 e) - 1)

/-- The Cevian arrangement invariant `Θ(y) = θ₀ + θ₂ + θ₆`. -/
def ThetaInv (y : Fin 7 → Fin 3 → ℝ) : ℝ :=
  theta0 y + theta2 y + theta6 y

/-- The standard 2-simplex in the corner view cone. -/
def Simplex2 : Set (Fin 3 → ℝ) :=
  {c | (∀ e, 0 ≤ c e) ∧ ∑ e, c e = 1}

/-- The central triangle `T`: views in `Simplex2` where all three cap facets
`{2, 3, 6}`, `{0, 4, 6}`, `{0, 2, 5}` are strictly back. -/
def TriangleT (y : Fin 7 → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {c ∈ Simplex2 | theta0 y < c 0 ∧ theta2 y < c 1 ∧ theta6 y < c 2}

/-- **Non-emptiness of Triangle T.**
`TriangleT y` is non-empty if and only if `ThetaInv y < 1`. -/
theorem triangleT_nonempty_iff (y : Fin 7 → Fin 3 → ℝ)
    (h0 : 0 < theta0 y) (h2 : 0 < theta2 y) (h6 : 0 < theta6 y) :
    (TriangleT y).Nonempty ↔ ThetaInv y < 1 := by
  constructor
  · rintro ⟨c, ⟨⟨hc_nonneg, hsum⟩, ⟨hc0, hc1, hc2⟩⟩⟩
    have hsum3 : c 0 + c 1 + c 2 = 1 := by
      rw [← hsum, Fin.sum_univ_three]
    dsimp [ThetaInv]
    linarith
  · intro hT
    dsimp [ThetaInv] at hT
    set δ := (1 - (theta0 y + theta2 y + theta6 y)) / 3
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    set c : Fin 3 → ℝ := ![theta0 y + δ, theta2 y + δ, theta6 y + δ]
    refine ⟨c, ?_⟩
    dsimp [TriangleT, Simplex2]
    have hc0 : c 0 = theta0 y + δ := rfl
    have hc1 : c 1 = theta2 y + δ := rfl
    have hc2 : c 2 = theta6 y + δ := rfl
    have hsum : ∑ e, c e = 1 := by
      rw [Fin.sum_univ_three, hc0, hc1, hc2]
      dsimp [δ]
      ring
    have hpos0 : 0 ≤ c 0 := by rw [hc0]; linarith
    have hpos1 : 0 ≤ c 1 := by rw [hc1]; linarith
    have hpos2 : 0 ≤ c 2 := by rw [hc2]; linarith
    have hnonneg : ∀ e, 0 ≤ c e := by
      intro e
      fin_cases e
      · exact hpos0
      · exact hpos1
      · exact hpos2
    refine ⟨⟨hnonneg, hsum⟩, ?_, ?_, ?_⟩
    · rw [hc0]; linarith
    · rw [hc1]; linarith
    · rw [hc2]; linarith

/-- **Facet 7 ({2, 3, 6}) Backness Condition.**
Under `c ∈ Simplex2` with `u = ∑ e, c e • v e`, Facet 7 is strictly back
(`⟪F.N 7, u⟫ < 0`) if and only if `theta0 y < c 0`. -/
theorem facet7_back_iff (F : Minimality.H21.S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (c : Fin 3 → ℝ) (hc_sum : ∑ e, c e = 1) :
    ⟪F.N 7, ∑ e, c e • v e⟫ < 0 ↔ theta0 y < c 0 := by
  have he7 := Minimality.T24.TheoremP.s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 7 3
  have hz72 : F.f 7 (x 2) = 0 := F.zero 7 2 (by decide)
  have hz73 : F.f 7 (x 3) = 0 := F.zero 7 3 (by decide)
  have hz76 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have hn71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have hn70 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  rw [hz72, hz73, hz76] at he7
  simp only [zero_sub] at he7
  have hlin : ⟪F.N 7, ∑ e, c e • v e⟫ = c 0 * F.f 7 (x 0) - F.f 7 (x 1) := by
    have hsum : ∑ e, c e • v e = c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1) := by
      rw [Fin.sum_univ_three, hv0, hv1, hv2]
    rw [hsum]
    simp only [inner_add_right, inner_smul_right]
    rw [← F.hN 7 (x 0) (x 1), ← F.hN 7 (x 2) (x 1), ← F.hN 7 (x 6) (x 1)]
    rw [hz72, hz76]
    have hc_sum3 : c 0 + c 1 + c 2 = 1 := by rw [← hc_sum, Fin.sum_univ_three]
    calc c 0 * (F.f 7 (x 0) - F.f 7 (x 1)) + c 1 * (0 - F.f 7 (x 1)) + c 2 * (0 - F.f 7 (x 1))
      _ = c 0 * F.f 7 (x 0) - (c 0 + c 1 + c 2) * F.f 7 (x 1) := by ring
      _ = c 0 * F.f 7 (x 0) - 1 * F.f 7 (x 1) := by rw [hc_sum3]
      _ = c 0 * F.f 7 (x 0) - F.f 7 (x 1) := by ring
  rw [hlin]
  have hV3 := Minimality.T24.TheoremP.type24_sigma3_gt_one F p v y hxy hp hv0 hv1 hv2
  have hS_pos : 0 < (∑ e, y 3 e) - 1 := by linarith
  have hE3 : ∑ e, y 3 e = y 3 0 + y 3 1 + y 3 2 := by rw [Fin.sum_univ_three]
  have hrel : y 3 0 * F.f 7 (x 0) = ((∑ e, y 3 e) - 1) * F.f 7 (x 1) := by
    rw [hE3]
    linarith
  have hy30_pos : 0 < y 3 0 := by
    have hprod : ((∑ e, y 3 e) - 1) * F.f 7 (x 1) < 0 := mul_neg_of_pos_of_neg hS_pos hn71
    have hprod2 : y 3 0 * F.f 7 (x 0) < 0 := by rwa [hrel]
    exact pos_of_mul_neg_left hprod2 hn70.le
  dsimp [theta0]
  have hident : (c 0 * ((∑ e, y 3 e) - 1) - y 3 0) * F.f 7 (x 1) =
      y 3 0 * (c 0 * F.f 7 (x 0) - F.f 7 (x 1)) := by
    calc (c 0 * ((∑ e, y 3 e) - 1) - y 3 0) * F.f 7 (x 1)
      _ = c 0 * (((∑ e, y 3 e) - 1) * F.f 7 (x 1)) - y 3 0 * F.f 7 (x 1) := by ring
      _ = c 0 * (y 3 0 * F.f 7 (x 0)) - y 3 0 * F.f 7 (x 1) := by rw [hrel]
      _ = y 3 0 * (c 0 * F.f 7 (x 0) - F.f 7 (x 1)) := by ring
  constructor
  · intro hlt
    have h_rhs_neg : y 3 0 * (c 0 * F.f 7 (x 0) - F.f 7 (x 1)) < 0 :=
      mul_neg_of_pos_of_neg hy30_pos hlt
    rw [← hident] at h_rhs_neg
    have h_factor_pos : 0 < c 0 * ((∑ e, y 3 e) - 1) - y 3 0 :=
      pos_of_mul_neg_left h_rhs_neg hn71.le
    have h_step : y 3 0 < c 0 * ((∑ e, y 3 e) - 1) := by linarith
    exact (div_lt_iff₀ hS_pos).2 h_step
  · intro hgt
    have h_step : y 3 0 < c 0 * ((∑ e, y 3 e) - 1) := (div_lt_iff₀ hS_pos).1 hgt
    have h_factor_pos : 0 < c 0 * ((∑ e, y 3 e) - 1) - y 3 0 := by linarith
    have h_lhs_neg : (c 0 * ((∑ e, y 3 e) - 1) - y 3 0) * F.f 7 (x 1) < 0 :=
      mul_neg_of_pos_of_neg h_factor_pos hn71
    rw [hident] at h_lhs_neg
    exact neg_of_mul_neg_right h_lhs_neg hy30_pos.le

/-- **Facet 4 ({0, 4, 6}) Backness Condition.**
Under `c ∈ Simplex2` with `u = ∑ e, c e • v e`, Facet 4 is strictly back
(`⟪F.N 4, u⟫ < 0`) if and only if `theta2 y < c 1`. -/
theorem facet4_back_iff (F : Minimality.H21.S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (c : Fin 3 → ℝ) (hc_sum : ∑ e, c e = 1) :
    ⟪F.N 4, ∑ e, c e • v e⟫ < 0 ↔ theta2 y < c 1 := by
  have he4 := Minimality.T24.TheoremP.s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 4 4
  have hz40 : F.f 4 (x 0) = 0 := F.zero 4 0 (by decide)
  have hz44 : F.f 4 (x 4) = 0 := F.zero 4 4 (by decide)
  have hz46 : F.f 4 (x 6) = 0 := F.zero 4 6 (by decide)
  have hn41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have hn42 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  rw [hz40, hz44, hz46] at he4
  simp only [zero_sub] at he4
  have hlin : ⟪F.N 4, ∑ e, c e • v e⟫ = c 1 * F.f 4 (x 2) - F.f 4 (x 1) := by
    have hsum : ∑ e, c e • v e = c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1) := by
      rw [Fin.sum_univ_three, hv0, hv1, hv2]
    rw [hsum]
    simp only [inner_add_right, inner_smul_right]
    rw [← F.hN 4 (x 0) (x 1), ← F.hN 4 (x 2) (x 1), ← F.hN 4 (x 6) (x 1)]
    rw [hz40, hz46]
    have hc_sum3 : c 0 + c 1 + c 2 = 1 := by rw [← hc_sum, Fin.sum_univ_three]
    calc c 0 * (0 - F.f 4 (x 1)) + c 1 * (F.f 4 (x 2) - F.f 4 (x 1)) + c 2 * (0 - F.f 4 (x 1))
      _ = c 1 * F.f 4 (x 2) - (c 0 + c 1 + c 2) * F.f 4 (x 1) := by ring
      _ = c 1 * F.f 4 (x 2) - 1 * F.f 4 (x 1) := by rw [hc_sum3]
      _ = c 1 * F.f 4 (x 2) - F.f 4 (x 1) := by ring
  rw [hlin]
  have hV4 := Minimality.T24.TheoremP.type24_sigma4_gt_one F p v y hxy hp hv0 hv1 hv2
  have hS_pos : 0 < (∑ e, y 4 e) - 1 := by linarith
  have hE4 : ∑ e, y 4 e = y 4 0 + y 4 1 + y 4 2 := by rw [Fin.sum_univ_three]
  have hrel : y 4 1 * F.f 4 (x 2) = ((∑ e, y 4 e) - 1) * F.f 4 (x 1) := by
    rw [hE4]
    linarith
  have hy41_pos : 0 < y 4 1 := by
    have hprod : ((∑ e, y 4 e) - 1) * F.f 4 (x 1) < 0 := mul_neg_of_pos_of_neg hS_pos hn41
    have hprod2 : y 4 1 * F.f 4 (x 2) < 0 := by rwa [hrel]
    exact pos_of_mul_neg_left hprod2 hn42.le
  dsimp [theta2]
  have hident : (c 1 * ((∑ e, y 4 e) - 1) - y 4 1) * F.f 4 (x 1) =
      y 4 1 * (c 1 * F.f 4 (x 2) - F.f 4 (x 1)) := by
    calc (c 1 * ((∑ e, y 4 e) - 1) - y 4 1) * F.f 4 (x 1)
      _ = c 1 * (((∑ e, y 4 e) - 1) * F.f 4 (x 1)) - y 4 1 * F.f 4 (x 1) := by ring
      _ = c 1 * (y 4 1 * F.f 4 (x 2)) - y 4 1 * F.f 4 (x 1) := by rw [hrel]
      _ = y 4 1 * (c 1 * F.f 4 (x 2) - F.f 4 (x 1)) := by ring
  constructor
  · intro hlt
    have h_rhs_neg : y 4 1 * (c 1 * F.f 4 (x 2) - F.f 4 (x 1)) < 0 :=
      mul_neg_of_pos_of_neg hy41_pos hlt
    rw [← hident] at h_rhs_neg
    have h_factor_pos : 0 < c 1 * ((∑ e, y 4 e) - 1) - y 4 1 :=
      pos_of_mul_neg_left h_rhs_neg hn41.le
    have h_step : y 4 1 < c 1 * ((∑ e, y 4 e) - 1) := by linarith
    exact (div_lt_iff₀ hS_pos).2 h_step
  · intro hgt
    have h_step : y 4 1 < c 1 * ((∑ e, y 4 e) - 1) := (div_lt_iff₀ hS_pos).1 hgt
    have h_factor_pos : 0 < c 1 * ((∑ e, y 4 e) - 1) - y 4 1 := by linarith
    have h_lhs_neg : (c 1 * ((∑ e, y 4 e) - 1) - y 4 1) * F.f 4 (x 1) < 0 :=
      mul_neg_of_pos_of_neg h_factor_pos hn41
    rw [hident] at h_lhs_neg
    exact neg_of_mul_neg_right h_lhs_neg hy41_pos.le

/-- **Facet 2 ({0, 2, 5}) Backness Condition.**
Under `c ∈ Simplex2` with `u = ∑ e, c e • v e`, Facet 2 is strictly back
(`⟪F.N 2, u⟫ < 0`) if and only if `theta6 y < c 2`. -/
theorem facet2_back_iff (F : Minimality.H21.S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (c : Fin 3 → ℝ) (hc_sum : ∑ e, c e = 1) :
    ⟪F.N 2, ∑ e, c e • v e⟫ < 0 ↔ theta6 y < c 2 := by
  have he2 := Minimality.T24.TheoremP.s0x_affine_eval F p v y hxy hp hv0 hv1 hv2 2 5
  have hz20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have hz22 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have hz25 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have hn21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have hn26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
  rw [hz20, hz22, hz25] at he2
  simp only [zero_sub] at he2
  have hlin : ⟪F.N 2, ∑ e, c e • v e⟫ = c 2 * F.f 2 (x 6) - F.f 2 (x 1) := by
    have hsum : ∑ e, c e • v e = c 0 • (x 0 - x 1) + c 1 • (x 2 - x 1) + c 2 • (x 6 - x 1) := by
      rw [Fin.sum_univ_three, hv0, hv1, hv2]
    rw [hsum]
    simp only [inner_add_right, inner_smul_right]
    rw [← F.hN 2 (x 0) (x 1), ← F.hN 2 (x 2) (x 1), ← F.hN 2 (x 6) (x 1)]
    rw [hz20, hz22]
    have hc_sum3 : c 0 + c 1 + c 2 = 1 := by rw [← hc_sum, Fin.sum_univ_three]
    calc c 0 * (0 - F.f 2 (x 1)) + c 1 * (0 - F.f 2 (x 1)) + c 2 * (F.f 2 (x 6) - F.f 2 (x 1))
      _ = c 2 * F.f 2 (x 6) - (c 0 + c 1 + c 2) * F.f 2 (x 1) := by ring
      _ = c 2 * F.f 2 (x 6) - 1 * F.f 2 (x 1) := by rw [hc_sum3]
      _ = c 2 * F.f 2 (x 6) - F.f 2 (x 1) := by ring
  rw [hlin]
  have hV5 := Minimality.T24.TheoremP.type24_sigma5_gt_one F p v y hxy hp hv0 hv1 hv2
  have hS_pos : 0 < (∑ e, y 5 e) - 1 := by linarith
  have hE5 : ∑ e, y 5 e = y 5 0 + y 5 1 + y 5 2 := by rw [Fin.sum_univ_three]
  have hrel : y 5 2 * F.f 2 (x 6) = ((∑ e, y 5 e) - 1) * F.f 2 (x 1) := by
    rw [hE5]
    linarith
  have hy52_pos : 0 < y 5 2 := by
    have hprod : ((∑ e, y 5 e) - 1) * F.f 2 (x 1) < 0 := mul_neg_of_pos_of_neg hS_pos hn21
    have hprod2 : y 5 2 * F.f 2 (x 6) < 0 := by rwa [hrel]
    exact pos_of_mul_neg_left hprod2 hn26.le
  dsimp [theta6]
  have hident : (c 2 * ((∑ e, y 5 e) - 1) - y 5 2) * F.f 2 (x 1) =
      y 5 2 * (c 2 * F.f 2 (x 6) - F.f 2 (x 1)) := by
    calc (c 2 * ((∑ e, y 5 e) - 1) - y 5 2) * F.f 2 (x 1)
      _ = c 2 * (((∑ e, y 5 e) - 1) * F.f 2 (x 1)) - y 5 2 * F.f 2 (x 1) := by ring
      _ = c 2 * (y 5 2 * F.f 2 (x 6)) - y 5 2 * F.f 2 (x 1) := by rw [hrel]
      _ = y 5 2 * (c 2 * F.f 2 (x 6) - F.f 2 (x 1)) := by ring
  constructor
  · intro hlt
    have h_rhs_neg : y 5 2 * (c 2 * F.f 2 (x 6) - F.f 2 (x 1)) < 0 :=
      mul_neg_of_pos_of_neg hy52_pos hlt
    rw [← hident] at h_rhs_neg
    have h_factor_pos : 0 < c 2 * ((∑ e, y 5 e) - 1) - y 5 2 :=
      pos_of_mul_neg_left h_rhs_neg hn21.le
    have h_step : y 5 2 < c 2 * ((∑ e, y 5 e) - 1) := by linarith
    exact (div_lt_iff₀ hS_pos).2 h_step
  · intro hgt
    have h_step : y 5 2 < c 2 * ((∑ e, y 5 e) - 1) := (div_lt_iff₀ hS_pos).1 hgt
    have h_factor_pos : 0 < c 2 * ((∑ e, y 5 e) - 1) - y 5 2 := by linarith
    have h_lhs_neg : (c 2 * ((∑ e, y 5 e) - 1) - y 5 2) * F.f 2 (x 1) < 0 :=
      mul_neg_of_pos_of_neg h_factor_pos hn21
    rw [hident] at h_lhs_neg
    exact neg_of_mul_neg_right h_lhs_neg hy52_pos.le

end

end Minimality.T24.Hexagon

end
