module

public import Minimality.Type21Limit
public import Minimality.Type08S.P2RFinalJ
public import Minimality.ManyTies
public import Minimality.Type08S.P2RLexUni5

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

theorem inner3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- (★): the edge identity. -/
theorem h21_bracket (A B d y a w : ℝ³) (μ : ℝ) (hd : d = μ • cross A B) :
    det3 d (y - a) w = μ * (⟪A, y - a⟫ * ⟪B, w⟫ - ⟪B, y - a⟫ * ⟪A, w⟫) := by
  subst hd
  simp only [det3_expand, inner3, cross_apply_zero, cross_apply_one, cross_apply_two,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-- Binet-Cauchy. -/
theorem h21_binet (A B u w : ℝ³) :
    ⟪A, u⟫ * ⟪B, w⟫ - ⟪A, w⟫ * ⟪B, u⟫ = ⟪cross A B, cross u w⟫ := by
  simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

theorem h21_cross_ne {A B u w : ℝ³} (hu : 0 < ⟪A, u⟫) (hv : ⟪B, u⟫ < 0)
    (hA : ⟪A, w⟫ ≤ 0) (hB : ⟪B, w⟫ ≤ 0) (hs : ⟪A, w⟫ < 0 ∨ ⟪B, w⟫ < 0) :
    cross A B ≠ 0 := by
  intro h
  have := h21_binet A B u w
  rw [h] at this
  simp only [inner_zero_left] at this
  rcases hs with hs | hs <;> nlinarith [mul_pos hu (neg_pos.2 hv), mul_nonneg_of_nonpos_of_nonpos hA hv.le,
    mul_nonpos_of_nonneg_of_nonpos hu.le hB, mul_neg_of_pos_of_neg hu hv]

/-- A vector orthogonal to both is a multiple of the cross product. -/
theorem h21_mul_cross {A B d : ℝ³} (hc : cross A B ≠ 0) (h1 : ⟪A, d⟫ = 0) (h2 : ⟪B, d⟫ = 0) :
    ∃ μ : ℝ, d = μ • cross A B := by
  have hn : 0 < ⟪cross A B, cross A B⟫ := real_inner_self_pos.2 hc
  rw [inner3] at h1 h2
  simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two] at hn
  set N : ℝ := (A 1 * B 2 - A 2 * B 1) * (A 1 * B 2 - A 2 * B 1) +
        (A 2 * B 0 - A 0 * B 2) * (A 2 * B 0 - A 0 * B 2) +
      (A 0 * B 1 - A 1 * B 0) * (A 0 * B 1 - A 1 * B 0) with hN
  refine ⟨((A 1 * B 2 - A 2 * B 1) * d 0 + (A 2 * B 0 - A 0 * B 2) * d 1 +
    (A 0 * B 1 - A 1 * B 0) * d 2) / N, ?_⟩
  have k0 : d 0 = (((A 1 * B 2 - A 2 * B 1) * d 0 + (A 2 * B 0 - A 0 * B 2) * d 1 +
    (A 0 * B 1 - A 1 * B 0) * d 2) / N) * (A 1 * B 2 - A 2 * B 1) := by
    rw [div_mul_eq_mul_div, eq_div_iff hn.ne', hN]
    linear_combination
      ((A 2 * B 0 - A 0 * B 2) * A 2 - (A 0 * B 1 - A 1 * B 0) * A 1) * h2
      - ((A 2 * B 0 - A 0 * B 2) * B 2 - (A 0 * B 1 - A 1 * B 0) * B 1) * h1
  have k1 : d 1 = (((A 1 * B 2 - A 2 * B 1) * d 0 + (A 2 * B 0 - A 0 * B 2) * d 1 +
    (A 0 * B 1 - A 1 * B 0) * d 2) / N) * (A 2 * B 0 - A 0 * B 2) := by
    rw [div_mul_eq_mul_div, eq_div_iff hn.ne', hN]
    linear_combination
      ((A 0 * B 1 - A 1 * B 0) * A 0 - (A 1 * B 2 - A 2 * B 1) * A 2) * h2
      - ((A 0 * B 1 - A 1 * B 0) * B 0 - (A 1 * B 2 - A 2 * B 1) * B 2) * h1
  have k2 : d 2 = (((A 1 * B 2 - A 2 * B 1) * d 0 + (A 2 * B 0 - A 0 * B 2) * d 1 +
    (A 0 * B 1 - A 1 * B 0) * d 2) / N) * (A 0 * B 1 - A 1 * B 0) := by
    rw [div_mul_eq_mul_div, eq_div_iff hn.ne', hN]
    linear_combination
      ((A 1 * B 2 - A 2 * B 1) * A 1 - (A 2 * B 0 - A 0 * B 2) * A 0) * h2
      - ((A 1 * B 2 - A 2 * B 1) * B 1 - (A 2 * B 0 - A 0 * B 2) * B 0) * h1
  ext i
  fin_cases i
  · simpa [cross_apply_zero] using k0
  · simpa [cross_apply_one] using k1
  · simpa [cross_apply_two] using k2

end H21
end Minimality
