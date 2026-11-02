module

public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K6HF

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k24h1c0_gram (A N E : ℝ³) : det3 A N E ^ 2 = ⟪A, A⟫ * ⟪N, N⟫ * ⟪E, E⟫ +
    2 * ⟪A, N⟫ * ⟪N, E⟫ * ⟪E, A⟫ - ⟪A, A⟫ * ⟪N, E⟫ ^ 2 - ⟪N, N⟫ * ⟪E, A⟫ ^ 2 -
    ⟪E, E⟫ * ⟪A, N⟫ ^ 2 := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  ring

set_option maxHeartbeats 3200000 in
/-- Metric facts of cell C. -/
theorem k24h1c0_keys {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH : K6mH1 α1 β1 β6 γ6)
    (ht1 : ⟪c - a', a - b'⟫ = 0) :
    0 < ⟪c - b', a - b'⟫ ∧ ⟪c - a', c - d⟫ < 0 := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨hα1, hβ1, -, hβ6, hγ61⟩ := hH
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e1 : c - a' = (1 - γ6) • R - β6 • Q := by rw [ha', hQ, hR]; module
  have e3 : a - b' = (1 - α1) • P - β1 • R := by rw [hb', hP, hR]; module
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  have e9 : c - b' = (1 - β1) • R - α1 • P := by rw [hb', hP, hR]; module
  have hg := k24h1c0_gram P Q R
  rw [e1, e3] at ht1
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  rw [e9, e3, e1]
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at ht1 hm0 hm1 hm2 ⊢
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  simp only [hPR, hRP] at ht1 hm1 hm2 hg ⊢
  have hdet2 : 0 < det3 P Q R ^ 2 := by positivity
  have hee : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by
    by_contra hn; push_neg at hn
    nlinarith [sq_nonneg (⟪Q, Q⟫ - ⟪R, R⟫), real_inner_self_nonneg (x := Q), real_inner_self_nonneg (x := R)]
  have hm : ⟪P, Q⟫ < 0 := by
    by_contra hn; push_neg at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hee.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hr2]
  have hqq : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hpq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  -- PD: ss * Dd > m^2 ee
  have hpd : ⟪P, Q⟫ ^ 2 * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) <
      ⟪P, P⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by nlinarith
  have hss : -(β1 - 1) * ⟪P, Q⟫ < α1 * ⟪P, P⟫ := by
    by_contra hn; push_neg at hn
    have h1 := mul_le_mul_of_nonneg_right hn hr2.le
    nlinarith
  have hpos : 0 ≤ α1 * ⟪P, Q⟫ + (β1 - 1) * ⟪R, R⟫ := by
    have : (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) * (α1 * ⟪P, Q⟫ + (β1 - 1) * ⟪R, R⟫) =
        (β1 - 1) * (⟪R, R⟫ - ⟪Q, R⟫) ^ 2 := by linear_combination hr1'
    by_contra hn; push_neg at hn
    nlinarith [mul_neg_of_pos_of_neg hee hn, mul_nonneg (sub_pos.2 hβ1).le (sq_nonneg (⟪R, R⟫ - ⟪Q, R⟫))]
  have hα : 0 < α1 - 1 := by linarith
  constructor
  · nlinarith [mul_pos hα (sub_pos.2 hss), mul_nonneg (by linarith : (0:ℝ) ≤ β1) hpos]
  · have hT : β1 * ((1 - γ6) * ⟪R, R⟫ - β6 * ⟪Q, R⟫) = (1 - α1) * ⟪P, Q⟫ * (1 - γ6 - β6) := by
      linear_combination (-1 : ℝ) * ht1
    have : (1 - α1) * ⟪P, Q⟫ * (1 - γ6 - β6) < 0 := by
      have : 0 < (α1 - 1) * (-⟪P, Q⟫) := mul_pos hα (by linarith)
      nlinarith [mul_pos this (by linarith : (0:ℝ) < γ6 + β6 - 1)]
    nlinarith


set_option maxHeartbeats 3200000 in
/-- <c-c',c-d> > 0 on the tie. -/
theorem k24h1c0_cc {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH : K6mH1 α1 β1 β6 γ6)
    (ht1 : ⟪c - a', a - b'⟫ = 0) :
    0 < ⟪c - c', c - d⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨hα1, hβ1, -, hβ6, hγ61⟩ := hH
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e1 : c - a' = (1 - γ6) • R - β6 • Q := by rw [ha', hQ, hR]; module
  have e3 : a - b' = (1 - α1) • P - β1 • R := by rw [hb', hP, hR]; module
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  have e9 : c - b' = (1 - β1) • R - α1 • P := by rw [hb', hP, hR]; module
  have hg := k24h1c0_gram P Q R
  rw [e1, e3] at ht1
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at ht1 hm0 hm1 hm2 ⊢
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  simp only [hPR, hRP] at ht1 hm1 hm2 hg ⊢
  have hdet2 : 0 < det3 P Q R ^ 2 := by positivity
  have hee : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by
    by_contra hn; push_neg at hn
    nlinarith [sq_nonneg (⟪Q, Q⟫ - ⟪R, R⟫), real_inner_self_nonneg (x := Q), real_inner_self_nonneg (x := R)]
  have hm : ⟪P, Q⟫ < 0 := by
    by_contra hn; push_neg at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hee.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hr2]
  have hqq : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hpq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  have hW2 : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := hee
  have e7 : c - c' = R - α1 • P - β1 • Q := by rw [hc', hR, hP, hQ]; module
  have e8 : ⟪c, R⟫ - ⟪c', R⟫ = ⟪R, R⟫ - α1 * ⟪P, R⟫ - β1 * ⟪Q, R⟫ := by
    rw [← inner_sub_left, e7]; simp only [inner_sub_left, inner_smul_left, conj_trivial]
  rw [e8, hPR]
  have hX : (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) * (⟪R, R⟫ - α1 * ⟪P, Q⟫ - β1 * ⟪Q, R⟫) =
      (β1 - 1) * (⟪Q, Q⟫ - ⟪Q, R⟫) * (⟪R, R⟫ - ⟪Q, R⟫) + (⟪R, R⟫ - ⟪Q, R⟫) * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) := by
    linear_combination (-1 : ℝ) * hr1'
  have hpos : 0 < (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) * (⟪R, R⟫ - α1 * ⟪P, Q⟫ - β1 * ⟪Q, R⟫) := by
    rw [hX]
    have h1 : 0 < ⟪Q, Q⟫ - ⟪Q, R⟫ := by linarith
    have h2 : 0 < ⟪R, R⟫ - ⟪Q, R⟫ := by linarith
    have := mul_pos (mul_pos (sub_pos.2 hβ1) h1) h2
    nlinarith [mul_pos h2 hW2]
  exact pos_of_mul_pos_right hpos hW2.le

end C2
end Type08Sp
end Minimality
