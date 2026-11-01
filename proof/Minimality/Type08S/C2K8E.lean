module

public import Minimality.Type08S.C2K8D

@[expose] public section

/-! # K8E: tilt choices and the wrapper for `TpA1ii` with `C > 0`: all of `s ≠ 0`, and `s = 0` unless `⟪t - c', q⟫ = 0`. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- A tilt segment `v = (η (1 + lam), -1)` in the cone `Q1` (with `(1 - β1) v1 + v2 < 0`), positive on `x v1 + y v2` if `y < 0`. -/
theorem k8_tilt1 {β1 : ℝ} (x y : ℝ) (hβ1 : 0 < β1) : ∃ η : ℝ, 0 < η ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → 0 < η + lam * η ∧ (-1 : ℝ) + lam * 0 < 0 ∧
      (1 - β1) * (η + lam * η) + ((-1 : ℝ) + lam * 0) < 0) ∧
    (y < 0 → ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < (η + lam * η) * x + ((-1 : ℝ) + lam * 0) * y) := by
  by_cases hy : y = 0
  · refine ⟨1 / (4 * (1 + β1)), by positivity, ?_, fun h => absurd hy h.ne⟩
    intro lam hl0 hl1
    have h4 : 0 < 4 * (1 + β1) := by positivity
    have e : 1 / (4 * (1 + β1)) * (4 * (1 + β1)) = 1 := by field_simp
    have hη : 0 < 1 / (4 * (1 + β1)) := by positivity
    refine ⟨by nlinarith, by linarith, ?_⟩
    nlinarith [mul_pos hη hl0, mul_pos hη hβ1, mul_pos (mul_pos hη hβ1) hl0]
  · obtain ⟨η0, hη0, hη0x⟩ := k8_eta (x := x) hy
    set η := min η0 (1 / (4 * (1 + β1))) with hηdef
    have hη1 : η ≤ η0 := min_le_left _ _
    have hη2 : η ≤ 1 / (4 * (1 + β1)) := min_le_right _ _
    have hηp : 0 < η := lt_min hη0 (by positivity)
    have h4 : 0 < 4 * (1 + β1) := by positivity
    have e : 1 / (4 * (1 + β1)) * (4 * (1 + β1)) = 1 := by field_simp
    refine ⟨η, hηp, ?_, ?_⟩
    · intro lam hl0 hl1
      refine ⟨by nlinarith, by linarith, ?_⟩
      have : η * (4 * (1 + β1)) ≤ 1 := by nlinarith
      nlinarith [mul_pos hηp hl0, mul_pos hηp hβ1, mul_pos (mul_pos hηp hβ1) hl0]
    · intro hy' lam hl0 hl1
      have hay : |y| = -y := abs_of_neg hy'
      have h1 : |(η + lam * η) * x| ≤ 2 * η * |x| := by
        rw [abs_mul, abs_of_pos (by nlinarith : 0 < η + lam * η)]
        have := abs_nonneg x
        nlinarith [mul_nonneg (mul_pos hηp (sub_pos.2 hl1)).le this]
      have h2 : 2 * η * |x| ≤ 2 * η0 * |x| := by
        have := abs_nonneg x; nlinarith
      have := neg_abs_le ((η + lam * η) * x)
      nlinarith

/-- The mirror: `v = (-η (1 + lam), -1)` in the cone `Q4`, `x v1 + y v2 < 0` if `0 < y`. -/
theorem k8_tilt4 {β1 : ℝ} (x y : ℝ) (hβ1 : 0 < β1) : ∃ η : ℝ, 0 < η ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → -η + lam * -η < 0 ∧ (-1 : ℝ) + lam * 0 < 0 ∧
      (1 - β1) * (-η + lam * -η) + ((-1 : ℝ) + lam * 0) < 0) ∧
    (0 < y → ∀ lam : ℝ, 0 < lam → lam < 1 → (-η + lam * -η) * x + ((-1 : ℝ) + lam * 0) * y < 0) := by
  by_cases hy : y = 0
  · refine ⟨1 / (4 * (1 + β1)), by positivity, ?_, fun h => absurd hy h.ne'⟩
    intro lam hl0 hl1
    have h4 : 0 < 4 * (1 + β1) := by positivity
    have e : 1 / (4 * (1 + β1)) * (4 * (1 + β1)) = 1 := by field_simp
    have hη : 0 < 1 / (4 * (1 + β1)) := by positivity
    refine ⟨by nlinarith, by linarith, ?_⟩
    nlinarith [mul_pos hη hl0, mul_pos hη hβ1, mul_pos (mul_pos hη hβ1) hl0]
  · obtain ⟨η0, hη0, hη0x⟩ := k8_eta (x := x) hy
    set η := min η0 (1 / (4 * (1 + β1))) with hηdef
    have hη1 : η ≤ η0 := min_le_left _ _
    have hη2 : η ≤ 1 / (4 * (1 + β1)) := min_le_right _ _
    have hηp : 0 < η := lt_min hη0 (by positivity)
    have h4 : 0 < 4 * (1 + β1) := by positivity
    have e : 1 / (4 * (1 + β1)) * (4 * (1 + β1)) = 1 := by field_simp
    refine ⟨η, hηp, ?_, ?_⟩
    · intro lam hl0 hl1
      refine ⟨by nlinarith, by linarith, ?_⟩
      have : η * (4 * (1 + β1)) ≤ 1 := by nlinarith
      nlinarith [mul_pos hηp hl0, mul_pos hηp hβ1, mul_pos (mul_pos hηp hβ1) hl0]
    · intro hy' lam hl0 hl1
      have hay : |y| = y := abs_of_pos hy'
      have h1 : |(-η + lam * -η) * x| ≤ 2 * η * |x| := by
        rw [abs_mul, show -η + lam * -η = -(η + lam * η) by ring, abs_neg, abs_of_pos (by nlinarith : 0 < η + lam * η)]
        have := abs_nonneg x
        nlinarith [mul_nonneg (mul_pos hηp (sub_pos.2 hl1)).le this]
      have h2 : 2 * η * |x| ≤ 2 * η0 * |x| := by
        have := abs_nonneg x; nlinarith
      have := neg_abs_le ((-η + lam * -η) * x)
      have := le_abs_self ((-η + lam * -η) * x)
      nlinarith

end C2
end Type08Sp
end Minimality
