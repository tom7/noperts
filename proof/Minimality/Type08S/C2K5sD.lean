module

public import Minimality.Type08S.C2K5sC

@[expose] public section

/-!
# K5s / D: real tilt-segment choices for the tie rule at `s = 0`
-/
set_option autoImplicit true
set_option linter.unusedVariables false

namespace Minimality
namespace Type08Sp
namespace C2

/-- X1: a segment in the open negative quadrant on which `x v1 + y v2 > 0`, when `x < 0` or `y < 0`. -/
theorem k5_tilt1 (x y : ℝ) (h : x < 0 ∨ y < 0) :
    ∃ u1 u2 t1 t2 : ℝ, u1 < 0 ∧ u2 < 0 ∧ u1 + t1 < 0 ∧ u2 + t2 < 0 ∧ u1 * t2 - u2 * t1 ≠ 0 ∧
      0 < u1 * x + u2 * y ∧ 0 < (u1 + t1) * x + (u2 + t2) * y := by
  rcases h with hx | hy
  · have hd : 0 < -x / (2 * (|y| + 1)) := by
      have : 0 < -x := by linarith
      positivity
    set δ := -x / (2 * (|y| + 1)) with hδ
    have e : δ * (|y| + 1) = -x / 2 := by rw [hδ]; field_simp
    have hy' : -(|y|) ≤ y := neg_abs_le y
    refine ⟨-1, -δ, 0, δ / 2, by norm_num, by linarith, by norm_num, by linarith, by intro h; nlinarith, ?_, ?_⟩
    · nlinarith [mul_nonneg hd.le (abs_nonneg y), abs_nonneg y, mul_nonneg hd.le (sub_nonneg.2 hy'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self y))]
    · nlinarith [mul_nonneg hd.le (abs_nonneg y), abs_nonneg y, mul_nonneg hd.le (sub_nonneg.2 hy'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self y))]
  · have hd : 0 < -y / (2 * (|x| + 1)) := by
      have : 0 < -y := by linarith
      positivity
    set δ := -y / (2 * (|x| + 1)) with hδ
    have e : δ * (|x| + 1) = -y / 2 := by rw [hδ]; field_simp
    have hx' : -(|x|) ≤ x := neg_abs_le x
    refine ⟨-δ, -1, δ / 2, 0, by linarith, by norm_num, by linarith, by norm_num, by intro h; nlinarith, ?_, ?_⟩
    · nlinarith [mul_nonneg hd.le (abs_nonneg x), abs_nonneg x, mul_nonneg hd.le (sub_nonneg.2 hx'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self x))]
    · nlinarith [mul_nonneg hd.le (abs_nonneg x), abs_nonneg x, mul_nonneg hd.le (sub_nonneg.2 hx'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self x))]

/-- X2: a segment with `v1 < 0 < v2` on which `x v1 + y v2 < 0`, when `0 < x` or `y < 0`. -/
theorem k5_tilt2 (x y : ℝ) (h : 0 < x ∨ y < 0) :
    ∃ u1 u2 t1 t2 : ℝ, u1 < 0 ∧ 0 < u2 ∧ u1 + t1 < 0 ∧ 0 < u2 + t2 ∧ u1 * t2 - u2 * t1 ≠ 0 ∧
      u1 * x + u2 * y < 0 ∧ (u1 + t1) * x + (u2 + t2) * y < 0 := by
  rcases h with hx | hy
  · have hd : 0 < x / (2 * (|y| + 1)) := by positivity
    set δ := x / (2 * (|y| + 1)) with hδ
    have e : δ * (|y| + 1) = x / 2 := by rw [hδ]; field_simp
    have hy' : -(|y|) ≤ y := neg_abs_le y
    refine ⟨-1, δ, 0, -δ / 2, by norm_num, by linarith, by norm_num, by linarith, by intro h; nlinarith, ?_, ?_⟩
    · nlinarith [mul_nonneg hd.le (abs_nonneg y), abs_nonneg y, mul_nonneg hd.le (sub_nonneg.2 hy'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self y))]
    · nlinarith [mul_nonneg hd.le (abs_nonneg y), abs_nonneg y, mul_nonneg hd.le (sub_nonneg.2 hy'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self y))]
  · have hd : 0 < -y / (2 * (|x| + 1)) := by
      have : 0 < -y := by linarith
      positivity
    set δ := -y / (2 * (|x| + 1)) with hδ
    have e : δ * (|x| + 1) = -y / 2 := by rw [hδ]; field_simp
    have hx' : -(|x|) ≤ x := neg_abs_le x
    refine ⟨-δ, 1, δ / 2, 0, by linarith, by norm_num, by linarith, by norm_num, by intro h; nlinarith, ?_, ?_⟩
    · nlinarith [mul_nonneg hd.le (abs_nonneg x), abs_nonneg x, mul_nonneg hd.le (sub_nonneg.2 hx'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self x))]
    · nlinarith [mul_nonneg hd.le (abs_nonneg x), abs_nonneg x, mul_nonneg hd.le (sub_nonneg.2 hx'), mul_nonneg hd.le (sub_nonneg.2 (le_abs_self x))]

end C2
end Type08Sp
end Minimality
