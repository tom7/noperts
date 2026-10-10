module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Six-decimal bounds for cos and sin of 2π/5

The atlas covers outer views with azimuth in the wedge `[0, 2π/5]`
(`AtlasPose.InViewWedge`), and the fivefold solids' fundamental-cell prune
(`AtlasFundamentalPrune`) compares traces against the rotation by `2π/5`
about the z axis. Both use rational six-decimal stand-ins for
`cos (2π/5) = (√5 - 1)/4 ≈ 0.309017` and `sin (2π/5) ≈ 0.951057`; these two
lemmas bound the error of those stand-ins by `10⁻⁶`. They do not depend on
any solid.
-/

namespace Noperts.Pipeline

theorem cos_two_pi_div_five_bounds :
    |Real.cos (2 * Real.pi / 5) - (309017 / 1000000 : ℝ)| ≤
      1 / 1000000 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower : (2236067 / 1000000 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 2236067 / 1000000)]
  have hsqrtUpper : Real.sqrt 5 ≤ (2236069 / 1000000 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 2236069 / 1000000)]
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  rw [abs_le]
  constructor <;> nlinarith

theorem sin_two_pi_div_five_bounds :
    |Real.sin (2 * Real.pi / 5) - (951057 / 1000000 : ℝ)| ≤
      1 / 1000000 := by
  have hangle0 : 0 < 2 * Real.pi / 5 := by positivity
  have hanglePi : 2 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcosBounds := cos_two_pi_div_five_bounds
  rw [abs_le] at hcosBounds ⊢
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
  constructor <;> nlinarith [sq_nonneg
    (Real.sin (2 * Real.pi / 5) - 951056 / 1000000),
    sq_nonneg (Real.sin (2 * Real.pi / 5) - 951058 / 1000000)]

end Noperts.Pipeline

end
