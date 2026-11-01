module

public import Minimality.Type16UJ

@[expose] public section


/-!
# U1: depth patterns of the pentagon `(6,3,5,2,4)` (pure real)
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U

theorem qB_lt (A B p q r : ℝ) (hA : 0 < A) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hB1 : B < 1) (G : 1 < p + r)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1)) : q < B := by
  have hq1 : q < 1 := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg hA.le (sub_nonneg.2 hc), mul_pos (sub_pos.2 hB1) (by linarith : (0:ℝ) < p + r)]
  by_contra hc; push Not at hc
  have h1 : (1 - q) * (p + r) ≤ (1 - B) * (p + r) := by nlinarith
  have hAp : p + r < A := by
    by_contra hd; push Not at hd
    nlinarith [mul_nonneg (sub_nonneg.2 hd) (sub_pos.2 hq1).le]
  nlinarith [mul_pos hq (sub_pos.2 hAp), mul_pos hq (by linarith : (0:ℝ) < p + r - 1), mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ p + r - 1)]

/-- Peaks at `3, 2` or at `6, 2` (the latter with `m1 ≤ 0`): impossible. -/
theorem pat_core (A B p q r m1 m2 m3 : ℝ) (hA : 0 < A) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (G : 1 < p + r)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1))
    (hm1 : m1 ≤ 0) (hm13 : m1 < m3) (hm2 : m2 < 0)
    (c1 : m2 < A * m1 + B * m2) (c2 : p * m1 + q * m2 + r * m3 < A * m1 + B * m2) : False := by
  have hB1 : B < 1 := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hA.le hm1, mul_nonneg (sub_nonneg.2 hc) (neg_nonneg.2 hm2.le)]
  have hqB := qB_lt A B p q r hA hp hq hr hB1 G hu hR2
  have hc : (1 - B) * r < A * (1 - q) - p * (1 - B) := by nlinarith
  have e1 : 0 < (1 - B) * ((A - p) * m1 + (B - q) * m2 - r * m3) := mul_pos (sub_pos.2 hB1) (by linarith)
  have e2 : 0 < (B - q) * (A * m1 + (B - 1) * m2) := mul_pos (sub_pos.2 hqB) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hc.le) (neg_nonneg.2 hm1), mul_pos (sub_pos.2 hB1) hr,
    mul_pos (mul_pos (sub_pos.2 hB1) hr) (sub_pos.2 hm13)]

end H16U
end Minimality
