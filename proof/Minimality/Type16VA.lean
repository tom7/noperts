module

public import Minimality.Type16UW

@[expose] public section


/-! # H16/V: depth pattern "peaks at 6 and 2" without `m1 ≤ 0` (pure real) -/
set_option autoImplicit true
set_option linter.unusedVariables false

namespace Minimality
namespace H16U

theorem h16v_Ale (A B p q r : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (G : p + r ≤ 1)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1))
    (h6 : 0 < A * (q + r - 1) - (B - 1) * p) (hs : 0 < p + q + r - 1) : A ≤ p + r := by
  by_contra hc; push Not at hc
  nlinarith [mul_pos hA hr, mul_pos hq hp, mul_pos hB hp, mul_pos hu hp, mul_pos hR2 hp, mul_pos h6 hp, mul_pos hu hA, mul_pos hR2 hA, mul_pos h6 hA, mul_pos (sub_pos.2 hc) hq, mul_pos (sub_pos.2 hc) hB, mul_pos (sub_pos.2 hc) hr, mul_nonneg (sub_nonneg.2 G) hB.le, mul_nonneg (sub_nonneg.2 G) hq.le]

theorem h16v_Ap (A B p q r : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (G : 1 < p + r)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1))
    (h6 : 0 < A * (q + r - 1) - (B - 1) * p) (hs : 0 < p + q + r - 1) (hAp : p + r < A) : A * (1 - r) ≤ p := by
  by_contra hc; push Not at hc
  nlinarith [mul_pos hA hr, mul_pos hq hp, mul_pos hB hp, mul_pos hu hp, mul_pos hR2 hp, mul_pos h6 hp, mul_pos hu hA, mul_pos hR2 hA, mul_pos h6 hA, sub_pos.2 hc, mul_pos (sub_pos.2 hc) hq, mul_pos (sub_pos.2 hc) hB,mul_pos (sub_pos.2 hAp) hq, mul_pos (sub_pos.2 hAp) hB, mul_pos (sub_pos.2 hAp) hr]

/-- Peaks at `6` and `2` (no sign hypothesis on `m1`). -/
theorem h16v_pat_core (A B p q r m1 m2 m3 : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1))
    (h6 : 0 < A * (q + r - 1) - (B - 1) * p) (hs : 0 < p + q + r - 1)
    (hm13 : m1 < m3) (hm2 : m2 < 0)
    (c1 : m2 < A * m1 + B * m2) (c2 : p * m1 + q * m2 + r * m3 < A * m1 + B * m2)
    (c3 : p * m1 + q * m2 + r * m3 < m3) : False := by
  rcases le_or_gt A (p + r) with h | h
  · nlinarith [mul_pos hR2 (neg_pos.2 hm2), mul_pos (mul_pos hr hA) (sub_pos.2 hm13),
      mul_nonneg (sub_nonneg.2 h) (sub_pos.2 c1).le, mul_pos hA (sub_pos.2 c2)]
  · have G : 1 < p + r := by
      by_contra hG; push Not at hG
      linarith [h16v_Ale A B p q r hA hB hp hq hr hG hu hR2 h6 hs]
    have hAp := h16v_Ap A B p q r hA hB hp hq hr G hu hR2 h6 hs h
    nlinarith [mul_pos hu (neg_pos.2 hm2), mul_nonneg (by nlinarith : 0 ≤ p - A * (1 - r)) (sub_pos.2 hm13).le,
      mul_pos (sub_pos.2 h) (sub_pos.2 c3), mul_pos (by linarith : 0 < p + r - 1) (sub_pos.2 c2)]

/-- Peaks at `3` and `2` (`m3 < 0`), no `G`. -/
theorem h16v_pat32 (A B p q r m1 m2 m3 : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1))
    (h6 : 0 < A * (q + r - 1) - (B - 1) * p) (hs : 0 < p + q + r - 1)
    (hm1 : m1 ≤ 0) (hm13 : m1 < m3) (hm2 : m2 < 0)
    (c1 : m2 < A * m1 + B * m2) (c2 : p * m1 + q * m2 + r * m3 < A * m1 + B * m2) : False := by
  rcases le_or_gt A (p + r) with h | h
  · nlinarith [mul_pos hR2 (neg_pos.2 hm2), mul_pos (mul_pos hr hA) (sub_pos.2 hm13),
      mul_nonneg (sub_nonneg.2 h) (sub_pos.2 c1).le, mul_pos hA (sub_pos.2 c2)]
  · have G : 1 < p + r := by
      by_contra hG; push Not at hG
      linarith [h16v_Ale A B p q r hA hB hp hq hr hG hu hR2 h6 hs]
    exact pat_core A B p q r m1 m2 m3 hA hp hq hr G hu hR2 hm1 hm13 hm2 c1 c2

end H16U
end Minimality
