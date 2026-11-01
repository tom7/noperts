module

public import Minimality.Type16UI
public import Minimality.Type16UG

@[expose] public section


/-!
# U1: the EV1 leaf `LDE (6,3,5,2,4)`  (`ζ < 0`, `φF(0,6) > 0`, `φH(0,6) > 0`): convexity of the pentagon
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

/-- Convexity of the pentagon `6̄, 3̄, 5̄, 2̄, 4̄` in the frame at `s06` (pure real). -/
theorem pent_hconv (A B p q r : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hab : 0 < A + B - 1) (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hc31 : 0 < B * (p + r) - q * A)
    (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1)) (hs1 : 0 < p + q + r - 1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < TwoRay.cross2
        (cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) (i + 1) -
          cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) i)
        (cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) j -
          cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) i) := by
  intro i j hji hj
  have hq' := hq.ne'
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hji
      | exact absurd (by decide) hj
      | (simp only [TwoRay.cross2, cyc5_0, cyc5_1, cyc5_2, cyc5_3, cyc5_4, show (0 : ZMod 5) + 1 = 1 from rfl,
          show (1 : ZMod 5) + 1 = 2 from rfl, show (2 : ZMod 5) + 1 = 3 from rfl,
          show (3 : ZMod 5) + 1 = 4 from rfl, show (4 : ZMod 5) + 1 = 0 from rfl, Prod.mk_sub_mk]
         field_simp
         nlinarith [mul_pos hA hq, mul_pos hB hq, mul_pos hq hp, mul_pos hq hr, mul_pos hq hR2,
           mul_pos hq hc31, mul_pos hq hu, mul_pos hq hab, mul_pos hq hs1])


/-- The point `1 = (0, g, d)` is strictly inside the pentagon. -/
theorem pent_inside1 (A B g d p q r z : ℝ) (hA : 0 < A) (hB : 0 < B) (hg : 0 < g) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hu : 0 < B * (p + r - 1) - q * (A - 1)) (hw : 0 < g * (p + r - 1) - q * (d - 1))
    (hd : 0 < d) (hR2 : 0 < (B - 1) * (p + r) - A * (q - 1)) (hs1 : 0 < p + q + r - 1)
    (hR1 : 0 < d * (q - 1) - (g - 1) * (p + r))
    (hZ : 0 < d * (B - 1) - A * (g - 1))
    (hZ' : 0 < (1 - A) * (q - g) - (1 - d) * (q - B) + (p + r - 1) * (B - g)) :
    ∀ i : ZMod 5, 0 < TwoRay.cross2
        (cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) (i + 1) -
          cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) i)
        ((1 - 0 - d + (p + r - 1) / q * g, g / q, z) -
          cyc5 (1 + (p + r - 1) / q) (1 / q) (p / q) (1 - A + (p + r - 1) / q * B) (B / q) (p * B / q - A) i) := by
  intro i
  have hq' := hq.ne'
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TwoRay.cross2, cyc5_0, cyc5_1, cyc5_2, cyc5_3, cyc5_4, show (0 : ZMod 5) + 1 = 1 from rfl,
          show (1 : ZMod 5) + 1 = 2 from rfl, show (2 : ZMod 5) + 1 = 3 from rfl,
          show (3 : ZMod 5) + 1 = 4 from rfl, show (4 : ZMod 5) + 1 = 0 from rfl, Prod.mk_sub_mk]
     field_simp
     nlinarith [mul_pos hA hq, mul_pos hq hg, mul_pos hq hp, mul_pos hq hr, mul_pos hq hR2, mul_pos hq hd,
           mul_pos hq hu, mul_pos hq hw, mul_pos hq hs1, mul_pos hq hZ, mul_pos hq hZ', mul_pos hq hR1])

end H16U
end Minimality
