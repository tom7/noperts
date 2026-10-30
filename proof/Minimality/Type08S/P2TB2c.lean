module

public import Minimality.Type08S.P2TB2b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B2c: `rows_T4g` (both edges at `ḡ`: SlideTest "zero, positive derivative"), `np_K2T`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Rows of `q` over the screen vertex `ḡ` (`Xq = Xg`, `Yq = Yg`): strict at the two edges not at `ḡ`, zero with
positive derivative at the two edges at `ḡ` (needs `Yg < Yr`, i.e. `AngBig`, and `κ (zq - zg) < 0`). -/
theorem rows_T4g (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf Xr Yr zr Xg Yg zg zq : ℝ}
    (hκ : κ ≠ 0) (hκv : κv ≠ 0) (hL : 0 < L) (hYg : 0 < Yg) (hYrg : Yg < Yr)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr))
    (hzq : κ * (zq - zg) < 0) :
    ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (fpt e1 e2 e3 O Xg Yg zq - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3) ((κ * κv) • e1) := by
  intro i
  have h11 : (1 : ZMod 4) + 1 = 2 := by decide
  have h21 : (2 : ZMod 4) + 1 = 3 := by decide
  have h31 : (3 : ZMod 4) + 1 = 0 := by decide
  have hLY : 0 < L * Yg := mul_pos hL hYg
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [h11, h21, h31, Qg, quad, Matrix.cons_val, zero_add, fpt_sub]
  · exact slideTest_of_cross hF hκv _ _ _ _ _ _ (by nlinarith [hLY])
  · exact slideTest_of_cross hF hκv _ _ _ _ _ _ (by nlinarith [hcr])
  · refine slideTest_of_deriv hF hκ hκv _ _ _ _ _ _ ?_ ?_
    · ring
    · nlinarith [mul_pos (sub_pos.mpr hYrg) (neg_pos.mpr hzq)]
  · refine slideTest_of_deriv hF hκ hκv _ _ _ _ _ _ ?_ ?_
    · ring
    · nlinarith [mul_pos hYg (neg_pos.mpr hzq)]

end Type08Sp
end Minimality
