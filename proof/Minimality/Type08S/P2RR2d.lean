module

public import Minimality.Type08S.P2RR2c

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R2d: `AngBig` is `γ4 > 1` in the `T` frame; and the main theorem `lexCell_N2WS`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace R2

theorem angBig_gamma {a b b' c d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α4 γ4 : ℝ}
    (hν : 0 < ν) (hv1 : v1 ≠ 0) (hha : 0 < ha)
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3)
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hang : AngBig a b b' c d) : 1 < γ4 := by
  unfold AngBig at hang
  have f1 : c - b' = (0 - (-v1 * (1 - γ4) + α4 * w1)) • e1 + (0 - α4 * ha) • e2 +
      (C0 - (α4 * w3 + γ4 * C0)) • e3 := by
    rw [hc, hb']; simp only [pt, pc]; module
  have f2 : a - d = (w1) • e1 + (ha) • e2 + (w3) • e3 := by
    rw [ha_, hd]; simp only [pt, pc]; module
  have f3 : b - d = (0:ℝ) • e1 + (0:ℝ) • e2 + ν • e3 := by
    rw [hb, hd]; simp only [pt, pc]; module
  have f4 : c - d = (v1) • e1 + (0:ℝ) • e2 + C0 • e3 := by
    rw [hc, hd]; simp only [pt, pc]; module
  rw [f1, f2, f3, f4, det3_coord, det3_coord] at hang
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ν ^ 2 * ha ^ 2 * v1 ^ 2 := by positivity
  nlinarith [sq_nonneg (det3 e1 e2 e3), mul_nonneg (sq_nonneg (det3 e1 e2 e3)) (mul_nonneg hpos.le (sub_nonneg.mpr hcon))]

end R2
end Type08Sp
end Minimality
