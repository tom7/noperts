module

public import Minimality.Type08S.P2NP3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a: the rows of the extra point `w` (N2: `a` inside the quadrilateral; T4: `q` on the chord `g x`).
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

theorem rows_N2 (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf Xr Yr zr Xg Yg zg Xa Ya za : ℝ}
    (hκv : κv ≠ 0) (hL : 0 < L) (hYa : 0 < Ya)
    (hfr : 0 < (Xr - L) * Ya - Yr * (Xa - L))
    (hrg : 0 < (Xg - Xr) * (Ya - Yr) - (Yg - Yr) * (Xa - Xr))
    (hgx : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)) (c : ℝ) :
    ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (fpt e1 e2 e3 O Xa Ya za - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3) (c • e1) := by
  intro i
  have h11 : (1 : ZMod 4) + 1 = 2 := by decide
  have h21 : (2 : ZMod 4) + 1 = 3 := by decide
  have h31 : (3 : ZMod 4) + 1 = 0 := by decide
  have hLY : 0 < L * Ya := mul_pos hL hYa
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [h11, h21, h31, Qg, quad, Matrix.cons_val, zero_add, fpt_sub] <;>
    refine slideTest_of_cross hF hκv _ _ _ _ _ _ ?_ <;> nlinarith [hLY, hfr, hrg, hgx]

/-- Rows of the G-middle `q` (on the screen segment `0 g`, strictly inside), T4. -/
theorem rows_T4 (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf Xr Yr zr Xg Yg zg Xq Yq zq : ℝ}
    (hκ : κ ≠ 0) (hκv : κv ≠ 0) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hYq : 0 < Yq) (hYlt : Yq < Yg) (hcop : Xq * Yg = Yq * Xg)
    (hchord : 0 < κ * ((0 - Yg) * (zq - zg) - (κ - zg) * (Yq - Yg))) :
    ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (fpt e1 e2 e3 O Xq Yq zq - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3) ((κ * κv) • e1) := by
  intro i
  have h11 : (1 : ZMod 4) + 1 = 2 := by decide
  have h21 : (2 : ZMod 4) + 1 = 3 := by decide
  have h31 : (3 : ZMod 4) + 1 = 0 := by decide
  have hLY : 0 < L * Yq := mul_pos hL hYq
  -- strict rows, multiplied by `Yg`
  have hr1 : 0 < (Xr - L) * Yq - Yr * (Xq - L) := by
    have h : 0 < Yg * ((Xr - L) * Yq - Yr * (Xq - L)) := by
      have e : Yg * ((Xr - L) * Yq - Yr * (Xq - L)) = Yq * ((Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) +
          Yr * L * (Yg - Yq) := by linear_combination (-Yr) * hcop
      rw [e]; nlinarith [mul_pos hYq hcr, mul_pos (mul_pos hYr hL) (sub_pos.mpr hYlt)]
    exact pos_of_mul_pos_right h hYg.le
  have hr2 : 0 < (Xg - Xr) * (Yq - Yr) - (Yg - Yr) * (Xq - Xr) := by
    have h : 0 < Yg * ((Xg - Xr) * (Yq - Yr) - (Yg - Yr) * (Xq - Xr)) := by
      have e : Yg * ((Xg - Xr) * (Yq - Yr) - (Yg - Yr) * (Xq - Xr)) = (Yg - Yq) * (Yg * Xr - Xg * Yr) := by
        linear_combination (-(Yg - Yr)) * hcop
      rw [e]; exact mul_pos (sub_pos.mpr hYlt) hcg
    exact pos_of_mul_pos_right h hYg.le
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [h11, h21, h31, Qg, quad, Matrix.cons_val, zero_add, fpt_sub]
  · exact slideTest_of_cross hF hκv _ _ _ _ _ _ (by nlinarith [hLY])
  · exact slideTest_of_cross hF hκv _ _ _ _ _ _ (by nlinarith [hr1])
  · exact slideTest_of_cross hF hκv _ _ _ _ _ _ (by nlinarith [hr2])
  · refine slideTest_of_deriv hF hκ hκv _ _ _ _ _ _ ?_ ?_
    · linear_combination hcop
    · nlinarith [hchord]

end Type08Sp
end Minimality
