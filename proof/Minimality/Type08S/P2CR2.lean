module

public import Minimality.Type08S.P2CR1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 2: the cycle tests `hcyc` for the screen quadrilateral `(x, f, r, g)`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem det3_u0 (hF : Fr e1 e2 e3) (κv a1 a2 a3 b1 b2 b3 : ℝ) :
    det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (κv • e3) = κv * (a1 * b2 - a2 * b1) := by
  rw [pc_smul_e3 hF, det3_pc hF]; ring

theorem det3_e (hF : Fr e1 e2 e3) (c a1 a2 a3 b1 b2 b3 : ℝ) :
    det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (c • e1) = c * (a2 * b3 - a3 * b2) := by
  rw [pc_smul_e1, det3_pc hF]; ring

/-- Slide test of two coordinate vectors for the view `κv e3` and the slide `c e1`, `ρ = κv`:
strict screen orientation. -/
theorem slideTest_of_cross (hF : Fr e1 e2 e3) {κv c : ℝ} (hκv : κv ≠ 0) (a1 a2 a3 b1 b2 b3 : ℝ)
    (h : 0 < a1 * b2 - a2 * b1) :
    SlideTest κv (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (κv • e3) (c • e1) := by
  left
  rw [det3_u0 hF]
  have : 0 < κv * κv := mul_self_pos.mpr hκv
  nlinarith

/-- Slide test, equality case with positive derivative. -/
theorem slideTest_of_deriv (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (a1 a2 a3 b1 b2 b3 : ℝ) (h0 : a1 * b2 - a2 * b1 = 0) (h : 0 < κ * (a2 * b3 - a3 * b2)) :
    SlideTest κv (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (κv • e3) ((κ * κv) • e1) := by
  right
  refine ⟨by rw [det3_u0 hF, h0, mul_zero], ?_⟩
  rw [det3_e hF]
  have : 0 < κv * κv := mul_self_pos.mpr hκv
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **`hcyc` for the screen quadrilateral.** -/
theorem core_hcyc (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf Xr Yr zr Xg Yg zg : ℝ} (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr) (c : ℝ) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      SlideTest κv
        (quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
          (fpt e1 e2 e3 O Xg Yg zg) (i + 1) -
         quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
          (fpt e1 e2 e3 O Xg Yg zg) i)
        (quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
          (fpt e1 e2 e3 O Xg Yg zg) j -
         quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
          (fpt e1 e2 e3 O Xg Yg zg) i) (κv • e3) (c • e1) := by
  intro i j hi hj
  have key : ∀ (P Q R : ℝ³) (a1 a2 a3 b1 b2 b3 : ℝ), Q - P = pc e1 e2 e3 a1 a2 a3 →
      R - P = pc e1 e2 e3 b1 b2 b3 → 0 < a1 * b2 - a2 * b1 →
      SlideTest κv (Q - P) (R - P) (κv • e3) (c • e1) := by
    intro P Q R a1 a2 a3 b1 b2 b3 h1 h2 h3
    rw [h1, h2]; exact slideTest_of_cross hF hκv _ _ _ _ _ _ h3
  have hLY : 0 < L * Yr := mul_pos hL hYr
  have hLG : 0 < L * Yg := mul_pos hL hYg
  have h11 : (1 : ZMod 4) + 1 = 2 := by decide
  have h21 : (2 : ZMod 4) + 1 = 3 := by decide
  have h31 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hi | (exact absurd (by decide) hj) | skip
  all_goals
    simp only [h11, h21, h31, quad, Matrix.cons_val, zero_add, fpt_sub]
    refine slideTest_of_cross hF hκv _ _ _ _ _ _ ?_
    linarith [hLY, hLG, hcr, hcg]

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.core_hcyc
