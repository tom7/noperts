module

public import Minimality.Type08S.P2I5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I6: frame-level closing of the `K_b`-type slide (`x'` the origin, `x`, `f`, `r`, `g` the screen quadrilateral,
the F-side middle `p` open over `x f`) with the extra point `w` BELOW the vertex `g` (the case `T'`: `a` below `c'`),
hidden iff `Yg < Yr`.
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

/-- Rows of a point `w` directly below (`δw`) the vertex `g`. -/
theorem rows_below_g (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf Xr Yr zr Xg Yg zg δw : ℝ}
    (hκ : κ ≠ 0) (hκv : κv ≠ 0) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hYgr : Yg < Yr) (hδ : κ * δw < 0) :
    ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (fpt e1 e2 e3 O Xg Yg (zg + δw) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3)
      ((κ * κv) • e1) := by
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
    · nlinarith [mul_pos_of_neg_of_neg hδ (sub_neg.mpr hYgr)]
  · refine slideTest_of_deriv hF hκ hκv _ _ _ _ _ _ ?_ ?_
    · ring
    · nlinarith [mul_pos (neg_pos.mpr hδ) hYg]

/-- **`K_b`-type closing at `T'` with `w` below `g`** (frame level, `κv > 0`, standard cycle). -/
theorem close_hidden_frame (hF : Fr e1 e2 e3) (O : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg Xp zp δw : ℝ} (hκ : κ ≠ 0) (hκv : 0 < κv)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hXp0 : 0 < Xp) (hXpL : Xp < L) (hDp : L * (zp - κ) - Xp * (zf - κ) ≠ 0)
    (hYgr : Yg < Yr) (hδ : κ * δw < 0)
    (hz : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i, κv • e3⟫))
    (hbad : NoPersistHDN (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg) (κv • e3) ((κ * κv) • e1)) :
    IsRupert ({O, fpt e1 e2 e3 O 0 0 κ, fpt e1 e2 e3 O L 0 zf, fpt e1 e2 e3 O Xr Yr zr,
      fpt e1 e2 e3 O Xg Yg zg, fpt e1 e2 e3 O Xp 0 zp, fpt e1 e2 e3 O Xg Yg (zg + δw)} : Finset ℝ³) :=
  slide_core hF O _ hκ hκv.ne' hL hYr hYg hcr hcg hXp0 hXpL hDp
    (rows_below_g hF O hκ hκv.ne' hL hYr hYg hcr hcg hYgr hδ) hz hbad

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_hidden_frame
