module

public import Minimality.Type08S.GT_Wrap9

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 10: facet-coefficient signs of `T4Cfg0` valid at `zv = 0`
(copies of the `HEndT4` lemmas with `0 <= zv`; the facets `Q_ac, T1, T3, T4` have `C` strictly beneath).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem delta_neg0 (F : Fc) {zv zw : ℝ} (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hC : F.c * zv + F.d < 0) (hW : F.c * zw + F.d ≤ 0) : F.d < 0 := by
  have e : F.d * (zv - zw) = zv * (F.c * zw + F.d) + (-zw) * (F.c * zv + F.d) := by ring
  have hneg : F.d * (zv - zw) < 0 := by
    rw [e]
    nlinarith [mul_nonneg hzv (show 0 ≤ -(F.c * zw + F.d) by linarith),
      mul_pos (show 0 < -zw by linarith) (show 0 < -(F.c * zv + F.d) by linarith)]
  by_contra hc; push Not at hc
  nlinarith

namespace T4Cfg0
variable {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
variable (h : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem zw_neg0 : zw < 0 :=
  zw_neg_of FQac h.hA h.hr2 h.hDr h.hzw h.Qac_G h.Qac_R h.Qac_W h.Qac_V h.Qac_B

theorem delta_Qac : FQac.d < 0 := by
  have := h.Qac_V; have := h.Qac_W; simp only [Fc.ev] at *
  exact delta_neg0 FQac h.hzv h.zw_neg0 (by linarith) (by linarith)

theorem delta_T1 : FT1.d < 0 := by
  have := h.T1_V; have := h.T1_W; simp only [Fc.ev] at *
  exact delta_neg0 FT1 h.hzv h.zw_neg0 (by linarith) (by linarith)

theorem delta_T3 : FT3.d < 0 := by
  have := h.T3_V; have := h.T3_W; simp only [Fc.ev] at *
  exact delta_neg0 FT3 h.hzv h.zw_neg0 (by linarith) (by linarith)

theorem delta_T4 : FT4.d < 0 := by
  have := h.T4_V; have := h.T4_W; simp only [Fc.ev] at *
  exact delta_neg0 FT4 h.hzv h.zw_neg0 (by linarith) (by linarith)

theorem Qac_a_pos : 0 < FQac.a := by
  have h1 := h.Qac_G; simp only [Fc.ev] at h1
  have := h.delta_Qac; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem T4_a_pos : 0 < FT4.a := by
  have h1 := h.T4_G; simp only [Fc.ev] at h1
  have := h.delta_T4; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem T1_a_eq : FT1.a * (r1 * b2 - r2 * b1) = (-FT1.d) * (b2 - r2) := by
  have h1 := h.T1_R; have h2 := h.T1_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T3_a_eq : FT3.a * (r1 * b2 - r2 * b1) = (-FT3.d) * (b2 - r2) := by
  have h1 := h.T3_R; have h2 := h.T3_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T1_a_neg_of (hr : b2 < r2) : FT1.a < 0 := by
  have e := h.T1_a_eq; have hS := h.S3_pos; have hd := h.delta_T1
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT1.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T3_a_neg_of (hr : b2 < r2) : FT3.a < 0 := by
  have e := h.T3_a_eq; have hS := h.S3_pos; have hd := h.delta_T3
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT3.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T1_a_pos_of (hr : r2 < b2) : 0 < FT1.a := by
  have e := h.T1_a_eq; have hS := h.S3_pos; have hd := h.delta_T1
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT1.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem T3_a_pos_of (hr : r2 < b2) : 0 < FT3.a := by
  have e := h.T3_a_eq; have hS := h.S3_pos; have hd := h.delta_T3
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT3.d by linarith) (show 0 < b2 - r2 by linarith)]

end T4Cfg0
end Type08Sp
end Minimality
