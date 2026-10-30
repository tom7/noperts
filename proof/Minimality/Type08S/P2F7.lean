module

public import Minimality.Type08S.P2F0
public import Minimality.Type08S.P2F1
public import Minimality.Type08S.P2F2
public import Minimality.Type08S.P2F3
public import Minimality.Type08S.P2F4
public import Minimality.Type08S.P2F5
public import Minimality.Type08S.P2F6

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

namespace TpCfg
variable {E U zv zw A b1 b2 r1 r2 xa za a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
  (h : TpCfg E U zv zw A b1 b2 r1 r2 xa za a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem H_cd : FH.c = 0 ∧ FH.d = 0 := by
  have h1 := h.H_V; have h2 := h.H_W; simp only [Fc.ev] at h1 h2
  have hzw := h.hzw
  have hc : FH.c = 0 := by
    have : FH.c * (zv - zw) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by linarith)
  refine ⟨hc, ?_⟩
  rw [hc] at h1; linarith

theorem H_a_neg : FH.a < 0 := by
  have h1 := h.H_G; simp only [Fc.ev] at h1
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1
  have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem S3_pos : 0 < r1 * b2 - r2 * b1 := by
  have h1 := h.H_B; have h2 := h.H_R; simp only [Fc.ev] at h1 h2
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1 h2
  have ha := h.H_a_neg; have hb2 := h.hb2
  have e : FH.a * (r1 * b2 - r2 * b1) = b2 * (FH.a * r1 + FH.b * r2 + 0 * 0 + 0) -
      r2 * (FH.a * b1 + FH.b * b2 + 0 * 0 + 0) := by ring
  have hneg : FH.a * (r1 * b2 - r2 * b1) < 0 := by
    rw [e, h1]; have := mul_neg_of_pos_of_neg hb2 h2; linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hh]

theorem delta_T2 (hz : 0 < zv) (hzw : zw < 0) : FT2.d < 0 := by
  have := h.T2_V; have := h.T2_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FT2 hz hzw (by linarith) (by linarith) (Or.inr (by linarith))

theorem T2_a_eq : FT2.a * xa * zv = (-FT2.d) * (zv - za) := by
  have h1 := h.T2_V; have h2 := h.T2_P; simp only [Fc.ev] at h1 h2
  linear_combination zv * h2 - za * h1

theorem T2_a_neg_iff (hz : 0 < zv) (hzw : zw < 0) : FT2.a < 0 ↔ za > zv := by
  have e := h.T2_a_eq; have hd := h.delta_T2 hz hzw; have := h.hxa
  constructor
  · intro ha
    by_contra hc; push Not at hc
    nlinarith [mul_pos (show 0 < -FT2.a by linarith) (mul_pos h.hxa hz),
      mul_nonneg (show 0 ≤ -FT2.d by linarith) (show 0 ≤ zv - za by linarith)]
  · intro hc
    by_contra ha; push Not at ha
    nlinarith [mul_nonneg ha (mul_pos h.hxa hz).le,
      mul_pos (show 0 < -FT2.d by linarith) (show 0 < za - zv by linarith)]

theorem T2_a_neg_of_le (hz : 0 < zv) (hzw : zw < 0) (hr : b2 ≤ r2) : FT2.a < 0 := by
  have h1 := h.T2_B; have h2 := h.T2_R; simp only [Fc.ev] at h1 h2
  have hS := h.S3_pos; have hd := h.delta_T2 hz hzw
  have key : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) < 0 := by
    have : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) =
        b2 * (FT2.a * r1 + FT2.b * r2 + FT2.c * 0 + FT2.d) -
          r2 * (FT2.a * b1 + FT2.b * b2 + FT2.c * 0 + FT2.d) := by ring
    rw [this, h1]
    have := mul_neg_of_pos_of_neg h.hb2 h2
    linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_nonneg (show 0 ≤ -FT2.d by linarith) (show 0 ≤ r2 - b2 by linarith)]

end TpCfg

end Type08Sp
end Minimality
