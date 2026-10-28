module

public import Minimality.Type08S.GT_Wrap19

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem n2_t1_pos'' {zv b1 b2 t1 t2 t3 α1 β1 γ1 δ1 α2 β2 γ2 δ2 : ℝ} (hzv : 0 < zv) (hb2 : 0 < b2)
    (d1 : δ1 < 0) (d2 : δ2 < 0) (hα1 : 0 < α1) (hα2 : α2 ≤ 0) (hγ1 : 0 < γ1) (hγ2 : 0 < γ2)
    (hβ1 : β1 < 0) (hβ2 : 0 ≤ β2)
    (Qac_C : α1 * 0 + β1 * 0 + γ1 * zv + δ1 = 0)
    (Qac_B : α1 * b1 + β1 * b2 + γ1 * 0 + δ1 < 0)
    (Qab_B : α2 * b1 + β2 * b2 + γ2 * 0 + δ2 = 0)
    (Qab_C : α2 * 0 + β2 * 0 + γ2 * zv + δ2 < 0)
    (E1 : α1 * t1 + β1 * t2 + γ1 * t3 = 0) (E2 : α2 * t1 + β2 * t2 + γ2 * t3 = 0)
    (hH : b2 * t1 - b1 * t2 > 0) : 0 < t1 := by
  have hc1 : α2 * γ1 - γ2 * α1 < 0 := by nlinarith [mul_pos hγ2 hα1, mul_nonneg (neg_nonneg.mpr hα2) hγ1.le]
  have hc2 : 0 < β2 * γ1 - γ2 * β1 := by nlinarith [mul_nonneg hβ2 hγ1.le, mul_pos hγ2 (neg_pos.mpr hβ1)]
  have hlin : (α2 * γ1 - γ2 * α1) * t1 + (β2 * γ1 - γ2 * β1) * t2 = 0 := by
    linear_combination (-γ2) * E1 + γ1 * E2
  have hK : 0 < b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1) := by
    have e : b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1) =
        γ1 * (α2 * b1 + β2 * b2) - γ2 * (α1 * b1 + β1 * b2) := by ring
    rw [e]
    have e1 : α2 * b1 + β2 * b2 = -δ2 := by linarith
    have e2 : α1 * b1 + β1 * b2 < -δ1 := by linarith
    have e3 : γ1 * zv = -δ1 := by linarith
    have e4 : γ2 * zv < -δ2 := by linarith
    rw [e1]
    have : 0 < zv * (γ1 * -δ2 - γ2 * (α1 * b1 + β1 * b2)) := by
      nlinarith [mul_pos hγ2 (show 0 < -δ1 - (α1 * b1 + β1 * b2) by linarith),
        mul_pos (neg_pos.mpr d1) (show 0 < -δ2 - γ2 * zv by linarith), mul_pos hγ2 hzv]
    exact pos_of_mul_pos_right this hzv.le
  have key : (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1)) * t1 =
      (β2 * γ1 - γ2 * β1) * (b2 * t1 - b1 * t2) := by
    linear_combination b1 * hlin
  have : 0 < (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1)) * t1 := by
    rw [key]; exact mul_pos hc2 hH
  exact pos_of_mul_pos_right this hK.le


variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}

/-- Weak Lemma 1.2 / 30.3 (`b2 < r2`): `x_a > x_2`, with `A ≤ r1`, `b1 ≤ r1`. -/
theorem _root_.Minimality.N2Cfg.xa2 (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3)
    (hα2 : FQab.a ≤ 0) (hA : A ≤ r1) (hb : b1 ≤ r1) : s * b1 < a1 := by
  have Qac_G := h.Qac_G; have Qac_C := h.Qac_C; have Qac_M := h.Qac_M; have Qac_A := h.Qac_A
  have Qac_R := h.Qac_R; have Qac_B := h.Qac_B
  have Qab_R := h.Qab_R; have Qab_B := h.Qab_B; have Qab_M := h.Qab_M; have Qab_A := h.Qab_A
  have Qab_C := h.Qab_C
  have H_B := h.H_B; have H_A := h.H_A; have H_M := h.H_M
  obtain ⟨Hc, Hd⟩ := h.H_cd
  simp only [Fc.ev] at Qac_G Qac_C Qac_M Qac_A Qac_R Qac_B Qab_R Qab_B Qab_M Qab_A Qab_C H_B H_A H_M
  rw [Hc, Hd] at H_B H_A H_M
  have hα1 : 0 < FQac.a := h.Qac_a_pos
  have hHα := h.H_a_neg
  have d1 := h.delta_Qac; have d2 := h.delta_Qab
  have hS3 := h.S3_pos
  have hβ2S : FQab.b * (r1 * b2 - r2 * b1) = (-FQab.d) * (r1 - b1) := by
    linear_combination (-b1) * Qab_R + r1 * Qab_B
  have hγ1 : 0 < FQac.c := n2_pos_of_mul h.hzv (by linarith)
  have hγ2 : 0 < FQab.c := by
    have e : FQab.c * m3 = -(1 - s) * FQab.d := by linear_combination Qab_M - s * Qab_B
    exact n2_pos_of_mul h.hm3 (by rw [e]; nlinarith [h.hs1])
  have hβ1 : FQac.b < 0 := (h.Qac_bc hA).1
  have hβ2 : 0 ≤ FQab.b := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos (neg_pos.mpr hc) hS3, mul_nonneg (neg_pos.mpr d2).le (sub_nonneg.mpr hb)]
  have E1 : FQac.a * (a1 - s * b1) + FQac.b * (a2 - s * b2) + FQac.c * (a3 - m3) = 0 := by
    linear_combination Qac_A - Qac_M
  have E2 : FQab.a * (a1 - s * b1) + FQab.b * (a2 - s * b2) + FQab.c * (a3 - m3) = 0 := by
    linear_combination Qab_A - Qab_M
  have hH : b2 * (a1 - s * b1) - b1 * (a2 - s * b2) > 0 := by
    have e : FH.a * b1 + FH.b * b2 = 0 := by linarith
    have hh : FH.a * (a1 - s * b1) + FH.b * (a2 - s * b2) < 0 := by
      have : FH.a * (s * b1) + FH.b * (s * b2) = 0 := by linear_combination s * e
      linarith
    exact n2_edgeH h.hb2 hHα e hh
  have := n2_t1_pos'' h.hzv h.hb2 d1 d2 hα1 hα2 hγ1 hγ2 hβ1 hβ2 Qac_C Qac_B Qab_B Qab_C E1 E2 hH
  linarith


end Type08Sp
end Minimality
