module

public import Minimality.Type08S.GT_Wrap22

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 23: the S2 position `zv = 0` of N2: facet-coefficient signs, `a`'s screen position,
Lemma 1.2 (`s b1 < a1`) and the `Q_ac` tilt rows.
At `zv = 0`: `FQac.d = FQac.a = 0`, `c = (0,0,0)`, `c, 2, a` are screen-collinear on the line through the origin.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem tilt_neg (F : Fc) (P Q S : V3) (hP : F.ev P = 0) (hQ : F.ev Q = 0) (hS : F.ev S = 0)
    (hc : 0 < F.c) {tt : ℝ} (hb : tt * F.c < -F.b) (hn : cxy P Q S < 0) :
    0 < ((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) + tt * cxy P Q S := by
  have e := tilt_parallel F P Q S hP hQ hS
  have h1 : 0 < (((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) + tt * cxy P Q S) * F.c := by
    have : (((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) + tt * cxy P Q S) * F.c
        = cxy P Q S * (F.b + tt * F.c) := by linear_combination e
    rw [this]; exact mul_pos_of_neg_of_neg hn (by linarith)
  exact pos_of_mul_pos_left h1 hc.le

theorem n2z_t1 {α2 β1 β2 γ1 γ2 δ2 b1 b2 t1 t2 t3 : ℝ} (hb2 : 0 < b2) (hγ1 : 0 < γ1) (hγ2 : 0 < γ2)
    (hβ1 : β1 < 0) (hβ2 : 0 ≤ β2) (d2 : δ2 < 0) (Qab_B : α2 * b1 + β2 * b2 + δ2 = 0)
    (E1 : β1 * t2 + γ1 * t3 = 0) (E2 : α2 * t1 + β2 * t2 + γ2 * t3 = 0)
    (hH : 0 < b2 * t1 - b1 * t2) : 0 < t1 := by
  have hc2 : 0 < β2 * γ1 - γ2 * β1 := by nlinarith [mul_nonneg hβ2 hγ1.le, mul_pos hγ2 (neg_pos.mpr hβ1)]
  have hlin : α2 * γ1 * t1 + (β2 * γ1 - γ2 * β1) * t2 = 0 := by
    linear_combination (-γ2) * E1 + γ1 * E2
  have hK : 0 < b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1) := by
    have e : b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1) = γ1 * (-δ2) - γ2 * β1 * b2 := by
      linear_combination γ1 * Qab_B
    rw [e]; nlinarith [mul_pos hγ1 (neg_pos.mpr d2), mul_pos (mul_pos hγ2 (neg_pos.mpr hβ1)) hb2]
  have key : (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1)) * t1 = (β2 * γ1 - γ2 * β1) * (b2 * t1 - b1 * t2) := by
    linear_combination b1 * hlin
  have : 0 < (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1)) * t1 := by rw [key]; exact mul_pos hc2 hH
  exact pos_of_mul_pos_right this hK.le

namespace N2Cfg0
variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
  (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hz : zv = 0)
include h hz

theorem zwn : zw < 0 := by have := h.hzw; linarith

theorem Qac_d : FQac.d = 0 := by have := h.Qac_C; simp only [Fc.ev, hz] at this; linarith

theorem Qac_a : FQac.a = 0 := by
  have := h.Qac_G; have d := h.Qac_d hz; simp only [Fc.ev] at this
  have e : FQac.a * A = 0 := by linarith
  exact (mul_eq_zero.mp e).resolve_right h.hA.ne'

theorem Qac_b : FQac.b < 0 := by
  have := h.Qac_R; have d := h.Qac_d hz; have a := h.Qac_a hz; simp only [Fc.ev] at this
  rw [a] at this
  by_contra hb; push Not at hb
  nlinarith [mul_nonneg hb h.hr2.le]

theorem Qac_c : 0 < FQac.c := by
  have := h.Qac_W; have d := h.Qac_d hz; have a := h.Qac_a hz; simp only [Fc.ev] at this
  have hw := h.zwn hz
  by_contra hb; push Not at hb
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hb hw.le]

theorem Qab_d : FQab.d < 0 := by have := h.Qab_C; simp only [Fc.ev, hz] at this; linarith
theorem T1_d : FT1.d < 0 := by have := h.T1_C; simp only [Fc.ev, hz] at this; linarith
theorem T2_d : FT2.d < 0 := by have := h.T2_C; simp only [Fc.ev, hz] at this; linarith
theorem T3_d : FT3.d < 0 := by have := h.T3_C; simp only [Fc.ev, hz] at this; linarith

theorem T1_apos : 0 < FT1.a := by
  have := h.T1_G; have d := h.T1_d hz; simp only [Fc.ev] at this
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) h.hA.le]

theorem T3_apos : 0 < FT3.a := by
  have := h.T3_G; have d := h.T3_d hz; simp only [Fc.ev] at this
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) h.hA.le]

theorem Qab_aeq : FQab.a * (r1 * b2 - r2 * b1) = (-FQab.d) * (b2 - r2) := by
  have h1 := h.Qab_R; have h2 := h.Qab_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T2_aeq : FT2.a * (r1 * b2 - r2 * b1) = (-FT2.d) * (b2 - r2) := by
  have h1 := h.T2_R; have h2 := h.T2_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem Qab_aneg (hr : b2 < r2) : FQab.a < 0 := by
  have e := h.Qab_aeq hz; have hS := h.S3_pos; have hd := h.Qab_d hz
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FQab.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T2_aneg (hr : b2 < r2) : FT2.a < 0 := by
  have e := h.T2_aeq hz; have hS := h.S3_pos; have hd := h.T2_d hz
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT2.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem Qab_apos (hr : r2 < b2) : 0 < FQab.a := by
  have e := h.Qab_aeq hz; have hS := h.S3_pos; have hd := h.Qab_d hz
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FQab.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem T2_apos (hr : r2 < b2) : 0 < FT2.a := by
  have e := h.T2_aeq hz; have hS := h.S3_pos; have hd := h.T2_d hz
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT2.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem Qab_azero (hr : r2 = b2) : FQab.a = 0 := by
  have e := h.Qab_aeq hz; have hS := h.S3_pos
  have e' : FQab.a * (r1 * b2 - r2 * b1) = 0 := by rw [e, hr]; ring
  exact (mul_eq_zero.mp e').resolve_right hS.ne'

theorem Qab_cpos : 0 < FQab.c := by
  have Qab_M := h.Qab_M; have Qab_B := h.Qab_B; simp only [Fc.ev] at Qab_M Qab_B
  have e : FQab.c * m3 = -(1 - s) * FQab.d := by linear_combination Qab_M - s * Qab_B
  have hd := h.Qab_d hz
  exact n2_pos_of_mul h.hm3 (by rw [e]; nlinarith [h.hs1])

theorem Qab_bnn (hb : b1 ≤ r1) : 0 ≤ FQab.b := by
  have Qab_R := h.Qab_R; have Qab_B := h.Qab_B; simp only [Fc.ev] at Qab_R Qab_B
  have hS3 := h.S3_pos; have d2 := h.Qab_d hz
  have hβ2S : FQab.b * (r1 * b2 - r2 * b1) = (-FQab.d) * (r1 - b1) := by
    linear_combination (-b1) * Qab_R + r1 * Qab_B
  by_contra hc; push Not at hc
  nlinarith [mul_pos (neg_pos.mpr hc) hS3, mul_nonneg (neg_pos.mpr d2).le (sub_nonneg.mpr hb)]

theorem Qab_bpos (hb : b1 < r1) : 0 < FQab.b := by
  have Qab_R := h.Qab_R; have Qab_B := h.Qab_B; simp only [Fc.ev] at Qab_R Qab_B
  have hS3 := h.S3_pos; have d2 := h.Qab_d hz
  have hβ2S : FQab.b * (r1 * b2 - r2 * b1) = (-FQab.d) * (r1 - b1) := by
    linear_combination (-b1) * Qab_R + r1 * Qab_B
  exact n2_pos_of_mul hS3 (by rw [hβ2S]; exact mul_pos (neg_pos.mpr d2) (sub_pos.mpr hb))

/-- Collinearity on the screen of `c, 2, a`. -/
theorem col : a2 * m3 = s * b2 * a3 := by
  have Qac_M := h.Qac_M; have Qac_A := h.Qac_A; have d := h.Qac_d hz; have a := h.Qac_a hz
  simp only [Fc.ev] at Qac_M Qac_A
  rw [d, a] at Qac_M Qac_A
  have hc := h.Qac_c hz
  have : FQac.c * (a2 * m3 - s * b2 * a3) = 0 := by linear_combination a2 * Qac_M - (s * b2) * Qac_A
  have := (mul_eq_zero.mp this).resolve_left hc.ne'
  linarith

theorem a3pos : 0 < a3 := by
  have Qac_A := h.Qac_A; have d := h.Qac_d hz; have a := h.Qac_a hz
  simp only [Fc.ev] at Qac_A
  rw [d, a] at Qac_A
  have hb := h.Qac_b hz; have hc := h.Qac_c hz; have ha2 := h.ha2
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hh), mul_pos (neg_pos.mpr hb) ha2]

/-- Lemma 1.2 at `zv = 0`. -/
theorem xa0 (hb : b1 ≤ r1) : s * b1 < a1 := by
  have Qac_M := h.Qac_M; have Qac_A := h.Qac_A; have d := h.Qac_d hz; have a := h.Qac_a hz
  have Qab_B := h.Qab_B; have Qab_M := h.Qab_M; have Qab_A := h.Qab_A
  have H_B := h.H_B; have H_A := h.H_A; have H_M := h.H_M
  obtain ⟨Hc, Hd⟩ := h.H_cd
  simp only [Fc.ev] at Qac_M Qac_A Qab_B Qab_M Qab_A H_B H_A H_M
  rw [Hc, Hd] at H_B H_A H_M
  rw [d, a] at Qac_M Qac_A
  have hHα := h.H_a_neg
  have E1 : FQac.b * (a2 - s * b2) + FQac.c * (a3 - m3) = 0 := by linear_combination Qac_A - Qac_M
  have E2 : FQab.a * (a1 - s * b1) + FQab.b * (a2 - s * b2) + FQab.c * (a3 - m3) = 0 := by
    linear_combination Qab_A - Qab_M
  have hH : 0 < b2 * (a1 - s * b1) - b1 * (a2 - s * b2) := by
    have e : FH.a * b1 + FH.b * b2 = 0 := by linarith
    have hh : FH.a * (a1 - s * b1) + FH.b * (a2 - s * b2) < 0 := by
      have : FH.a * (s * b1) + FH.b * (s * b2) = 0 := by linear_combination s * e
      linarith
    exact n2_edgeH h.hb2 hHα e hh
  have := n2z_t1 h.hb2 (h.Qac_c hz) (h.Qab_cpos hz) (h.Qac_b hz) (h.Qab_bnn hz hb) (h.Qab_d hz)
    (by linarith) E1 E2 hH
  linarith

/-- `κ (a2 - s b2) = - α s b2 (a1 - s b1)` for `Q_ab`. -/
theorem a2rel : (a2 - s * b2) * (FQab.b * (s * b2) + FQab.c * m3) = -FQab.a * (s * b2) * (a1 - s * b1) := by
  have Qab_M := h.Qab_M; have Qab_A := h.Qab_A; simp only [Fc.ev] at Qab_M Qab_A
  have E2 : FQab.a * (a1 - s * b1) + FQab.b * (a2 - s * b2) + FQab.c * (a3 - m3) = 0 := by
    linear_combination Qab_A - Qab_M
  have colT : (a3 - m3) * (s * b2) = (a2 - s * b2) * m3 := by have := h.col hz; linarith
  linear_combination (s * b2) * E2 - FQab.c * colT

theorem kappa_pos (hb : b1 ≤ r1) : 0 < FQab.b * (s * b2) + FQab.c * m3 := by
  have := h.Qab_bnn hz hb; have := h.Qab_cpos hz
  have hsb := mul_pos h.hs0 h.hb2
  nlinarith [mul_nonneg ‹0 ≤ FQab.b› hsb.le, mul_pos ‹0 < FQab.c› h.hm3]

/-- `cxy (c, 2, a) < 0` (orientation in the `xy`-plane), from `Q_ac` and `H`. -/
theorem cxyCMA : cxy ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ < 0 := by
  subst hz
  have hc := h.Qac_c rfl
  have key := plane_aff FQac FH ⟨0, 0, 0⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨A, 0, 0⟩ hc.ne'
    h.Qac_C h.Qac_M h.Qac_A h.Qac_G h.H_C h.H_M
  have g : cxy ⟨0, 0, 0⟩ ⟨s * b1, s * b2, m3⟩ ⟨A, 0, 0⟩ < 0 := by
    simp only [cxy]; nlinarith [mul_pos (mul_pos h.hs0 h.hb2) h.hA]
  have e1 := h.H_A; have e2 := h.H_G
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr e1.le) hh, mul_pos_of_neg_of_neg e2 g]

end N2Cfg0

end Type08Sp
end Minimality
