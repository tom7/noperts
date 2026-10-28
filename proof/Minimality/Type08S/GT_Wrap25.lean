module

public import Minimality.Type08S.GT_Wrap24

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 25: N2, weakly beyond, `r2 > b2`, `zv = 0` (S2): the pentagon `(a', c, 2, a, c')` with
`c, 2, a` screen-collinear (tilt rows in `Q_ac`), and `a2 > s b2` (`a` beyond `2` on the line).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

section G0
variable {zv zw s b1 b2 z2 A r1 r2 a1 a2 a3 t : ℝ}

/-- Like `n2g_g`, with the row of the collinear edge `(2, a)` as a hypothesis. -/
theorem n2g_g0 (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hb2 : 0 < b2) (hr2 : 0 < r2) (ha3 : 0 < a3) (hz2 : (1 - s) * zv < z2)
    (ht : t * (s * b2) < z2)
    (hrow2 : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 2)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (2 + 1)) ⟨A, 0, 0⟩) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) ⟨A, 0, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hD : 0 < zv - zw := by linarith
  have a1' := mul_pos hA hD
  have a2' := mul_pos hA hr2
  have a3' := mul_pos ha3 hr2
  have a4' := mul_pos hr2 (neg_pos.mpr hzw)
  have a5' := mul_pos hA (sub_pos.mpr ht)
  have a6' := mul_pos (mul_pos hs0 hb2) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    right; refine ⟨by ring, by nlinarith⟩
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    rcases lt_or_eq_of_le hzv with hz | hz
    · left; nlinarith [mul_pos (mul_pos hs0 hb2) hz]
    · subst hz
      right; refine ⟨by ring, by nlinarith⟩
  · exact hrow2
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    left; nlinarith
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    left; nlinarith

end G0

namespace N2Cfg0
variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
  (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hz : zv = 0)
include h hz

/-- the tilt `t` with `t s b2 < m3` is below the slope of `Q_ac`. -/
theorem ttc {t : ℝ} (ht : 0 < t) (htt : t * (s * b2) < m3) : t * FQac.c < -FQac.b := by
  have hc := h.Qac_c hz
  have Qac_M := h.Qac_M; have d0 := h.Qac_d hz; have a0 := h.Qac_a hz
  simp only [Fc.ev] at Qac_M
  rw [d0, a0] at Qac_M
  have hsb := mul_pos h.hs0 h.hb2
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hsb.le (show 0 ≤ t * FQac.c + FQac.b by linarith), mul_pos hc h.hm3,
    mul_pos hc (sub_pos.mpr htt)]

theorem a2gt (hr : b2 < r2) (hb : b1 ≤ r1) : s * b2 < a2 := by
  have hxa := h.xa0 hz hb
  have rel := h.a2rel hz
  have hk := h.kappa_pos hz hb
  have hα := h.Qab_aneg hz hr
  have hsb := mul_pos h.hs0 h.hb2
  have : 0 < (a2 - s * b2) * (FQab.b * (s * b2) + FQab.c * m3) := by
    rw [rel]; nlinarith [mul_pos (mul_pos (neg_pos.mpr hα) hsb) (sub_pos.mpr hxa)]
  have := pos_of_mul_pos_left this hk.le
  linarith

theorem a2eq (hr : r2 = b2) (hb : b1 ≤ r1) : a2 = s * b2 := by
  have rel := h.a2rel hz
  have hk := h.kappa_pos hz hb
  have hα := h.Qab_azero hz hr
  rw [hα] at rel
  have : (a2 - s * b2) * (FQab.b * (s * b2) + FQab.c * m3) = 0 := by rw [rel]; ring
  have := (mul_eq_zero.mp this).resolve_right hk.ne'
  linarith

end N2Cfg0

/-- The 13 strict screen tests of the pentagon `(a', c, 2, a, c')`, N2, `r2 > b2`, `zv = 0`. -/
theorem n2_hcv0 {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hz : zv = 0)
    (hr : b2 < r2) (hb : b1 ≤ r1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → ¬ ((i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 1)) →
      crossYZ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 i) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (i + 1))
        (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 j) < 0 := by
  have hHa := h.H_a_neg; have hQb := h.Qab_aneg hz hr
  have hT1 := h.T1_apos hz; have hT3 := h.T3_apos hz; have hT2 := h.T2_aneg hz hr
  have hzw := h.zwn hz; have hb2 := h.hb2; have hr2 := h.hr2; have ha2 := h.ha2
  have hs0 := h.hs0; have hsb := mul_pos hs0 hb2
  have hm3 := h.hm3
  have hg := h.a2gt hz hr hb
  have hcol := h.col hz
  have hD : 0 < zv - zw := by have := h.hzw; linarith
  have ha3m : m3 < a3 := by nlinarith
  -- edge 0: `a' c`
  have k02 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos hD hsb]
  have k03 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨a1, a2, a3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos hD ha2]
  have k04 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨r1, r2, 0⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos hD hr2]
  -- edge 1: `c 2`
  have k10 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨0, 0, zw⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k02
  have k14 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨r1, r2, 0⟩ < 0 := by
    simp only [crossYZ]; rw [hz]; nlinarith [mul_pos hm3 hr2]
  -- edge 2: `2 a`
  have k24 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ < 0 := by
    simp only [crossYZ]
    nlinarith [mul_pos (sub_pos.mpr hg) hm3, mul_pos (sub_pos.mpr ha3m) (show 0 < r2 - s * b2 by nlinarith [mul_pos (sub_pos.mpr h.hs1) hb2])]
  have k20 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, zw⟩ < 0 := by
    simp only [crossYZ]
    nlinarith [mul_pos (sub_pos.mpr hg) (neg_pos.mpr hzw)]
  -- edge 3: `a c'` = T1 ∩ Qab
  have p3w := phiP (F1 := FT1) (F2 := FQab) (S := ⟨0, 0, zw⟩) h.T1_W.le h.Qab_W.le hT1 hQb (Or.inl h.T1_W)
  have p3c := phiP (F1 := FT1) (F2 := FQab) (S := ⟨0, 0, zv⟩) h.T1_C.le h.Qab_C.le hT1 hQb (Or.inl h.T1_C)
  have p3m := phiP (F1 := FT1) (F2 := FQab) (S := ⟨s * b1, s * b2, m3⟩) h.T1_M.le h.Qab_M.le hT1 hQb (Or.inl h.T1_M)
  have ne3 : FT2.ev ⟨a1, a2, a3⟩ ≠ FT2.ev ⟨r1, r2, 0⟩ := fun e => by
    have := h.T2_A; have := h.T2_R; linarith
  have k32 : crossYZ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ ⟨s * b1, s * b2, m3⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k24
  have k30 : crossYZ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT1 FQab FT2 _ _ _ _ h.T1_A h.T1_R h.Qab_A h.Qab_R ne3 (phi_prodP p3w p3m)) k32
  have k31 : crossYZ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ ⟨0, 0, zv⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT1 FQab FT2 _ _ _ _ h.T1_A h.T1_R h.Qab_A h.Qab_R ne3 (phi_prodP p3c p3m)) k32
  -- edge 4: `c' a'` = T3 ∩ T2
  have p4c := phiP (F1 := FT3) (F2 := FT2) (S := ⟨0, 0, zv⟩) h.T3_C.le h.T2_C.le hT3 hT2 (Or.inl h.T3_C)
  have p4m := phiP (F1 := FT3) (F2 := FT2) (S := ⟨s * b1, s * b2, m3⟩) h.T3_M.le h.T2_M.le hT3 hT2 (Or.inl h.T3_M)
  have p4a := phiP (F1 := FT3) (F2 := FT2) (S := ⟨a1, a2, a3⟩) h.T3_A.le h.T2_A.le hT3 hT2 (Or.inl h.T3_A)
  have ne4 : FT1.ev ⟨r1, r2, 0⟩ ≠ FT1.ev ⟨0, 0, zw⟩ := fun e => by
    have := h.T1_R; have := h.T1_W; linarith
  have k43 : crossYZ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ ⟨a1, a2, a3⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k30
  have k41 : crossYZ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT3 FT2 FT1 _ _ _ _ h.T3_R h.T3_W h.T2_R h.T2_W ne4 (phi_prodP p4c p4a)) k43
  have k42 : crossYZ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ ⟨s * b1, s * b2, m3⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT3 FT2 FT1 _ _ _ _ h.T3_R h.T3_W h.T2_R h.T2_W ne4 (phi_prodP p4m p4a)) k43
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i j hj1 hj2 hx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact absurd rfl hj1
  | exact absurd (by decide) hj2
  | exact absurd (by decide) hx
  | (simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
     first | exact k02 | exact k03 | exact k04 | exact k14 | exact k10 | exact k24 | exact k20
           | exact k32 | exact k30 | exact k31 | exact k43 | exact k41 | exact k42)

end Type08Sp
end Minimality
