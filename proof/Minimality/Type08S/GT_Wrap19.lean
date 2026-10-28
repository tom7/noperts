module

public import Minimality.Type08S.GT_Wrap18

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 19: N2, weakly beyond, `r2 = b2`, `zv > 0` (`propH_n2_ge_eq2`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem crossYZ_planar (F : Fc) (P Q S : V3) (hP : F.ev P = 0) (hQ : F.ev Q = 0) (hS : F.ev S = 0)
    (ha : F.a = 0) (hc : F.c ≠ 0) : crossYZ P Q S = 0 := by
  simp only [Fc.ev] at hP hQ hS
  have hu : F.a * (Q.x - P.x) + F.b * (Q.y - P.y) + F.c * (Q.z - P.z) = 0 := by linarith
  have hv : F.a * (S.x - P.x) + F.b * (S.y - P.y) + F.c * (S.z - P.z) = 0 := by linarith
  rw [ha] at hu hv
  have : F.c * crossYZ P Q S = 0 := by
    simp only [crossYZ]
    linear_combination (Q.y - P.y) * hv - (S.y - P.y) * hu
  exact (mul_eq_zero.mp this).resolve_left hc

theorem phiP0 {F1 F2 : Fc} {S : V3} (h2 : F2.ev S < 0) (a1 : 0 < F1.a) (a2 : F2.a = 0) :
    0 < Phi F1 F2 S := by
  simp only [Phi]; rw [a2]; nlinarith [mul_pos (neg_pos.mpr h2) a1]

theorem _root_.Minimality.N2Cfg.Qab_bc {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3)
    (hb : b1 < r1) : 0 < FQab.b ∧ 0 < FQab.c := by
  have Qab_R := h.Qab_R; have Qab_B := h.Qab_B; have Qab_M := h.Qab_M
  simp only [Fc.ev] at Qab_R Qab_B Qab_M
  have d2 := h.delta_Qab; have hS3 := h.S3_pos
  have hβ2S : FQab.b * (r1 * b2 - r2 * b1) = (-FQab.d) * (r1 - b1) := by
    linear_combination (-b1) * Qab_R + r1 * Qab_B
  refine ⟨?_, ?_⟩
  · exact n2_pos_of_mul hS3 (by rw [hβ2S]; exact mul_pos (neg_pos.mpr d2) (sub_pos.mpr hb))
  · have e : FQab.c * m3 = -(1 - s) * FQab.d := by linear_combination Qab_M - s * Qab_B
    exact n2_pos_of_mul h.hm3 (by rw [e]; nlinarith [h.hs1])

theorem _root_.Minimality.N2Cfg.Qab_a_zero {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hr : r2 = b2) :
    FQab.a = 0 := by
  have e := h.Qab_a_eq; have hS := h.S3_pos
  have e' : FQab.a * (r1 * b2 - r2 * b1) = 0 := by rw [e, hr]; ring
  exact (mul_eq_zero.mp e').resolve_right hS.ne'

theorem _root_.Minimality.N2Cfg.T2_a_zero {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hr : r2 = b2) :
    FT2.a = 0 := by
  have e := h.T2_a_eq; have hS := h.S3_pos
  have e' : FT2.a * (r1 * b2 - r2 * b1) = 0 := by rw [e, hr]; ring
  exact (mul_eq_zero.mp e').resolve_right hS.ne'

/-- The screen tests of the pentagon at `r2 = b2` (all but the two collinear rows). -/
theorem n2_hcv_eq {E U zv zw A b1 b2 r1 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg E U zv zw A b1 b2 r1 b2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → ¬ ((i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 2)) →
      crossYZ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 b2 i) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 b2 (i + 1))
        (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 b2 j) < 0 := by
  have hHa := h.H_a_neg; have hQc := h.Qac_a_pos
  have hQb := h.Qab_a_zero rfl; have hT2 := h.T2_a_zero rfl
  have hT1 := h.T1_a_pos; have hT3 := h.T3_a_pos
  have hzw := h.hzw; have hzv := h.hzv; have hb2 := h.hb2; have ha2 := h.ha2
  have hs0 := h.hs0; have hsb := mul_pos hs0 hb2
  have k02 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) hsb]
  have k03 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨a1, a2, a3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) ha2]
  have k04 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨r1, b2, 0⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) hb2]
  -- edge 1: `c 2` = H ∩ Qac
  have p1a := phiN (F1 := FH) (F2 := FQac) (S := ⟨a1, a2, a3⟩) h.H_A.le h.Qac_A.le hHa hQc (Or.inl h.H_A)
  have p1r := phiN (F1 := FH) (F2 := FQac) (S := ⟨r1, b2, 0⟩) h.H_R.le h.Qac_R.le hHa hQc (Or.inl h.H_R)
  have p1w := phiN (F1 := FH) (F2 := FQac) (S := ⟨0, 0, zw⟩) h.H_W.le h.Qac_W.le hHa hQc (Or.inr h.Qac_W)
  have ne1 : FQab.ev ⟨0, 0, zv⟩ ≠ FQab.ev ⟨s * b1, s * b2, m3⟩ := fun e => by
    have := h.Qab_C; have := h.Qab_M; linarith
  have k10 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨0, 0, zw⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k02
  have k13 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ < 0 :=
    neg_of_prod (cross_pos_prod FH FQac FQab _ _ _ _ h.H_C h.H_M h.Qac_C h.Qac_M ne1 (phi_prodN p1a p1w)) k10
  have k14 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨r1, b2, 0⟩ < 0 :=
    neg_of_prod (cross_pos_prod FH FQac FQab _ _ _ _ h.H_C h.H_M h.Qac_C h.Qac_M ne1 (phi_prodN p1r p1w)) k10
  -- edge 2: `2 a`
  have p2w := phiP0 (F1 := FQac) (F2 := FQab) (S := ⟨0, 0, zw⟩) h.Qab_W hQc hQb
  have p2c := phiP0 (F1 := FQac) (F2 := FQab) (S := ⟨0, 0, zv⟩) h.Qab_C hQc hQb
  have ne2 : FT1.ev ⟨s * b1, s * b2, m3⟩ ≠ FT1.ev ⟨a1, a2, a3⟩ := fun e => by
    have := h.T1_A; have := h.T1_M; linarith
  have k21 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, zv⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k13
  have k20 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, zw⟩ < 0 :=
    neg_of_prod (cross_pos_prod FQac FQab FT1 _ _ _ _ h.Qac_M h.Qac_A h.Qab_M h.Qab_A ne2 (phi_prodP p2w p2c)) k21
  -- edge 4: `c' a'` = T3 ∩ T2, reference from edge 0
  have p4c := phiP0 (F1 := FT3) (F2 := FT2) (S := ⟨0, 0, zv⟩) h.T2_C hT3 hT2
  have p4m := phiP0 (F1 := FT3) (F2 := FT2) (S := ⟨s * b1, s * b2, m3⟩) h.T2_M hT3 hT2
  have p4a := phiP0 (F1 := FT3) (F2 := FT2) (S := ⟨a1, a2, a3⟩) h.T2_A hT3 hT2
  have ne4 : FT1.ev ⟨r1, b2, 0⟩ ≠ FT1.ev ⟨0, 0, zw⟩ := fun e => by
    have := h.T1_R; have := h.T1_W; linarith
  have k41 : crossYZ ⟨r1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ < 0 := by
    have := k04; rw [crossYZ_cyc, crossYZ_cyc] at this; exact this
  have k42 : crossYZ ⟨r1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨s * b1, s * b2, m3⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT3 FT2 FT1 _ _ _ _ h.T3_R h.T3_W h.T2_R h.T2_W ne4 (phi_prodP p4m p4c)) k41
  have k43 : crossYZ ⟨r1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨a1, a2, a3⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT3 FT2 FT1 _ _ _ _ h.T3_R h.T3_W h.T2_R h.T2_W ne4 (phi_prodP p4a p4c)) k41
  -- edge 3: `a c'` = T1 ∩ Qab
  have p3w := phiP0 (F1 := FT1) (F2 := FQab) (S := ⟨0, 0, zw⟩) h.Qab_W hT1 hQb
  have p3c := phiP0 (F1 := FT1) (F2 := FQab) (S := ⟨0, 0, zv⟩) h.Qab_C hT1 hQb
  have ne3 : FT2.ev ⟨a1, a2, a3⟩ ≠ FT2.ev ⟨r1, b2, 0⟩ := fun e => by
    have := h.T2_A; have := h.T2_R; linarith
  have k30 : crossYZ ⟨a1, a2, a3⟩ ⟨r1, b2, 0⟩ ⟨0, 0, zw⟩ < 0 := by
    have := k43; rw [crossYZ_cyc, crossYZ_cyc] at this; exact this
  have k31 : crossYZ ⟨a1, a2, a3⟩ ⟨r1, b2, 0⟩ ⟨0, 0, zv⟩ < 0 :=
    neg_of_prod (cross_pos_prod FT1 FQab FT2 _ _ _ _ h.T1_A h.T1_R h.Qab_A h.Qab_R ne3 (phi_prodP p3c p3w)) k30
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i j hj1 hj2 hsp
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact absurd rfl hj1
  | exact absurd (by decide) hj2
  | exact absurd (Or.inl ⟨rfl, rfl⟩) hsp
  | exact absurd (Or.inr ⟨rfl, rfl⟩) hsp
  | (simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
     first | exact k02 | exact k03 | exact k04 | exact k13 | exact k14 | exact k10 | exact k21 | exact k20
           | exact k30 | exact k31 | exact k43 | exact k41 | exact k42)

end Type08Sp
end Minimality
