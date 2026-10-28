module

public import Minimality.Type08S.GT_Wrap13

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 14: N2, weakly beyond, `r2 > b2`, `zv > 0`: `hcv` from the face lattice, `propH_n2_ge`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem phiN {F1 F2 : Fc} {S : V3} (h1 : F1.ev S ≤ 0) (h2 : F2.ev S ≤ 0) (a1 : F1.a < 0) (a2 : 0 < F2.a)
    (hs : F1.ev S < 0 ∨ F2.ev S < 0) : Phi F1 F2 S < 0 := by
  simp only [Phi]
  rcases hs with h | h <;> nlinarith [mul_nonneg (neg_nonneg.mpr h1) a2.le, mul_nonneg (neg_nonneg.mpr h2) (neg_nonneg.mpr a1.le),
    mul_pos (neg_pos.mpr h) a2, mul_pos (neg_pos.mpr h) (neg_pos.mpr a1)]

theorem phiP {F1 F2 : Fc} {S : V3} (h1 : F1.ev S ≤ 0) (h2 : F2.ev S ≤ 0) (a1 : 0 < F1.a) (a2 : F2.a < 0)
    (hs : F1.ev S < 0 ∨ F2.ev S < 0) : 0 < Phi F1 F2 S := by
  simp only [Phi]
  rcases hs with h | h <;> nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr a2.le), mul_nonneg (neg_nonneg.mpr h2) a1.le,
    mul_pos (neg_pos.mpr h) (neg_pos.mpr a2), mul_pos (neg_pos.mpr h) a1]

theorem neg_of_prod {x y : ℝ} (h : 0 < x * y) (hy : y < 0) : x < 0 := by nlinarith

theorem phi_prodN {F1 F2 : Fc} {S S' : V3} (h : Phi F1 F2 S < 0) (h' : Phi F1 F2 S' < 0) :
    0 < Phi F1 F2 S * Phi F1 F2 S' := mul_pos_of_neg_of_neg h h'
theorem phi_prodP {F1 F2 : Fc} {S S' : V3} (h : 0 < Phi F1 F2 S) (h' : 0 < Phi F1 F2 S') :
    0 < Phi F1 F2 S * Phi F1 F2 S' := mul_pos h h'

/-- The 15 tests of the pentagon `(a', c, 2, a, c')`, N2, `r2 > b2`, `zv > 0`. -/
theorem n2_hcv {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hr : b2 < r2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      crossYZ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 i) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (i + 1))
        (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 j) < 0 := by
  have hHa := h.H_a_neg; have hQc := h.Qac_a_pos; have hQb := h.Qab_a_neg_of hr
  have hT1 := h.T1_a_pos; have hT3 := h.T3_a_pos; have hT2 := h.T2_a_neg_of hr
  have hzw := h.hzw; have hzv := h.hzv; have hb2 := h.hb2; have hr2 := h.hr2; have ha2 := h.ha2
  have hs0 := h.hs0; have hsb := mul_pos hs0 hb2
  have hzz : zw < zv := h.hzw
  -- edge 0: `a' c`
  have k02 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) hsb]
  have k03 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨a1, a2, a3⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) ha2]
  have k04 : crossYZ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨r1, r2, 0⟩ < 0 := by
    simp only [crossYZ]; nlinarith [mul_pos (show 0 < zv - zw by linarith) hr2]
  -- edge 1: `c 2` = H ∩ Qac
  have p1a := phiN (F1 := FH) (F2 := FQac) (S := ⟨a1, a2, a3⟩) h.H_A.le h.Qac_A.le hHa hQc (Or.inl h.H_A)
  have p1r := phiN (F1 := FH) (F2 := FQac) (S := ⟨r1, r2, 0⟩) h.H_R.le h.Qac_R.le hHa hQc (Or.inl h.H_R)
  have p1w := phiN (F1 := FH) (F2 := FQac) (S := ⟨0, 0, zw⟩) h.H_W.le h.Qac_W.le hHa hQc (Or.inr h.Qac_W)
  have ne1 : FQab.ev ⟨0, 0, zv⟩ ≠ FQab.ev ⟨s * b1, s * b2, m3⟩ := fun e => by
    have := h.Qab_C; have := h.Qab_M; linarith
  have k10 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨0, 0, zw⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k02
  have k13 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ < 0 :=
    neg_of_prod (cross_pos_prod FH FQac FQab _ _ _ _ h.H_C h.H_M h.Qac_C h.Qac_M ne1 (phi_prodN p1a p1w)) k10
  have k14 : crossYZ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨r1, r2, 0⟩ < 0 :=
    neg_of_prod (cross_pos_prod FH FQac FQab _ _ _ _ h.H_C h.H_M h.Qac_C h.Qac_M ne1 (phi_prodN p1r p1w)) k10
  -- edge 2: `2 a` = Qac ∩ Qab
  have p2r := phiP (F1 := FQac) (F2 := FQab) (S := ⟨r1, r2, 0⟩) h.Qac_R.le h.Qab_R.le hQc hQb (Or.inl h.Qac_R)
  have p2w := phiP (F1 := FQac) (F2 := FQab) (S := ⟨0, 0, zw⟩) h.Qac_W.le h.Qab_W.le hQc hQb (Or.inl h.Qac_W)
  have p2c := phiP (F1 := FQac) (F2 := FQab) (S := ⟨0, 0, zv⟩) h.Qac_C.le h.Qab_C.le hQc hQb (Or.inr h.Qab_C)
  have ne2 : FT1.ev ⟨s * b1, s * b2, m3⟩ ≠ FT1.ev ⟨a1, a2, a3⟩ := fun e => by
    have := h.T1_A; have := h.T1_M; linarith
  have k21 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, zv⟩ < 0 := by
    rw [← crossYZ_cyc]; exact k13
  have k24 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ < 0 :=
    neg_of_prod (cross_pos_prod FQac FQab FT1 _ _ _ _ h.Qac_M h.Qac_A h.Qab_M h.Qab_A ne2 (phi_prodP p2r p2c)) k21
  have k20 : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, zw⟩ < 0 :=
    neg_of_prod (cross_pos_prod FQac FQab FT1 _ _ _ _ h.Qac_M h.Qac_A h.Qab_M h.Qab_A ne2 (phi_prodP p2w p2c)) k21
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
  intro i j hj1 hj2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact absurd rfl hj1
  | exact absurd (by decide) hj2
  | (simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
     first | exact k02 | exact k03 | exact k04 | exact k13 | exact k14 | exact k10 | exact k21 | exact k24 | exact k20
           | exact k32 | exact k30 | exact k31 | exact k43 | exact k41 | exact k42)

open HFrame in
/-- **N2, weakly beyond, `r2 > b2`, `zv > 0`.** -/
theorem n2_gt (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : 0 < zv)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : b2 < r2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg.toCfg hz
  obtain ⟨hAr, hbr, -⟩ := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun hh => by linarith [hh.2])
  rw [P.hAE] at *
  have hr1 : 0 < r1 := by linarith [cfg.hA]
  have ha3 := cfg.a3_pos (by linarith [P.hAE])
  have hxa := cfg.xa hrb (by linarith [P.hAE]) hbr
  refine Fr.propH_n2_ge (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hA cfg.hs0 cfg.hs1 hz.le P.hzw0
    cfg.hb2 hrb P.hm hr1 ha3 hxa (n2_hcv cfg hrb)
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  tauto

end Type08Sp
end Minimality
