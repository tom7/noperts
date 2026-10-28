module

public import Minimality.Type08S.GT_Wrap23
public import Minimality.Type08S.GT_H

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 24: N2, weakly beyond, `r2 < b2`, `zv = 0` (S2): `a` hidden by the tilt on the edge `(c, 2)`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
section N2lt0
variable {zv zw s b1 b2 z2 t : ℝ} {a1 a2 a3 : ℝ}

theorem h4_a0
    (u0 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 0) (h4Pts zv zw s b1 b2 z2 1) ⟨a1, a2, a3⟩))
    (r1 : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 1)
        (h4Pts zv zw s b1 b2 z2 (1 + 1)) ⟨a1, a2, a3⟩)
    (u2 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 2) (h4Pts zv zw s b1 b2 z2 3) ⟨a1, a2, a3⟩))
    (u3 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 3) (h4Pts zv zw s b1 b2 z2 0) ⟨a1, a2, a3⟩)) :
    ∀ i : ZMod 4,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 i)
        (h4Pts zv zw s b1 b2 z2 (i + 1)) ⟨a1, a2, a3⟩ := by
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [b0]; left; simp only [LexTest, tst, hdet, crossYZ] at u0 ⊢; nlinarith
  · exact r1
  · rw [b2']; left; simp only [LexTest, tst, hdet, crossYZ] at u2 ⊢; nlinarith
  · rw [b3]; left; simp only [LexTest, tst, hdet, crossYZ] at u3 ⊢; nlinarith

end N2lt0
end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Proposition H, N2, `b2 > r2`** (cycle `(a', c, 2, b)`).  `r` weakly beyond enters only
through `b1 > 0` (Lemma 1.1 (B2')); `c'` and `b'` are hidden by the strict picture, `a` by the four
strict tests `u0`–`u3` (it lies strictly inside the screen quadrilateral). -/
theorem propH_n2_lt0 {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw b1 b2 z2 A r1 r2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hm : mP ∈ V) (hf : fP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, z2⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hb1 : 0 < b1) (hr2 : 0 < r2) (hrb : r2 < b2) (hz2 : (1 - s) * zv < z2)
    (u0' : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 0) (h4Pts zv zw s b1 b2 z2 1) ⟨a1, a2, a3⟩))
    (hrow1 : ∀ t : ℝ, 0 < t → t * (s * b2) < z2 → LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 1) (h4Pts zv zw s b1 b2 z2 (1 + 1)) ⟨a1, a2, a3⟩)
    (u2 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 2) (h4Pts zv zw s b1 b2 z2 3) ⟨a1, a2, a3⟩))
    (u3 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 3) (h4Pts zv zw s b1 b2 z2 0) ⟨a1, a2, a3⟩)) :
    IsRupert V := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have himg : ∀ i : ZMod 4, hfΦ vb g u0 fG (quad wP cP mP fP i) = h4Pts zv zw s b1 b2 z2 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [quad_0, Φw]; rfl
    · rw [quad_1, Φc]; rfl
    · rw [quad_2, Φm]; rfl
    · rw [quad_3, Φf]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  set tt : ℝ := z2 / (2 * (s * b2)) with htt
  have htt0 : 0 < tt := by positivity
  have htt1 : tt * (s * b2) < z2 := by
    have : tt * (s * b2) = z2 / 2 := by rw [htt]; field_simp
    rw [this]; linarith
  refine Fr.rupert_coords V (k := 4) (by norm_num) (quad wP cP mP fP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, -tt⟩ (Or.inl one_ne_zero) ?_ ?_ QH4 QH4_open (fun z c hc => QH4_smul hc)
    (fun z K => QH4_shift K) (fun z hinj => QH4_unimodal hinj) ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hw, hc, hm, hf]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact h4_cyc hs0 hs1 hzv hzw hb2 hz2 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · rw [h, Φr]; exact h4_cp hs0 hs1 hzv hzw hb2 hr2 hrb hz2 i
    · rw [h, Φg]; exact h4_bp hA hs0 hs1 hzv hzw hb2 hz2 htt1 i
    · exact absurd h (hyx 0)
    · rw [h, Φa]; exact h4_a0 u0' (hrow1 _ htt0 htt1) u2 u3 i
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 4), lin E M U c (hfΦ vb g u0 fG (quad wP cP mP fP i)) =
        lin E M U c (h4Pts zv zw s b1 b2 z2 i) := by
      intro c i; rw [himg i]
    have s0 : h4Pts zv zw s b1 b2 z2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : h4Pts zv zw s b1 b2 z2 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : h4Pts zv zw s b1 b2 z2 2 = ⟨s * b1, s * b2, z2⟩ := rfl
    have s3 : h4Pts zv zw s b1 b2 z2 3 = ⟨b1, b2, 0⟩ := rfl
    set L := fun i => lin E M U ⟨1, 0, 0⟩ (h4Pts zv zw s b1 b2 z2 i) with hLd
    set W := fun i => lin E M U ⟨0, -1, -tt⟩ (h4Pts zv zw s b1 b2 z2 i) with hWd
    have l10 : L 1 - L 0 = 0 := by
      simp only [hLd, s0, s1, lin]; ring
    have w10 : 0 < W 0 - W 1 := by
      simp only [hWd, s0, s1, lin]
      have : 0 < tt * (zv - zw) / U := div_pos (mul_pos htt0 (by linarith)) hU
      have e : 0 / E * 0 + (-1) / M * 0 + (-tt) / U * zw - (0 / E * 0 + (-1) / M * 0 + (-tt) / U * zv)
          = tt * (zv - zw) / U := by field_simp; ring
      linarith
    have l21 : 0 < L 2 - L 1 := by
      simp only [hLd, s1, s2, lin]
      have := div_pos (mul_pos hs0 hb1) hE
      have e : 1 / E * (s * b1) + 0 / M * (s * b2) + 0 / U * z2 - (1 / E * 0 + 0 / M * 0 + 0 / U * zv)
          = s * b1 / E := by field_simp; ring
      rw [e]; exact this
    have l30 : 0 < L 3 - L 0 := by
      simp only [hLd, s0, s3, lin]
      have := div_pos hb1 hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * 0 - (1 / E * 0 + 0 / M * 0 + 0 / U * zw) = b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have l32 : 0 < L 3 - L 2 := by
      simp only [hLd, s2, s3, lin]
      have := div_pos (mul_pos hs1' hb1) hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * 0 -
          (1 / E * (s * b1) + 0 / M * (s * b2) + 0 / U * z2) = (1 - s) * b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have k1 := eventually_pos_affine (A := L 0 - L 1) (B := W 0 - W 1) (Or.inr ⟨by linarith, w10⟩)
    have k2 := eventually_pos_affine (A := L 2 - L 1) (B := W 2 - W 1) (Or.inl l21)
    have k3 := eventually_pos_affine (A := L 3 - L 0) (B := W 3 - W 0) (Or.inl l30)
    have k4 := eventually_pos_affine (A := L 3 - L 2) (B := W 3 - W 2) (Or.inl l32)
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QH4, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩


end HFrame

namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

open HFrame in
/-- **N2, weakly beyond, `r2 < b2`, `zv = 0`.** -/
theorem n2_lt0 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : zv = 0)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : r2 < b2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg
  have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN cfg.hb2 hwb hrb
  have hHa := cfg.H_a_neg
  have hQb := cfg.Qab_apos hz hrb
  have hT2 := cfg.T2_apos hz hrb
  have hzw := P.hzw0
  have hs0 := cfg.hs0
  have hs1 := cfg.hs1
  have hb2 := cfg.hb2
  have hm3 := cfg.hm3
  have hr2 := cfg.hr2
  have ha2 := cfg.ha2
  have hq2 := cfg.Qab_W; have hq3 := cfg.T2_C
  have e1 := cfg.H_A
  refine Fr.propH_n2_lt0 (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hA hs0 hs1 hz.ge hzw hb2 hb1 hr2 hrb
    P.hm ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · simp only [h4Pts, quad_0, quad_1, crossYZ]
    nlinarith [mul_pos (show 0 < zv - zw by linarith [cfg.hzw]) ha2]
  · intro t ht htt
    obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
    simp only [h4Pts, b1', quad_1, quad_2]
    have hc := cfg.Qac_c hz
    have Qac_M := cfg.Qac_M; have d0 := cfg.Qac_d hz; have a0 := cfg.Qac_a hz
    simp only [Fc.ev] at Qac_M
    rw [d0, a0] at Qac_M
    have hb : t * FQac.c < -FQac.b := by
      have hsb := mul_pos hs0 hb2
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hsb.le (show 0 ≤ t * FQac.c + FQac.b by linarith), mul_pos hc hm3,
        mul_pos hc (sub_pos.mpr htt)]
    subst hz
    exact lex_of_tilt (crossYZ_planar FQac _ _ _ cfg.Qac_C cfg.Qac_M cfg.Qac_A (cfg.Qac_a rfl) hc.ne')
      (tilt_neg FQac _ _ _ cfg.Qac_C cfg.Qac_M cfg.Qac_A hc hb (cfg.cxyCMA rfl))
  · simp only [h4Pts, quad_2, quad_3]
    have := cross_neg_of_planes FH FQab ⟨s * b1, s * b2, m3⟩ ⟨b1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨a1, a2, a3⟩
      cfg.H_M cfg.H_B cfg.Qab_M cfg.Qab_B
      (by simp only [crossYZ]; nlinarith [mul_pos hb2 hm3, mul_pos hs0 hb2, mul_pos (show 0 < 1 - s by linarith) hb2,
        mul_pos (mul_pos (show 0 < 1 - s by linarith) hb2) (show 0 < m3 - zw by linarith)])
      (by simp only [Phi]; rw [cfg.H_W]; nlinarith [mul_pos_of_neg_of_neg hq2 hHa])
      (by simp only [Phi]; rw [cfg.Qab_A]; nlinarith [mul_neg_of_neg_of_pos e1 hQb])
    linarith
  · simp only [h4Pts, quad_3, quad_0]
    have := cross_neg_of_planes FH FT2 ⟨b1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨a1, a2, a3⟩
      cfg.H_B cfg.H_W cfg.T2_B cfg.T2_W
      (by simp only [crossYZ]; nlinarith [mul_pos hb2 (show 0 < zv - zw by linarith [cfg.hzw])])
      (by simp only [Phi]; rw [cfg.H_C]; nlinarith [mul_pos_of_neg_of_neg hq3 hHa])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos e1 hT2, mul_pos_of_neg_of_neg cfg.T2_A hHa])
    linarith

end Type08Sp
end Minimality
