module

public import Minimality.Type08S.GT_Wrap26
public import Minimality.Type08S.GT_Special

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 27: `n2_eq0` (N2, weakly beyond, `r2 = b2`, `zv = 0`): `2` and `a` coincide on the
screen (`a2 = s b2`, `a3 = m3`), `b` coincides with `c'`; then `gt_far_N2''`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

section Fe
variable {zw s b1 b2 z2 r1 a1 tt : ℝ}

/-- `b` over `c'` for the flat pentagon at `r2 = b2`. -/
theorem n2f_fe (hs0 : 0 < s) (hs1 : s < 1) (hzw : zw < 0) (hb2 : 0 < b2) (hz2 : 0 < z2)
    (hd : b1 < r1) (hxa : s * b1 < a1) (htt0 : 0 < tt) (hbr : tt * b2 < -zw) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 b2 i)
        (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 b2 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hd1 : 0 < a1 - s * b1 := by linarith
  have hd2 : 0 < r1 - b1 := by linarith
  have hw : 0 < -zw := neg_pos.mpr hzw
  have p1 := mul_pos hb2 hw
  have p2 := mul_pos hb2 hz2
  have tc := mul_pos hd1 (show 0 < z2 + tt * ((1 - s) * b2) by
    nlinarith [mul_pos htt0 (mul_pos (sub_pos.mpr hs1) hb2)])
  have t3 := mul_pos hd2 (show 0 < z2 + tt * ((1 - s) * b2) by
    nlinarith [mul_pos htt0 (mul_pos (sub_pos.mpr hs1) hb2)])
  have t4 := mul_pos hd2 (show 0 < -zw - tt * b2 by linarith)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end Fe

open HFrame in
/-- **N2, weakly beyond, `r2 = b2`, `zv = 0`.** -/
theorem n2_eq0 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : zv = 0)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : r2 = b2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by
    have h1 := cfg.H_R; have h2 := cfg.H_B; obtain ⟨e1, e2⟩ := h
    rw [e1, e2] at h1; linarith)
  have hAE := P.hAE
  have hd1 : b1 < r1 := hB1.2.2 hrb
  have hr1 : 0 < r1 := by linarith [cfg.hA, hB1.1]
  have hxa := cfg.xa0 hz hd1.le
  have ha2e := cfg.a2eq hz hrb hd1.le
  have hcol := cfg.col hz
  have hs0 := cfg.hs0; have hs1 := cfg.hs1; have hb2 := cfg.hb2; have hm3 := cfg.hm3
  have hsb := mul_pos hs0 hb2
  have ha3e : a3 = m3 := by
    rw [ha2e] at hcol
    have : s * b2 * (m3 - a3) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hsb.ne'
    linarith
  have hzw := P.hzw0
  have Φr' : hfΦ c b' (c - a') F.a'b'c.f c' = ⟨r1, b2, 0⟩ := by rw [P.Φc', hrb]
  have Φa' : hfΦ c b' (c - a') F.a'b'c.f a = ⟨a1, s * b2, m3⟩ := by rw [P.Φa, ha2e, ha3e]
  have hsr : s * b2 < r2 := by rw [hrb]; nlinarith [mul_pos (sub_pos.mpr hs1) hb2]
  obtain ⟨tt, htt0, htt1, htt2⟩ : ∃ tt : ℝ, 0 < tt ∧ tt * (s * b2) < m3 ∧ tt * b2 < -zw := by
    refine ⟨min (m3 / (2 * (s * b2))) (-zw / (2 * b2)), lt_min (by positivity) (by
      have : 0 < -zw := neg_pos.mpr hzw
      positivity), ?_, ?_⟩
    · have h1 := min_le_left (m3 / (2 * (s * b2))) (-zw / (2 * b2))
      have := mul_le_mul_of_nonneg_right h1 hsb.le
      have e : m3 / (2 * (s * b2)) * (s * b2) = m3 / 2 := by field_simp
      linarith
    · have h1 := min_le_right (m3 / (2 * (s * b2))) (-zw / (2 * b2))
      have := mul_le_mul_of_nonneg_right h1 hb2.le
      have e : -zw / (2 * b2) * b2 = -zw / 2 := by field_simp
      have : 0 < -zw := neg_pos.mpr hzw
      linarith
  subst hz
  have hsr' : s * b2 < b2 := by nlinarith [mul_pos (sub_pos.mpr hs1) hb2]
  exact Fr.n2_core (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a)
    (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy; tauto)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    P.Φc P.Φd P.Φb Φr' P.Φb' P.Φa' Φa' cfg.hA hs0 hs1 le_rfl hzw hb2 P.hm hr1 hm3 hxa tt htt0
    (n2f_cyc hs0 hzw hb2 hm3 hsr' hxa htt1 htt0) (n2f_fe hs0 hs1 hzw hb2 hm3 hd1 hxa htt0 htt2)
    (n2f_g cfg.hA hs0 hzw hb2 hm3 hsr' hxa htt1)

end Type08Sp
end Minimality
