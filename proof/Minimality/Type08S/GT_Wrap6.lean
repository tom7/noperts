module

public import Minimality.Type08S.GT_Wrap5

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 6: N2, weakly beyond, `r2 < b2` (Proposition H via `propH_n2_lt`), `zv > 0`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem N2Cfg0.toCfg {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hz : 0 < zv) :
    N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55⟩ := h
  exact ⟨f0, f1, hz, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55⟩

open HFrame in
/-- **N2, weakly beyond, `r2 < b2`, `zv > 0`.** -/
theorem n2_lt (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : 0 < zv)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : r2 < b2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg.toCfg hz
  have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN cfg.hb2 hwb hrb
  have hHa := cfg.H_a_neg
  have hQc := cfg.Qac_a_pos
  have hQb := cfg.Qab_a_pos_of hrb
  have hT2 := cfg.T2_a_pos_of hrb
  have hzw := P.hzw0
  have hs0 := cfg.hs0
  have hs1 := cfg.hs1
  have hb2 := cfg.hb2
  have hm3 := cfg.hm3
  have hr2 := cfg.hr2
  have ha2 := cfg.ha2
  have hq1 := cfg.Qac_W; have hq2 := cfg.Qab_W; have hq3 := cfg.T2_C
  have e1 := cfg.H_A; have e2 := cfg.Qab_A; have e3 := cfg.Qac_A
  have e4 := cfg.T2_A; have e5 := cfg.Qab_C
  refine Fr.propH_n2_lt (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hA hs0 hs1 hz.le hzw hb2 hb1 hr2 hrb
    P.hm ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · simp only [h4Pts, quad_0, quad_1, crossYZ]
    nlinarith [mul_pos (show 0 < zv - zw by linarith) ha2]
  · simp only [h4Pts, quad_1, quad_2]
    have := cross_neg_of_planes FH FQac ⟨0, 0, zv⟩ ⟨s * b1, s * b2, m3⟩ ⟨0, 0, zw⟩ ⟨a1, a2, a3⟩
      cfg.H_C cfg.H_M cfg.Qac_C cfg.Qac_M
      (by simp only [crossYZ]; nlinarith [mul_pos hs0 hb2, mul_pos (mul_pos hs0 hb2) (show 0 < zv - zw by linarith)])
      (by simp only [Phi]; rw [cfg.H_W]; nlinarith [mul_pos_of_neg_of_neg hq1 hHa])
      (by simp only [Phi]; rw [cfg.Qac_A]; nlinarith [mul_neg_of_neg_of_pos e1 hQc])
    linarith
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
      (by simp only [crossYZ]; nlinarith [mul_pos hb2 (show 0 < zv - zw by linarith)])
      (by simp only [Phi]; rw [cfg.H_C]; nlinarith [mul_pos_of_neg_of_neg hq3 hHa])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos e1 hT2, mul_pos_of_neg_of_neg e4 hHa])
    linarith

end Type08Sp
end Minimality
