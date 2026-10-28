module

public import Minimality.Type08S.GT_Wrap7

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 8: T4 weakly beyond, `r2 != b2`, `zv > 0`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem T4Cfg0.toCfg {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (h : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4) (hz : 0 < zv) :
    T4Cfg E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54⟩ := h
  exact ⟨f0, f1, hz, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54⟩

open HFrame in
/-- **T4, weakly beyond, `r2 > b2`, `za' > zv > 0`** (cycle `(2, b, a', b', a)`). -/
theorem t4_a (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫) (hz : 0 < zv)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : b2 < r2) (hzz : zv < za) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg.toCfg hz
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by linarith [h.2])
  have hxt := P.hxt
  subst hxt
  have hA' : A ≤ r1 := by rw [P.hAE]; exact hB1.1
  have hT3 := cfg.T3_a_neg_of hrb
  have hT4 := cfg.T4_a_pos
  have hT1 := cfg.T1_a_neg_of hrb
  have hQc := cfg.Qac_a_pos
  have hzw := P.hzw0
  have hs0 := cfg.hua0
  have hs1 := cfg.hua1
  have hb2 := cfg.hb2
  have hr2 := cfg.hr2
  have hza0 : 0 < za := by linarith
  have ha3 : a3 < 0 := by nlinarith [P.hm, mul_pos (sub_pos.mpr hs1) (neg_pos.mpr hzw)]
  refine Fr.propH_t4_a (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hA hs0 hs1 P.ht0 P.ht1
    hz.le hzw P.hm P.hmp hzz hb2 hrb hA' hB1.2.1 ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · simp only [t5aPts, quint_2, quint_3, quint_4]
    exact cross_neg_of_planes FT3 FT4 ⟨t * A, 0, za⟩ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ ⟨ua * b1, ua * b2, a3⟩
      cfg.T3_P cfg.T3_R cfg.T4_P cfg.T4_R
      (by simp only [crossYZ]; nlinarith [mul_pos hr2 (show 0 < za - zw by linarith)])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.T3_W hT4, mul_pos_of_neg_of_neg cfg.T4_W hT3])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.T3_A hT4, mul_pos_of_neg_of_neg cfg.T4_A hT3])
  · simp only [t5aPts, quint_3, quint_4, quint_0, quint_2]
    have hub : ua * b2 < r2 := by nlinarith
    exact cross_neg_of_planes FT1 FQac ⟨r1, r2, 0⟩ ⟨ua * b1, ua * b2, a3⟩ ⟨t * A, 0, za⟩ ⟨0, 0, zw⟩
      cfg.T1_R cfg.T1_A cfg.Qac_R cfg.Qac_A
      (by simp only [crossYZ]; nlinarith [mul_pos (sub_pos.2 hub) hza0, mul_neg_of_pos_of_neg hr2 ha3])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.T1_P hQc, mul_pos_of_neg_of_neg cfg.Qac_P hT1])
      (by simp only [Phi]; rw [cfg.Qac_W]; nlinarith [mul_neg_of_neg_of_pos cfg.T1_W hQc])

open HFrame in
/-- **T4, weakly beyond, `r2 < b2`, `za' >= zv > 0`** (cycle `(2, b, a', c', a)`). -/
theorem t4_b (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫) (hz : 0 < zv)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : r2 < b2) (hzz : zv ≤ za) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg.toCfg hz
  have hxt := P.hxt
  subst hxt
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by linarith [h.2])
  have hA' : A ≤ r1 := by rw [P.hAE]; exact hB1.1
  have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN cfg.hb2 hwb hrb
  have hT3 := cfg.T3_a_pos_of hrb
  have hT1 := cfg.T1_a_pos_of hrb
  have hH := cfg.H_a_neg
  have hT2 : FT2.a ≤ 0 := by
    by_contra hh; push Not at hh
    have := cfg.T2_a_pos_iff.mp hh
    linarith
  have hzw := P.hzw0
  have hs0 := cfg.hua0
  have hs1 := cfg.hua1
  have hb2 := cfg.hb2
  have hr2 := cfg.hr2
  have hza0 : 0 < za := by linarith
  have ha3 : a3 < 0 := by nlinarith [P.hm, mul_pos (sub_pos.mpr hs1) (neg_pos.mpr hzw)]
  refine Fr.propH_t4_b (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hA hs0 hs1 P.ht0 P.ht1
    hz.le hzw P.hm P.hmp hzz hb2 hrb hb1 hr2 hA' hB1.2.1 ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · simp only [t5aPts, quint_2, quint_3, quint_4]
    exact cross_neg_of_planes FT2 FT3 ⟨t * A, 0, za⟩ ⟨b1, b2, 0⟩ ⟨0, 0, zw⟩ ⟨ua * b1, ua * b2, a3⟩
      cfg.T2_P cfg.T2_B cfg.T3_P cfg.T3_B
      (by simp only [crossYZ]; nlinarith [mul_pos hb2 (show 0 < za - zw by linarith)])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.T2_W hT3, mul_nonneg_of_nonpos_of_nonpos cfg.T3_W.le hT2])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.T2_A hT3, mul_nonneg_of_nonpos_of_nonpos cfg.T3_A.le hT2])
  · simp only [t5aPts, quint_3, quint_4, quint_0, quint_2]
    exact cross_neg_of_planes FH FT1 ⟨b1, b2, 0⟩ ⟨ua * b1, ua * b2, a3⟩ ⟨t * A, 0, za⟩ ⟨0, 0, zw⟩
      cfg.H_B cfg.H_A cfg.T1_B cfg.T1_A
      (by simp only [crossYZ]; nlinarith [mul_pos (mul_pos (sub_pos.2 hs1) hb2) hza0, mul_neg_of_pos_of_neg hb2 ha3])
      (by simp only [Phi]; nlinarith [mul_neg_of_neg_of_pos cfg.H_P hT1, mul_pos_of_neg_of_neg cfg.T1_P hH])
      (by simp only [Phi]; rw [cfg.H_W]; nlinarith [mul_pos_of_neg_of_neg cfg.T1_W hH])

end Type08Sp
end Minimality
