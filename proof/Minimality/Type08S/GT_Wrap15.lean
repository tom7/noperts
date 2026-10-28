module

public import Minimality.Type08S.GT_Wrap14
public import Minimality.Type08S.GT_Wrap11
public import Minimality.Type08S.GT_Special

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 15: T4, weakly beyond, `r2 = b2` (`propH_t4_a_eq`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

namespace T4Cfg0
variable {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
  (h : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem T3_a_zero (hr : r2 = b2) : FT3.a = 0 := by
  have e := h.T3_a_eq; have hS := h.S3_pos
  have e' : FT3.a * (r1 * b2 - r2 * b1) = 0 := by rw [e, hr]; ring
  exact (mul_eq_zero.mp e').resolve_right hS.ne'

theorem T1_a_zero (hr : r2 = b2) : FT1.a = 0 := by
  have e := h.T1_a_eq; have hS := h.S3_pos
  have e' : FT1.a * (r1 * b2 - r2 * b1) = 0 := by rw [e, hr]; ring
  exact (mul_eq_zero.mp e').resolve_right hS.ne'

end T4Cfg0

open HFrame in
/-- **T4, weakly beyond, `r2 = b2`, `za' > zv`** (cycle `(2, b, a', b', a)`, `propH_t4_a_eq`). -/
theorem t4_eq (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : r2 = b2) (hzz : zv < za) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by have := cfg.T2_B; have := cfg.T2_R; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; linarith)
  have hxt := P.hxt
  subst hxt
  have hA' : A ≤ r1 := by rw [P.hAE]; exact hB1.1
  have hd1 : b1 < r1 := hB1.2.2 hrb
  have hT3 : FT3.a = 0 := cfg.T3_a_zero hrb
  have hT1 : FT1.a = 0 := cfg.T1_a_zero hrb
  have hT4 := cfg.T4_a_pos
  have hQc := cfg.Qac_a_pos
  have hzw := P.hzw0
  have hs0 := cfg.hua0
  have hs1 := cfg.hua1
  have hb2 := cfg.hb2
  have hr2 := cfg.hr2
  have hza0 : 0 < za := by nlinarith [mul_nonneg (sub_pos.2 P.ht1).le cfg.hzv, P.hmp]
  have ha3 : a3 < 0 := by nlinarith [P.hm, mul_pos (sub_pos.mpr hs1) (neg_pos.mpr hzw)]
  refine Fr.propH_t4_a_eq (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' (hrb ▸ P.Φb') P.Φc P.Φd P.Φa cfg.hA hs0 hs1 P.ht0 P.ht1
    cfg.hzv hzw P.hm P.hmp hzz hb2 hA' hd1 ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · simp only [t5aPts, quint_2, quint_3, quint_4]
    subst hrb
    exact cross_neg_of_planes FT3 FT4 ⟨t * A, 0, za⟩ ⟨r1, r2, 0⟩ ⟨0, 0, zw⟩ ⟨ua * b1, ua * r2, a3⟩
      cfg.T3_P cfg.T3_R cfg.T4_P cfg.T4_R
      (by simp only [crossYZ]; nlinarith [mul_pos hr2 (show 0 < za - zw by linarith)])
      (by simp only [Phi]; rw [hT3]; nlinarith [mul_neg_of_neg_of_pos cfg.T3_W hT4])
      (by simp only [Phi]; rw [hT3]; nlinarith [mul_neg_of_neg_of_pos cfg.T3_A hT4])
  · simp only [t5aPts, quint_3, quint_4, quint_0, quint_2]
    subst hrb
    have hub : ua * r2 < r2 := by nlinarith
    exact cross_neg_of_planes FT1 FQac ⟨r1, r2, 0⟩ ⟨ua * b1, ua * r2, a3⟩ ⟨t * A, 0, za⟩ ⟨0, 0, zw⟩
      cfg.T1_R cfg.T1_A cfg.Qac_R cfg.Qac_A
      (by simp only [crossYZ]; nlinarith [mul_pos (sub_pos.2 hub) hza0, mul_neg_of_pos_of_neg hr2 ha3])
      (by simp only [Phi]; rw [hT1]; nlinarith [mul_neg_of_neg_of_pos cfg.T1_P hQc])
      (by simp only [Phi]; rw [cfg.Qac_W, hT1]; nlinarith [mul_neg_of_neg_of_pos cfg.T1_W hQc])

end Type08Sp
end Minimality
