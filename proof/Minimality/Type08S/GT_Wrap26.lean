module

public import Minimality.Type08S.GT_Wrap25

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 26: `n2_gt0` (N2, weakly beyond, `r2 > b2`, `zv = 0`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

namespace N2Cfg0
variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
  (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) (hz : zv = 0)
include h hz

/-- `cxy (2, a, g) < 0`. -/
theorem cxyMAG : cxy ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨A, 0, 0⟩ < 0 := by
  subst hz
  have hc := h.Qac_c rfl
  have key := plane_aff FQac FQab ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, 0⟩ ⟨A, 0, 0⟩ hc.ne'
    h.Qac_M h.Qac_A h.Qac_C h.Qac_G h.Qab_M h.Qab_A
  have e : cxy ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, 0⟩ = cxy ⟨0, 0, 0⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ := by
    simp only [cxy]; ring
  have g := h.cxyCMA rfl
  rw [← e] at g
  have e1 := h.Qab_C; have e2 := h.Qab_G
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr e1.le) hh, mul_pos_of_neg_of_neg e2 g]

end N2Cfg0

open HFrame in
/-- **N2, weakly beyond, `r2 > b2`, `zv = 0`.** -/
theorem n2_gt0 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : zv = 0)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : b2 < r2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg
  obtain ⟨hAr, hbr, -⟩ := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun hh => by linarith [hh.2])
  have hAE := P.hAE
  have hr1 : 0 < r1 := by linarith [cfg.hA]
  have ha3 := cfg.a3pos hz
  have hxa := cfg.xa0 hz hbr
  have hg := cfg.a2gt hz hrb hbr
  have hcol := cfg.col hz
  have hs0 := cfg.hs0; have hs1 := cfg.hs1; have hb2 := cfg.hb2; have hm3 := cfg.hm3
  have hsb := mul_pos hs0 hb2
  have ha3m : m3 < a3 := by nlinarith
  have hzw := P.hzw0
  set tt : ℝ := m3 / (2 * (s * b2)) with htt
  have htt0 : 0 < tt := by positivity
  have htt1 : tt * (s * b2) < m3 := by
    have : tt * (s * b2) = m3 / 2 := by rw [htt]; field_simp
    rw [this]; linarith
  have hb := cfg.ttc hz htt0 htt1
  have hc := cfg.Qac_c hz
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  have row13 : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 1)
      (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (1 + 1)) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 3) := by
    simp only [h5Pts, b1', quint_1, quint_2, quint_3]
    have cm := cfg.cxyCMA hz
    subst hz
    exact lex_of_tilt (crossYZ_planar FQac _ _ _ cfg.Qac_C cfg.Qac_M cfg.Qac_A (cfg.Qac_a rfl) hc.ne')
      (tilt_neg FQac _ _ _ cfg.Qac_C cfg.Qac_M cfg.Qac_A hc hb cm)
  have row21 : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 2)
      (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (2 + 1)) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 1) := by
    simp only [h5Pts, b2', quint_1, quint_2, quint_3]
    have cm := cfg.cxyCMA hz
    subst hz
    have e : cxy ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨0, 0, 0⟩ = cxy ⟨0, 0, 0⟩ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ := by
      simp only [cxy]; ring
    exact lex_of_tilt (crossYZ_planar FQac _ _ _ cfg.Qac_M cfg.Qac_A cfg.Qac_C (cfg.Qac_a rfl) hc.ne')
      (tilt_neg FQac _ _ _ cfg.Qac_M cfg.Qac_A cfg.Qac_C hc hb (by rw [e]; exact cm))
  have rowg : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 2)
      (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (2 + 1)) ⟨A, 0, 0⟩ := by
    simp only [h5Pts, b2', quint_2, quint_3]
    have cm := cfg.cxyMAG hz
    subst hz
    exact lex_of_tilt (crossYZ_planar FQac _ _ _ cfg.Qac_M cfg.Qac_A cfg.Qac_G (cfg.Qac_a rfl) hc.ne')
      (tilt_neg FQac _ _ _ cfg.Qac_M cfg.Qac_A cfg.Qac_G hc hb cm)
  have hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 (i + 1)) (h5Pts zv zw s b1 b2 m3 a1 a2 a3 r1 r2 j) := by
    intro i j h1 h2
    by_cases hx : (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 1)
    · rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact row13
      · exact row21
    · exact lex_of_cross _ (n2_hcv0 cfg hz hrb hbr i j h1 h2 hx)
  have hma : crossYZ ⟨s * b1, s * b2, m3⟩ ⟨a1, a2, a3⟩ ⟨b1, b2, 0⟩ < 0 := by
    simp only [crossYZ]
    nlinarith [mul_pos (sub_pos.mpr hg) hm3, mul_pos (sub_pos.mpr ha3m) (show 0 < b2 - s * b2 by nlinarith [mul_pos (sub_pos.mpr hs1) hb2])]
  exact Fr.n2_core (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a)
    (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy; tauto)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hA hs0 hs1 hz.ge hzw hb2 P.hm hr1 ha3 hxa tt htt0 hcyc
    (n2g_f hs0 hs1 hz.ge hzw hb2 hrb ha3 P.hm hma)
    (n2g_g0 cfg.hA hs0 hs1 hz.ge hzw hb2 cfg.hr2 ha3 P.hm htt1 rowg)

end Type08Sp
end Minimality
