module

public import Minimality.Type08S.GT_Wrap20

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 21: `n2_eq` (N2, weakly beyond, `r2 = b2`, `zv > 0`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

open HFrame in
/-- **N2, weakly beyond, `r2 = b2`, `zv > 0`.** -/
theorem n2_eq (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫) (hz : 0 < zv)
    (hwb : WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2) (hrb : r2 = b2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg.toCfg hz
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by
    have h1 := cfg.H_R; have h2 := cfg.H_B; obtain ⟨e1, e2⟩ := h
    rw [e1, e2] at h1; linarith)
  have hAE := P.hAE
  have hd1 : b1 < r1 := hB1.2.2 hrb
  subst hrb
  have hr1 : 0 < r1 := by linarith [cfg.hA, hB1.1]
  have hA' : A ≤ r1 := by linarith [hB1.1]
  have ha3 := cfg.a3_pos hA'
  have hQa := cfg.Qab_a_zero rfl
  have hxa := cfg.xa2 (le_of_eq hQa) hA' hd1.le
  obtain ⟨hβ, hγ⟩ := cfg.Qab_bc hd1
  have hs0 := cfg.hs0; have hs1 := cfg.hs1; have hb2 := cfg.hb2
  -- orientation in the plane `Q_ab`
  have c1 : 0 < cxy ⟨b1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ ⟨r1, r2, 0⟩ := by
    simp only [cxy]; nlinarith [mul_pos (mul_pos (sub_pos.mpr hs1) hb2) (sub_pos.mpr hd1)]
  have c2 : 0 < cxy ⟨b1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ := by
    have key := plane_aff FQab FH ⟨b1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ hγ.ne'
      cfg.Qab_B cfg.Qab_M cfg.Qab_A cfg.Qab_R cfg.H_B cfg.H_M
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos cfg.H_R.le hc, mul_neg_of_neg_of_pos cfg.H_A c1]
  have c3 : 0 < cxy ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨b1, r2, 0⟩ := by
    have : cxy ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨b1, r2, 0⟩ = cxy ⟨b1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ := by
      simp only [cxy]; ring
    rw [this]; exact c2
  have c4 : 0 < cxy ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ := by
    have key := plane_aff FQab FQac ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨b1, r2, 0⟩ ⟨r1, r2, 0⟩ hγ.ne'
      cfg.Qab_M cfg.Qab_A cfg.Qab_B cfg.Qab_R cfg.Qac_M cfg.Qac_A
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos cfg.Qac_B.le hc, mul_neg_of_neg_of_pos cfg.Qac_R c3]
  have c5 : 0 < cxy ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ := by
    have : cxy ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ ⟨s * b1, s * r2, m3⟩ = cxy ⟨s * b1, s * r2, m3⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩ := by
      simp only [cxy]; ring
    rw [this]; exact c4
  obtain ⟨b0, b1', r2', b3, b4⟩ := zmod5_add_one
  refine Fr.propH_n2_ge_eq2 (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hA hs0 hs1 hz.le P.hzw0
    hb2 P.hm hr1 hd1 ha3 hxa (n2_hcv_eq cfg) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · intro tt htt
    simp only [h5Pts, b0, b1', r2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exact lex_of_tilt (crossYZ_planar FQab _ _ _ cfg.Qab_M cfg.Qab_A cfg.Qab_R hQa hγ.ne')
      (tilt_pos FQab _ _ _ cfg.Qab_M cfg.Qab_A cfg.Qab_R hβ hγ htt c4)
  · intro tt htt
    simp only [h5Pts, b0, b1', r2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exact lex_of_tilt (crossYZ_planar FQab _ _ _ cfg.Qab_A cfg.Qab_R cfg.Qab_M hQa hγ.ne')
      (tilt_pos FQab _ _ _ cfg.Qab_A cfg.Qab_R cfg.Qab_M hβ hγ htt c5)
  · intro tt htt
    simp only [h5Pts, b0, b1', r2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exact lex_of_tilt (crossYZ_planar FQab _ _ _ cfg.Qab_M cfg.Qab_A cfg.Qab_B hQa hγ.ne')
      (tilt_pos FQab _ _ _ cfg.Qab_M cfg.Qab_A cfg.Qab_B hβ hγ htt c3)

end Type08Sp
end Minimality
