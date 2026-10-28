module

public import Minimality.Type08S.GT_Wrap10

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 11: T4 weakly beyond for all `zv >= 0` (S2 included), `r2 != b2`; final `gt_far_T4`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

open HFrame in
/-- **T4, weakly beyond, `r2 > b2`, `za' > zv >= 0`** (cycle `(2, b, a', b', a)`). -/
theorem t4_a0 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : b2 < r2) (hzz : zv < za) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg
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
  have hza0 : 0 < za := by nlinarith [mul_nonneg (sub_pos.2 P.ht1).le cfg.hzv, P.hmp]
  have ha3 : a3 < 0 := by nlinarith [P.hm, mul_pos (sub_pos.mpr hs1) (neg_pos.mpr hzw)]
  refine Fr.propH_t4_a (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hA hs0 hs1 P.ht0 P.ht1
    cfg.hzv hzw P.hm P.hmp hzz hb2 hrb hA' hB1.2.1 ?_ ?_
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
/-- **T4, weakly beyond, `r2 < b2`, `za' >= zv >= 0`** (cycle `(2, b, a', c', a)`). -/
theorem t4_b0 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : r2 < b2) (hzz : zv ≤ za) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg
  have hxt := P.hxt
  subst hxt
  have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb (fun h => by linarith [h.2])
  have hA' : A ≤ r1 := by rw [P.hAE]; exact hB1.1
  have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN cfg.hb2 hwb hrb
  have hT3 := cfg.T3_a_pos_of hrb
  have hT1 := cfg.T1_a_pos_of hrb
  have hH := cfg.H_a_neg
  have hT2 : FT2.a ≤ 0 := by
    have h1 := cfg.T2_V; have h2 := cfg.T2_P; have h3 := cfg.T2_W
    simp only [Fc.ev] at h1 h2 h3
    have hc : 0 < FT2.c := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (show 0 ≤ zv - zw by linarith [cfg.hzw])]
    by_contra hh; push Not at hh
    nlinarith [mul_pos hh cfg.hxa, mul_nonneg hc.le (sub_nonneg.2 hzz)]
  have hzw := P.hzw0
  have hs0 := cfg.hua0
  have hs1 := cfg.hua1
  have hb2 := cfg.hb2
  have hr2 := cfg.hr2
  have hza0 : 0 < za := by nlinarith [mul_nonneg (sub_pos.2 P.ht1).le cfg.hzv, P.hmp]
  have ha3 : a3 < 0 := by nlinarith [P.hm, mul_pos (sub_pos.mpr hs1) (neg_pos.mpr hzw)]
  refine Fr.propH_t4_b (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hA hs0 hs1 P.ht0 P.ht1
    cfg.hzv hzw P.hm P.hmp hzz hb2 hrb hb1 hr2 hA' hB1.2.1 ?_ ?_
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

/-- **The far triple tie, T4** (`z_w < tie <= z_v`; `z_v = 0` is S2): Rupert, or `PicFailT4`
(`r2 = b2`). -/
theorem gt_far_T4 (N : Norm08 a a' b b' c c' d)
    (hfc : N.F.abc'.f c < N.F.abc'.f a') (hfc' : N.F.a'bc.f c' < N.F.a'bc.f a)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫) (hzv0 : ⟪c, b - d⟫ ≤ ⟪b, b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ PicFailT4 N.F d := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, ua, a3, t, FH, FQac, FT1, FT2, FT3, FT4, P, hE⟩ :=
    t4_pic N.F N.hd hfc hfc' htouch hzw0 hzv0
  have Fr := t4_frame N.F N.hd
  by_cases hnb : NotBeyondW E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 A 0
  · exact Or.inl (t4_sminus N.F N.hd P hE hnb)
  · have hwb : WeakBeyond E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
    · rcases lt_or_ge za zv with hzz | hzz
      · exact Or.inl (t4_c N.F N.hd P hE hwb hrb hzz)
      · exact Or.inl (t4_b0 N.F N.hd P hE hwb hrb hzz)
    · exact Or.inr ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, ua, a3, t, FH, FQac, FT1, FT2, FT3, FT4,
        P, hE, hwb, hrb⟩
    · have hzz : zv < za := by
        rcases P.cfg.hzv.lt_or_eq with hz | hz
        · have cfg := P.cfg.toCfg hz
          exact cfg.T2_a_neg_iff.mp (cfg.T2_a_neg_of hrb)
        · have := P.hmp
          rw [← hz] at this ⊢
          linarith
      exact Or.inl (t4_a0 N.F N.hd P hE hwb hrb hzz)

end Type08Sp
end Minimality
