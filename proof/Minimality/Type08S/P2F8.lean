module

public import Minimality.Type08S.P2F7

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- Case A: `b2 < r2`. -/
theorem tp_far_A (N : Norm08 a a' b b' c c' d) {E U zv zw A b1 b2 r1 r2 xa za a3 t : ℝ}
    {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : TpPic a a' b b' c c' d N.F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za a3 t
      FH FQac FT1 FT2 FT3 FT4) (hxt : xa = t * A) (hrb : b2 < r2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hxt
  have Fr := t4_frame N.F N.hd
  have cfg := P.cfg
  have hS3 := cfg.S3_pos
  have hb2 := cfg.hb2
  have hA := cfg.hA
  have hr2 := cfg.hr2
  have hDr := cfg.hDr
  have hrb' : 0 < r2 - b2 := sub_pos.mpr hrb
  have hAr : 0 < A * (r2 - b2) := mul_pos hA hrb'
  set μ : ℝ := (r1 * b2 - r2 * b1 + 1) / (A * (r2 - b2)) with hμ
  have hμe : μ * (A * (r2 - b2)) = r1 * b2 - r2 * b1 + 1 := by
    rw [hμ]; field_simp
  have hμ0 : 0 < μ := by rw [hμ]; exact div_pos (by linarith) hAr
  refine Fr.tp_A (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a)
    (px := -(b1 + μ * A)) (py := -b2) ?_ (by simp) (by simp) (by simp) (by simp)
    P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa hA hb2 hr2 P.ht0 P.ht1 cfg.hzv P.hzw0 P.hm P.hmp hS3
    (by nlinarith) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · nlinarith [mul_pos hμ0 (mul_pos hA hb2)]
  · nlinarith
  · nlinarith


/-- Case B: `r2 ≤ b2`, strictly not beyond. -/
theorem tp_far_B (N : Norm08 a a' b b' c c' d) {E U zv zw A b1 b2 r1 r2 xa za a3 t : ℝ}
    {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : TpPic a a' b b' c c' d N.F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za a3 t
      FH FQac FT1 FT2 FT3 FT4) (hxt : xa = t * A) (hrb : r2 ≤ b2)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hnb : NotBeyondW E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 A 0) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hxt
  subst hE
  have Fr := t4_frame N.F N.hd
  have cfg := P.cfg
  have hS3 := cfg.S3_pos
  have hb2 := cfg.hb2
  have hA := cfg.hA
  have hr2 := cfg.hr2
  have hDr := cfg.hDr
  have q4 : 0 < (-1 : ℝ) * (b1 * 0 - b2 * A) := by nlinarith
  obtain ⟨px, py, t1, t2, hlex⟩ := tilt_sminus (σ := -1) Fr.hee Fr.hNN q4 hnb
  have t1' : 0 < py * b1 - px * b2 := by linarith
  have t2' : 0 < -(py * A) := by linarith
  have key : A * b2 * ((r2 - b2) * px - (r1 - b1) * py) =
      (-(py * A)) * (r1 * b2 - r2 * b1) + (b2 - r2) * A * (py * b1 - px * b2) := by ring
  have t3' : 0 < (r2 - b2) * px - (r1 - b1) * py := by
    have h1 : 0 < A * b2 * ((r2 - b2) * px - (r1 - b1) * py) := by
      rw [key]
      have := mul_pos t2' hS3
      have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hrb) hA.le) t1'.le
      linarith
    by_contra hh; push Not at hh
    nlinarith [mul_pos hA hb2]
  refine Fr.tp_B (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a)
    (px := px) (py := py) ?_ (by simp) (by simp) (by simp) (by simp) (by simp)
    P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa hA hb2 hr2 P.ht0 P.ht1 cfg.hzv P.hzw0 P.hm P.hmp hS3
    (by nlinarith) t1' t2' t3' (by simpa using hlex)
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  tauto

/-- Case C (`r2 ≤ b2`, weakly beyond). -/
theorem tp_far_C (N : Norm08 a a' b b' c c' d) {E U zv zw A b1 b2 r1 r2 xa za a3 t : ℝ}
    {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : TpPic a a' b b' c c' d N.F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za a3 t
      FH FQac FT1 FT2 FT3 FT4) (hxt : xa = t * A) (hrb : r2 ≤ b2)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hwb : WeakBeyond E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hxt
  subst hE
  have Fr := t4_frame N.F N.hd
  have cfg := P.cfg
  have hb2 := cfg.hb2
  have hA := cfg.hA
  have hr2 := cfg.hr2
  rcases hrb.lt_or_eq with hrb | hrb
  · have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN hb2 hwb hrb
    rcases lt_or_ge za zv with hzz | hzz
    · refine Fr.tp_C1 (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp)
        (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa hA P.ht0 P.ht1 cfg.hzv
        P.hzw0 P.hm P.hmp hzz hb2 hrb hb1 hr2
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    · refine Fr.tp_C2 (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp)
        (by simp) (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa hA P.ht0 P.ht1
        cfg.hzv P.hzw0 P.hm P.hmp hzz hb2 hrb hb1 hr2
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · have hne : ¬ (r1 = b1 ∧ r2 = b2) := fun h => by
      have h1 := cfg.T2_B; have h2 := cfg.T2_R
      obtain ⟨e1, e2⟩ := h
      subst e1; subst e2
      linarith
    have hB1 := weakBeyond_B1 Fr.hee Fr.hNN hwb hne
    have hA' : A ≤ r1 := by rw [P.hAE]; exact hB1.1
    have hd1 : b1 < r1 := hB1.2.2 hrb
    have hzz : zv < za := by
      rcases cfg.hzv.lt_or_eq with hz | hz
      · exact (cfg.T2_a_neg_iff hz P.hzw0).mp (cfg.T2_a_neg_of_le hz P.hzw0 hrb.ge)
      · have := P.hmp
        rw [← hz] at this ⊢
        linarith
    refine Fr.tp_C3 (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
      (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp)
      (by simp) (by simp) (by simp) (by simp) P.Φb P.Φa' P.Φc' (by rw [P.Φb', hrb]) P.Φc P.Φd P.Φa
      hA P.ht0 P.ht1 cfg.hzv P.hzw0 P.hm P.hmp hzz hb2 hA' hd1
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

/-- **The far triple tie at `T'`**, from the picture. -/
theorem tp_far_T4 (N : Norm08 a a' b b' c c' d)
    (hfc : N.F.abc'.f c < N.F.abc'.f a') (hfa : N.F.a'bc.f c' = N.F.a'bc.f a)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫) (hzv0 : ⟪c, b - d⟫ ≤ ⟪b, b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, a3, t, FH, FQac, FT1, FT2, FT3, FT4, P, hE⟩ :=
    t4_pic_Tp N.F N.hd hfc hfa htouch hzw0 hzv0
  have Fr := t4_frame N.F N.hd
  have hxt := P.hxt
  rcases lt_or_ge b2 r2 with hrb | hrb
  · exact tp_far_A N P hxt hrb
  · by_cases hnb : NotBeyondW E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 A 0
    · exact tp_far_B N P hxt hrb hE hnb
    · have hwb : WeakBeyond E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 := by
        rw [P.hAE] at hnb
        have hE' : 0 < E := by rw [hE]; exact Fr.hee
        exact weak_of_not_nb hE' Fr.hNN hnb
      exact tp_far_C N P hxt hrb hE hwb

/-- **`Tp_far`** (the residual package of the type-08 `T'` case, `TpFarH`). -/
theorem Tp_far (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (h : WeakFarTp b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hfa, hfc⟩ := Tp_far_hyps N hT'
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, -⟩ := norm08_coordsTp' N hT'
  have hdb : d ≠ b := N.hd.ne.2.2.1
  have hn : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  set n : ℝ := ⟪b - d, b - d⟫ with hnd
  have e1 : ⟪c' - d, b - d⟫ = ⟪a - d, b - d⟫ + β1 * n := by
    have : c' - d = (a - d) + β1 • (b - d) := by rw [hc']; module
    rw [this, inner_add_left, real_inner_smul_left]
  have e2 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb']; module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [inner_sub_left] at e1 e2
  have hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫ := by
    have key : (⟪c, b - d⟫ - ⟪d, b - d⟫) * (α4 + γ4 - 1) = α4 * β1 * n := by
      simp only [inner_sub_left] at *
      nlinarith [h1, h2, e1, e2]
    have hpos : 0 < α4 * β1 * n := mul_pos (mul_pos hα4 hβ1) hn
    have hp : 0 < α4 + γ4 - 1 := by linarith
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hp.le]
  exact tp_far_T4 N hfc hfa ⟨h2.symm, h1⟩ hzw0 (by linarith)

end Type08Sp
end Minimality
