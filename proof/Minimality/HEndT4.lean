module

public import Minimality.HEndN2

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

/-- Straddling for a facet through `g`, `r`, `w` with `v`, `h` beneath it. -/
theorem zw_neg_of (F : Fc) {A b1 b2 r1 r2 zv zw : ℝ} (hA : 0 < A) (hr2 : 0 < r2)
    (hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0) (hzw : zw < zv)
    (hg : F.ev ⟨A, 0, 0⟩ = 0) (hr : F.ev ⟨r1, r2, 0⟩ = 0) (hw : F.ev ⟨0, 0, zw⟩ = 0)
    (hc : F.ev ⟨0, 0, zv⟩ < 0) (hb : F.ev ⟨b1, b2, 0⟩ < 0) : zw < 0 := by
  simp only [Fc.ev] at hg hr hw hc hb
  have hγ : F.c < 0 := by nlinarith
  have key : A * r2 * (F.a * b1 + F.b * b2 + F.d) = F.d * (-((A - r1) * (b2 - r2) + r2 * (b1 - r1))) := by
    linear_combination (A * b2) * hr + (r2 * b1 - r1 * b2) * hg
  have hδ : F.d < 0 := by
    have h1 : A * r2 * (F.a * b1 + F.b * b2 + F.d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hA hr2) (by linarith)
    rw [key] at h1
    have : 0 < -((A - r1) * (b2 - r2) + r2 * (b1 - r1)) := by linarith
    by_contra hc; push Not at hc
    nlinarith
  nlinarith

/-- The coordinate data of case T4 of Proposition 30.4: `b = (0,0,zv)`, `d = (0,0,zw)`,
`c = (A,0,0)`, `c' = (b1,b2,0)`, `b' = (r1,r2,0)`, `a' = (xa,0,za)`, `a = (ua b1, ua b2, a3)`. -/
structure T4Cfg (E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ)
    (FH FQac FT1 FT2 FT3 FT4 : Fc) : Prop where
  hE : 0 < E
  hU : 0 < U
  hzv : 0 < zv
  hzw : zw < zv
  hA : 0 < A
  hb2 : 0 < b2
  hr2 : 0 < r2
  hxa : 0 < xa
  hxaA : xa < A
  hza : zw < za
  hua0 : 0 < ua
  hua1 : ua < 1
  hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0
  -- H = Q_ab: on d, a, c', b; off a', b', c
  H_W : FH.ev ⟨0, 0, zw⟩ = 0
  H_A : FH.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  H_B : FH.ev ⟨b1, b2, 0⟩ = 0
  H_V : FH.ev ⟨0, 0, zv⟩ = 0
  H_P : FH.ev ⟨xa, 0, za⟩ < 0
  H_R : FH.ev ⟨r1, r2, 0⟩ < 0
  H_G : FH.ev ⟨A, 0, 0⟩ < 0
  -- Q_ac: on d, a, b', c; off a', b, c'
  Qac_W : FQac.ev ⟨0, 0, zw⟩ = 0
  Qac_A : FQac.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  Qac_R : FQac.ev ⟨r1, r2, 0⟩ = 0
  Qac_G : FQac.ev ⟨A, 0, 0⟩ = 0
  Qac_P : FQac.ev ⟨xa, 0, za⟩ < 0
  Qac_V : FQac.ev ⟨0, 0, zv⟩ < 0
  Qac_B : FQac.ev ⟨b1, b2, 0⟩ < 0
  -- T1 = (a, c', b'): on a, c', b'; off a', b, c, d
  T1_A : FT1.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  T1_B : FT1.ev ⟨b1, b2, 0⟩ = 0
  T1_R : FT1.ev ⟨r1, r2, 0⟩ = 0
  T1_P : FT1.ev ⟨xa, 0, za⟩ < 0
  T1_V : FT1.ev ⟨0, 0, zv⟩ < 0
  T1_G : FT1.ev ⟨A, 0, 0⟩ < 0
  T1_W : FT1.ev ⟨0, 0, zw⟩ < 0
  -- T2 = (c', b, a'): on c', b, a'; off a, b', c, d
  T2_B : FT2.ev ⟨b1, b2, 0⟩ = 0
  T2_V : FT2.ev ⟨0, 0, zv⟩ = 0
  T2_P : FT2.ev ⟨xa, 0, za⟩ = 0
  T2_A : FT2.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T2_R : FT2.ev ⟨r1, r2, 0⟩ < 0
  T2_G : FT2.ev ⟨A, 0, 0⟩ < 0
  T2_W : FT2.ev ⟨0, 0, zw⟩ < 0
  -- T3 = (c', b', a'): on c', b', a'; off a, b, c, d
  T3_B : FT3.ev ⟨b1, b2, 0⟩ = 0
  T3_R : FT3.ev ⟨r1, r2, 0⟩ = 0
  T3_P : FT3.ev ⟨xa, 0, za⟩ = 0
  T3_A : FT3.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T3_V : FT3.ev ⟨0, 0, zv⟩ < 0
  T3_G : FT3.ev ⟨A, 0, 0⟩ < 0
  T3_W : FT3.ev ⟨0, 0, zw⟩ < 0
  -- T4 = (b', c, a'): on b', c, a'; off a, b, c', d
  T4_R : FT4.ev ⟨r1, r2, 0⟩ = 0
  T4_G : FT4.ev ⟨A, 0, 0⟩ = 0
  T4_P : FT4.ev ⟨xa, 0, za⟩ = 0
  T4_A : FT4.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T4_V : FT4.ev ⟨0, 0, zv⟩ < 0
  T4_B : FT4.ev ⟨b1, b2, 0⟩ < 0
  T4_W : FT4.ev ⟨0, 0, zw⟩ < 0

namespace T4Cfg
variable {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
variable (h : T4Cfg E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem zw_neg : zw < 0 :=
  zw_neg_of FQac h.hA h.hr2 h.hDr h.hzw h.Qac_G h.Qac_R h.Qac_W h.Qac_V h.Qac_B


theorem delta_Qac : FQac.d < 0 := by
  have := h.Qac_V; have := h.Qac_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FQac h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_T1 : FT1.d < 0 := by
  have := h.T1_V; have := h.T1_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FT1 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_T2 : FT2.d < 0 := by
  have := h.T2_V; have := h.T2_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FT2 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inr (by linarith))

theorem delta_T3 : FT3.d < 0 := by
  have := h.T3_V; have := h.T3_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FT3 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_T4 : FT4.d < 0 := by
  have := h.T4_V; have := h.T4_W; simp only [Fc.ev] at *
  exact N2Cfg.delta_neg FT4 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem H_cd : FH.c = 0 ∧ FH.d = 0 := by
  have h1 := h.H_V; have h2 := h.H_W; simp only [Fc.ev] at h1 h2
  have hzw := h.hzw
  have hc : FH.c = 0 := by
    have : FH.c * (zv - zw) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by linarith)
  refine ⟨hc, ?_⟩
  rw [hc] at h1; linarith

theorem H_a_neg : FH.a < 0 := by
  have h1 := h.H_G; simp only [Fc.ev] at h1
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1
  have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem Qac_a_pos : 0 < FQac.a := by
  have h1 := h.Qac_G; simp only [Fc.ev] at h1
  have := h.delta_Qac; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem T4_a_pos : 0 < FT4.a := by
  have h1 := h.T4_G; simp only [Fc.ev] at h1
  have := h.delta_T4; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

/-- `r1 b2 − r2 b1 > 0`. -/
theorem S3_pos : 0 < r1 * b2 - r2 * b1 := by
  have h1 := h.H_B; have h2 := h.H_R; simp only [Fc.ev] at h1 h2
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1 h2
  have ha := h.H_a_neg; have hb2 := h.hb2
  have e : FH.a * (r1 * b2 - r2 * b1) = b2 * (FH.a * r1 + FH.b * r2 + 0 * 0 + 0) -
      r2 * (FH.a * b1 + FH.b * b2 + 0 * 0 + 0) := by ring
  have hneg : FH.a * (r1 * b2 - r2 * b1) < 0 := by
    rw [e, h1]; have := mul_neg_of_pos_of_neg hb2 h2; linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hh]

theorem T1_a_eq : FT1.a * (r1 * b2 - r2 * b1) = (-FT1.d) * (b2 - r2) := by
  have h1 := h.T1_R; have h2 := h.T1_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T3_a_eq : FT3.a * (r1 * b2 - r2 * b1) = (-FT3.d) * (b2 - r2) := by
  have h1 := h.T3_R; have h2 := h.T3_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T1_a_neg_of (hr : b2 < r2) : FT1.a < 0 := by
  have e := h.T1_a_eq; have hS := h.S3_pos; have hd := h.delta_T1
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT1.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T3_a_neg_of (hr : b2 < r2) : FT3.a < 0 := by
  have e := h.T3_a_eq; have hS := h.S3_pos; have hd := h.delta_T3
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT3.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T1_a_pos_of (hr : r2 < b2) : 0 < FT1.a := by
  have e := h.T1_a_eq; have hS := h.S3_pos; have hd := h.delta_T1
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT1.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem T3_a_pos_of (hr : r2 < b2) : 0 < FT3.a := by
  have e := h.T3_a_eq; have hS := h.S3_pos; have hd := h.delta_T3
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT3.d by linarith) (show 0 < b2 - r2 by linarith)]

/-- The sign of `a'`-facet's `x`-coefficient: `α xa zv = −δ (zv − za)`. -/
theorem T2_a_eq : FT2.a * xa * zv = (-FT2.d) * (zv - za) := by
  have h1 := h.T2_V; have h2 := h.T2_P; simp only [Fc.ev] at h1 h2
  linear_combination zv * h2 - za * h1

/-- If `c'` is farther than `b` from the plane of `G`, then `(h,v,a')` is a back face. -/
theorem T2_a_neg_of (hr : b2 < r2) : FT2.a < 0 := by
  have h1 := h.T2_B; have h2 := h.T2_R; simp only [Fc.ev] at h1 h2
  have hS := h.S3_pos; have hd := h.delta_T2
  have key : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) < 0 := by
    have : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) =
        b2 * (FT2.a * r1 + FT2.b * r2 + FT2.c * 0 + FT2.d) -
          r2 * (FT2.a * b1 + FT2.b * b2 + FT2.c * 0 + FT2.d) := by ring
    rw [this, h1]
    have := mul_neg_of_pos_of_neg h.hb2 h2
    linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT2.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T2_a_neg_iff : FT2.a < 0 ↔ za > zv := by
  have e := h.T2_a_eq; have hd := h.delta_T2; have := h.hxa; have := h.hzv
  constructor
  · intro ha
    by_contra hc; push Not at hc
    nlinarith [mul_pos (show 0 < -FT2.a by linarith) (mul_pos h.hxa h.hzv),
      mul_nonneg (show 0 ≤ -FT2.d by linarith) (show 0 ≤ zv - za by linarith)]
  · intro hc
    by_contra ha; push Not at ha
    nlinarith [mul_nonneg ha (mul_pos h.hxa h.hzv).le,
      mul_pos (show 0 < -FT2.d by linarith) (show 0 < za - zv by linarith)]


theorem T2_a_pos_iff : 0 < FT2.a ↔ za < zv := by
  have e := h.T2_a_eq; have hd := h.delta_T2
  constructor
  · intro ha
    by_contra hc; push Not at hc
    nlinarith [mul_pos ha (mul_pos h.hxa h.hzv),
      mul_nonneg (show 0 ≤ -FT2.d by linarith) (show 0 ≤ za - zv by linarith)]
  · intro hc
    by_contra ha; push Not at ha
    nlinarith [mul_nonneg (show 0 ≤ -FT2.a by linarith) (mul_pos h.hxa h.hzv).le,
      mul_pos (show 0 < -FT2.d by linarith) (show 0 < zv - za by linarith)]

end T4Cfg

/-- The rim of case (i) of T4 (`r₂ > b₂`): `b' a' d a`. -/
def rimA (zw r1 r2 xa za ua b1 b2 a3 : ℝ) : ZMod 4 → V3 :=
  ![⟨r1, r2, 0⟩, ⟨xa, 0, za⟩, ⟨0, 0, zw⟩, ⟨ua * b1, ua * b2, a3⟩]

/-- The rim of case (ii) of T4 (`r₂ < b₂`, `z a' > z b`): `c' a' d a`. -/
def rimB (zw b1 b2 xa za ua a3 : ℝ) : ZMod 4 → V3 :=
  ![⟨b1, b2, 0⟩, ⟨xa, 0, za⟩, ⟨0, 0, zw⟩, ⟨ua * b1, ua * b2, a3⟩]

/-- The rim of case (iii) of T4 (`r₂ < b₂`, `z a' < z b`): `c' b d a`. -/
def rimC (zv zw b1 b2 ua a3 : ℝ) : ZMod 4 → V3 :=
  ![⟨b1, b2, 0⟩, ⟨0, 0, zv⟩, ⟨0, 0, zw⟩, ⟨ua * b1, ua * b2, a3⟩]

namespace T4Cfg
variable {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
variable (h : T4Cfg E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem testsA (hr : b2 < r2) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw E U δ) (rimA zw r1 r2 xa za ua b1 b2 a3 i)
          (rimA zw r1 r2 xa za ua b1 b2 a3 (i + 1)) (rimA zw r1 r2 xa za ua b1 b2 a3 j)) ∧
      (∀ i, 0 < σ * tst (vw E U δ) (rimA zw r1 r2 xa za ua b1 b2 a3 i)
          (rimA zw r1 r2 xa za ua b1 b2 a3 (i + 1)) ⟨b1, b2, 0⟩) ∧
      ∀ i, 0 < σ * tst (vw E U δ) (rimA zw r1 r2 xa za ua b1 b2 a3 i)
          (rimA zw r1 r2 xa za ua b1 b2 a3 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hE := h.hE
  have hT4 := eventually_lin_pos E U FT4 hE h.T4_a_pos
  have hT3 := eventually_lin_neg E U FT3 hE (h.T3_a_neg_of hr)
  have hQac := eventually_lin_pos E U FQac hE h.Qac_a_pos
  have hT1 := eventually_lin_neg E U FT1 hE (h.T1_a_neg_of hr)
  have hH := eventually_lin_neg E U FH hE h.H_a_neg
  have hb2 := h.hb2; have hr2 := h.hr2; have hua0 := h.hua0
  have hab : 0 < ua * b2 := mul_pos hua0 hb2
  refine rim_assemble (by norm_num) E U (rimA zw r1 r2 xa za ua b1 b2 a3) ⟨b1, b2, 0⟩ ⟨b1, b2, 0⟩ ?_
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · -- b' → a'  (T4 | T3)
    refine edge4 E U FT4 FT3 _ _ _ 0 ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ ?_ h.T4_R h.T4_P h.T3_R h.T3_P
      h.T3_B h.T4_B h.T4_G h.T3_G (hT4.mono fun _ h => h.le) hT3 ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FT1) h.T1_R h.T1_P
    · exact yok_mk h.T4_W.le h.T3_W.le (Or.inl h.T4_W)
    · exact yok_mk h.T4_A.le h.T3_A.le (Or.inl h.T4_A)
    · exact yok_mk h.T4_B.le h.T3_B.le (Or.inl h.T4_B)
    · exact yok_mk h.T4_B.le h.T3_B.le (Or.inl h.T4_B)
  · -- a' → d : the chord of `G`
    refine edge4_chord E U _ ⟨b1, b2, 0⟩ ⟨b1, b2, 0⟩ 1 rfl rfl h.hza hE ?_ hb2 hb2
    intro j h1 h2
    rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact hr2
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact hab
  · -- d → a  (Qac | H)
    refine edge4 E U FQac FH _ _ _ 2 ⟨0, 0, zv⟩ ⟨A, 0, 0⟩ ?_ h.Qac_W h.Qac_A h.H_W h.H_A
      h.H_V h.Qac_V h.Qac_G h.H_G (hQac.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FT1) h.T1_A h.T1_W).symm
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inr ⟨h.H_R, hQac⟩)
    · exact yok_mk h.Qac_P.le h.H_P.le (Or.inl h.Qac_P)
    · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
    · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
  · -- a → b'  (Qac | T1)
    refine edge4 E U FQac FT1 _ _ _ 3 ⟨b1, b2, 0⟩ ⟨0, 0, zw⟩ ?_ h.Qac_A h.Qac_R h.T1_A h.T1_R
      h.T1_B h.Qac_B h.Qac_W h.T1_W (hQac.mono fun _ h => h.le) hT1 ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FH) h.H_A h.H_R
    · exact yok_mk h.Qac_P.le h.T1_P.le (Or.inl h.Qac_P)
    · exact yok_mk h.Qac_W.le h.T1_W.le (Or.inr ⟨h.T1_W, hQac⟩)
    · exact yok_mk h.Qac_B.le h.T1_B.le (Or.inl h.Qac_B)
    · exact yok_mk h.Qac_B.le h.T1_B.le (Or.inl h.Qac_B)


theorem testsB (hr : r2 < b2) (hz : zv < za) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw E U δ) (rimB zw b1 b2 xa za ua a3 i)
          (rimB zw b1 b2 xa za ua a3 (i + 1)) (rimB zw b1 b2 xa za ua a3 j)) ∧
      (∀ i, 0 < σ * tst (vw E U δ) (rimB zw b1 b2 xa za ua a3 i)
          (rimB zw b1 b2 xa za ua a3 (i + 1)) ⟨r1, r2, 0⟩) ∧
      ∀ i, 0 < σ * tst (vw E U δ) (rimB zw b1 b2 xa za ua a3 i)
          (rimB zw b1 b2 xa za ua a3 (i + 1)) ⟨r1, r2, 0⟩ := by
  have hE := h.hE
  have hT3 := eventually_lin_pos E U FT3 hE (h.T3_a_pos_of hr)
  have hT2 := eventually_lin_neg E U FT2 hE (h.T2_a_neg_iff.mpr hz)
  have hQac := eventually_lin_pos E U FQac hE h.Qac_a_pos
  have hT1 := eventually_lin_pos E U FT1 hE (h.T1_a_pos_of hr)
  have hH := eventually_lin_neg E U FH hE h.H_a_neg
  have hb2 := h.hb2; have hr2 := h.hr2; have hua0 := h.hua0
  have hab : 0 < ua * b2 := mul_pos hua0 hb2
  refine rim_assemble (by norm_num) E U (rimB zw b1 b2 xa za ua a3) ⟨r1, r2, 0⟩ ⟨r1, r2, 0⟩ ?_
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · -- c' → a'  (T3 | T2)
    refine edge4 E U FT3 FT2 _ _ _ 0 ⟨0, 0, zv⟩ ⟨r1, r2, 0⟩ ?_ h.T3_B h.T3_P h.T2_B h.T2_P
      h.T2_V h.T3_V h.T3_R h.T2_R (hT3.mono fun _ h => h.le) hT2 ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FH) h.H_B h.H_P
    · exact yok_mk h.T3_W.le h.T2_W.le (Or.inl h.T3_W)
    · exact yok_mk h.T3_A.le h.T2_A.le (Or.inl h.T3_A)
    · exact yok_mk h.T3_R.le h.T2_R.le (Or.inr ⟨h.T2_R, hT3⟩)
    · exact yok_mk h.T3_R.le h.T2_R.le (Or.inr ⟨h.T2_R, hT3⟩)
  · -- a' → d : the chord of `G`
    refine edge4_chord E U _ ⟨r1, r2, 0⟩ ⟨r1, r2, 0⟩ 1 rfl rfl h.hza hE ?_ hr2 hr2
    intro j h1 h2
    rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact hb2
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact hab
  · -- d → a  (Qac | H)
    refine edge4 E U FQac FH _ _ _ 2 ⟨0, 0, zv⟩ ⟨A, 0, 0⟩ ?_ h.Qac_W h.Qac_A h.H_W h.H_A
      h.H_V h.Qac_V h.Qac_G h.H_G (hQac.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FT1) h.T1_A h.T1_W).symm
    · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
    · exact yok_mk h.Qac_P.le h.H_P.le (Or.inl h.Qac_P)
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inr ⟨h.H_R, hQac⟩)
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inr ⟨h.H_R, hQac⟩)
  · -- a → c'  (T1 | H)
    refine edge4 E U FT1 FH _ _ _ 3 ⟨0, 0, zw⟩ ⟨r1, r2, 0⟩ ?_ h.T1_A h.T1_B h.H_A h.H_B
      h.H_W h.T1_W h.T1_R h.H_R (hT1.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FQac) h.Qac_A h.Qac_B
    · exact yok_mk h.T1_P.le h.H_P.le (Or.inl h.T1_P)
    · exact yok_mk h.T1_W.le h.H_W.le (Or.inl h.T1_W)
    · exact yok_mk h.T1_R.le h.H_R.le (Or.inr ⟨h.H_R, hT1⟩)
    · exact yok_mk h.T1_R.le h.H_R.le (Or.inr ⟨h.H_R, hT1⟩)

theorem testsC (hr : r2 < b2) (hz : za < zv) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw E U δ) (rimC zv zw b1 b2 ua a3 i)
          (rimC zv zw b1 b2 ua a3 (i + 1)) (rimC zv zw b1 b2 ua a3 j)) ∧
      (∀ i, 0 < σ * tst (vw E U δ) (rimC zv zw b1 b2 ua a3 i)
          (rimC zv zw b1 b2 ua a3 (i + 1)) ⟨r1, r2, 0⟩) ∧
      ∀ i, 0 < σ * tst (vw E U δ) (rimC zv zw b1 b2 ua a3 i)
          (rimC zv zw b1 b2 ua a3 (i + 1)) ⟨r1, r2, 0⟩ := by
  have hE := h.hE
  have hT2 := eventually_lin_pos E U FT2 hE (h.T2_a_pos_iff.mpr hz)
  have hQac := eventually_lin_pos E U FQac hE h.Qac_a_pos
  have hT1 := eventually_lin_pos E U FT1 hE (h.T1_a_pos_of hr)
  have hH := eventually_lin_neg E U FH hE h.H_a_neg
  have hG0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ gFace.lin (vw E U δ) :=
    Eventually.of_forall fun δ => by rw [gFace_lin]
  have hb2 := h.hb2; have hr2 := h.hr2; have hua0 := h.hua0
  have hab : 0 < ua * b2 := mul_pos hua0 hb2
  refine rim_assemble (by norm_num) E U (rimC zv zw b1 b2 ua a3) ⟨r1, r2, 0⟩ ⟨r1, r2, 0⟩ ?_
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · -- c' → b  (T2 | H)
    refine edge4 E U FT2 FH _ _ _ 0 ⟨0, 0, zw⟩ ⟨xa, 0, za⟩ ?_ h.T2_B h.T2_V h.H_B h.H_V
      h.H_W h.T2_W h.T2_P h.H_P (hT2.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FT1) h.T1_B h.T1_V
    · exact yok_mk h.T2_W.le h.H_W.le (Or.inl h.T2_W)
    · exact yok_mk h.T2_A.le h.H_A.le (Or.inl h.T2_A)
    · exact yok_mk h.T2_R.le h.H_R.le (Or.inl h.T2_R)
    · exact yok_mk h.T2_R.le h.H_R.le (Or.inl h.T2_R)
  · -- b → d : the edge `vw`  (G | H)
    refine edge4 E U gFace FH _ _ _ 1 ⟨ua * b1, ua * b2, a3⟩ ⟨A, 0, 0⟩ ?_ (gFace_ev0 rfl)
      (gFace_ev0 rfl) h.H_V h.H_W h.H_A (gFace_evneg hab) (gFace_ev0 rfl) h.H_G hG0 hH
      ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FQac) h.Qac_W h.Qac_V).symm
    · exact yok_mk (gFace_evneg hab).le h.H_A.le (Or.inl (gFace_evneg hab))
    · exact yok_mk (gFace_evneg hb2).le h.H_B.le (Or.inl (gFace_evneg hb2))
    · exact yok_mk (gFace_evneg hr2).le h.H_R.le (Or.inl (gFace_evneg hr2))
    · exact yok_mk (gFace_evneg hr2).le h.H_R.le (Or.inl (gFace_evneg hr2))
  · -- d → a  (Qac | H)
    refine edge4 E U FQac FH _ _ _ 2 ⟨0, 0, zv⟩ ⟨A, 0, 0⟩ ?_ h.Qac_W h.Qac_A h.H_W h.H_A
      h.H_V h.Qac_V h.Qac_G h.H_G (hQac.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FT1) h.T1_A h.T1_W).symm
    · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
    · exact yok_mk h.Qac_V.le h.H_V.le (Or.inl h.Qac_V)
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inr ⟨h.H_R, hQac⟩)
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inr ⟨h.H_R, hQac⟩)
  · -- a → c'  (T1 | H)
    refine edge4 E U FT1 FH _ _ _ 3 ⟨0, 0, zw⟩ ⟨r1, r2, 0⟩ ?_ h.T1_A h.T1_B h.H_A h.H_B
      h.H_W h.T1_W h.T1_R h.H_R (hT1.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FQac) h.Qac_A h.Qac_B
    · exact yok_mk h.T1_V.le h.H_V.le (Or.inl h.T1_V)
    · exact yok_mk h.T1_W.le h.H_W.le (Or.inl h.T1_W)
    · exact yok_mk h.T1_R.le h.H_R.le (Or.inr ⟨h.H_R, hT1⟩)
    · exact yok_mk h.T1_R.le h.H_R.le (Or.inr ⟨h.H_R, hT1⟩)


theorem depthA (hA : A < r1) (hb : b1 < r1) (hb0 : b1 ≠ 0) (hnt : ¬ (xa = ua * b1 ∧ za = a3)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (dep (rimA zw r1 r2 xa za ua b1 b2 a3) δ) := by
  have hxa := h.hxa; have hxaA := h.hxaA; have hua0 := h.hua0; have hua1 := h.hua1
  have hAp := h.hA
  have hrp : 0 < r1 := by linarith
  have hr_xa : xa < r1 := by linarith
  have hr_ub : ua * b1 < r1 := by
    rcases lt_or_gt_of_ne hb0 with hn | hp
    · nlinarith
    · nlinarith
  have hub : ua * b1 ≠ 0 := mul_ne_zero hua0.ne' hb0
  have e1 := eventually_pos_affine (A := r1 - xa) (B := za) (Or.inl (by linarith))
  have e2 := eventually_pos_affine (A := xa) (B := zw - za) (Or.inl hxa)
  have e3 := eventually_pos_affine (A := r1 - ua * b1) (B := a3) (Or.inl (by linarith))
  have e4 := eventually_pos_affine (A := r1) (B := zw) (Or.inl hrp)
  have n13 := eventually_depth_ne (p := xa) (P := za) (q := ua * b1) (Q := a3) hnt
  have n23 := eventually_depth_ne (p := 0) (P := zw) (q := ua * b1) (Q := a3)
    (fun h' => hub h'.1.symm)
  have e5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  filter_upwards [e1, e2, e3, e4, n13, n23, e5] with δ h1 h2 h3 h4 m13 m23 h5
  obtain ⟨p0, p1, p2, p3⟩ := zmod4_add_one
  obtain ⟨m0, m1, m2, m3⟩ := zmod4_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) (injective4 (z := dep (rimA zw r1 r2 xa za ua b1 b2 a3) δ)
    ?_ ?_ ?_ ?_ ?_ ?_) 0 ?_
  · show r1 - δ * 0 ≠ xa - δ * za; intro e; linarith
  · show r1 - δ * 0 ≠ 0 - δ * zw; intro e; nlinarith
  · show r1 - δ * 0 ≠ ua * b1 - δ * a3; intro e; linarith
  · show xa - δ * za ≠ 0 - δ * zw; intro e; nlinarith
  · exact m13
  · exact m23
  · intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [m1]; show xa - δ * za < r1 - δ * 0; linarith
    · left; rw [m2]; show 0 - δ * zw < xa - δ * za; linarith
    · right; rw [p3]; show ua * b1 - δ * a3 < r1 - δ * 0; linarith


theorem depthB (hz : zv < za) (hb0 : b1 ≠ 0) (hnt : ¬ (xa = ua * b1 ∧ za = a3)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (dep (rimB zw b1 b2 xa za ua a3) δ) := by
  have hxa := h.hxa; have hua0 := h.hua0; have hua1 := h.hua1; have hzv := h.hzv
  have hub : ua * b1 ≠ 0 := mul_ne_zero hua0.ne' hb0
  have hza0 : za ≠ 0 := by intro h0; linarith
  have n01 := eventually_depth_ne (p := b1) (P := 0) (q := xa) (Q := za)
    (fun h' => hza0 h'.2.symm)
  have n02 := eventually_depth_ne (p := b1) (P := 0) (q := 0) (Q := zw) (fun h' => hb0 h'.1)
  have n03 := eventually_depth_ne (p := b1) (P := 0) (q := ua * b1) (Q := a3) (by
    rintro ⟨h1, -⟩
    apply hb0; nlinarith)
  have n12 := eventually_depth_ne (p := xa) (P := za) (q := 0) (Q := zw) (fun h' => hxa.ne' h'.1)
  have n13 := eventually_depth_ne (p := xa) (P := za) (q := ua * b1) (Q := a3) hnt
  have n23 := eventually_depth_ne (p := 0) (P := zw) (q := ua * b1) (Q := a3)
    (fun h' => hub h'.1.symm)
  have e12 := eventually_pos_affine (A := xa) (B := zw - za) (Or.inl hxa)
  have hinj : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Function.Injective (dep (rimB zw b1 b2 xa za ua a3) δ) := by
    filter_upwards [n01, n02, n03, n12, n13, n23] with δ m01 m02 m03 m12 m13 m23
    exact injective4 m01 m02 m03 m12 m13 m23
  rcases lt_or_gt_of_ne hb0 with hneg | hpos
  · have e3 := eventually_pos_affine (A := -(ua * b1)) (B := a3 - zw) (Or.inl (by nlinarith))
    filter_upwards [hinj, e12, e3] with δ hj h1 h3
    refine uni4_B hj ?_ (Or.inr ?_)
    · show 0 - δ * zw < xa - δ * za; linarith
    · show ua * b1 - δ * a3 < 0 - δ * zw; linarith
  · have e3 := eventually_pos_affine (A := (1 - ua) * b1) (B := a3) (Or.inl (by nlinarith))
    filter_upwards [hinj, e12, e3] with δ hj h1 h3
    refine uni4_B hj ?_ (Or.inl ?_)
    · show 0 - δ * zw < xa - δ * za; linarith
    · show ua * b1 - δ * a3 < b1 - δ * 0; nlinarith

theorem depthC (hb0 : b1 ≠ 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (dep (rimC zv zw b1 b2 ua a3) δ) := by
  have hua0 := h.hua0; have hua1 := h.hua1; have hzvw := h.hzw
  have hub : ua * b1 ≠ 0 := mul_ne_zero hua0.ne' hb0
  have n01 := eventually_depth_ne (p := b1) (P := 0) (q := 0) (Q := zv) (fun h' => hb0 h'.1)
  have n02 := eventually_depth_ne (p := b1) (P := 0) (q := 0) (Q := zw) (fun h' => hb0 h'.1)
  have n03 := eventually_depth_ne (p := b1) (P := 0) (q := ua * b1) (Q := a3) (by
    rintro ⟨h1, -⟩
    apply hb0; nlinarith)
  have n12 := eventually_depth_ne (p := 0) (P := zv) (q := 0) (Q := zw) (fun h' => hzvw.ne' h'.2)
  have n13 := eventually_depth_ne (p := 0) (P := zv) (q := ua * b1) (Q := a3)
    (fun h' => hub h'.1.symm)
  have n23 := eventually_depth_ne (p := 0) (P := zw) (q := ua * b1) (Q := a3)
    (fun h' => hub h'.1.symm)
  have hinj : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Function.Injective (dep (rimC zv zw b1 b2 ua a3) δ) := by
    filter_upwards [n01, n02, n03, n12, n13, n23] with δ m01 m02 m03 m12 m13 m23
    exact injective4 m01 m02 m03 m12 m13 m23
  have e5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨p0, p1, p2, p3⟩ := zmod4_add_one
  obtain ⟨m0, m1, m2, m3⟩ := zmod4_sub_one
  rcases lt_or_gt_of_ne hb0 with hneg | hpos
  · -- the top is `d`
    have e0 := eventually_pos_affine (A := -b1) (B := -zv) (Or.inl (by linarith))
    have e3 := eventually_pos_affine (A := -(ua * b1)) (B := a3 - zw) (Or.inl (by nlinarith))
    filter_upwards [hinj, e0, e3, e5] with δ hj h0 h3 h5
    refine isCyclicUnimodal_of_top (by norm_num) hj 2 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · right; rw [p0]; show b1 - δ * 0 < 0 - δ * zv; linarith
    · right; rw [p1]; show 0 - δ * zv < 0 - δ * zw; nlinarith
    · exact absurd rfl hi
    · left; rw [m3]; show ua * b1 - δ * a3 < 0 - δ * zw; linarith
  · -- the top is `c'`
    have e1 := eventually_pos_affine (A := b1) (B := zv) (Or.inl hpos)
    have e2 := eventually_pos_affine (A := ua * b1) (B := zw - a3) (Or.inl (by nlinarith))
    have e3 := eventually_pos_affine (A := (1 - ua) * b1) (B := a3) (Or.inl (by nlinarith))
    filter_upwards [hinj, e1, e2, e3, e5] with δ hj h1 h2 h3 h5
    refine isCyclicUnimodal_of_top (by norm_num) hj 0 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [m1]; show 0 - δ * zv < b1 - δ * 0; linarith
    · right; rw [p2]; show 0 - δ * zw < ua * b1 - δ * a3; linarith
    · right; rw [p3]; show ua * b1 - δ * a3 < b1 - δ * 0; nlinarith

end T4Cfg

end Minimality
end
