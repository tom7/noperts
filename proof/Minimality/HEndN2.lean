module

public import Minimality.HEnd

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

/-- The coordinate data of case N2 of Proposition 30.4 (`FEWER-FACES-PROOFS.md` §30): the
vertices `c = (0,0,zv)`, `a' = (0,0,zw)`, `b' = (A,0,0)`, `b = (b1,b2,0)`, `c' = (r1,r2,0)`,
`d = (s b1, s b2, m3)`, `a = (a1,a2,a3)` and the facets `H = a'bc`, `Q_ab = abc'`, `Q_ac = ab'c`,
`T1 = ab'c'`, `T2 = a'bc'`, `T3 = a'b'c'` (the facet `G = a'b'c` is `y = 0`, `K ⊂ {y ≥ 0}`). -/
structure N2Cfg (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ)
    (FH FQab FQac FT1 FT2 FT3 : Fc) : Prop where
  hE : 0 < E
  hU : 0 < U
  hzv : 0 < zv
  hzw : zw < zv
  hA : 0 < A
  hb2 : 0 < b2
  hr2 : 0 < r2
  ha2 : 0 < a2
  hs0 : 0 < s
  hs1 : s < 1
  hm3 : 0 < m3
  hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0
  hTa1 : (A - r1) * (a2 - r2) + r2 * (a1 - r1) < 0
  hTa2 : (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) < 0
  H_M : FH.ev ⟨s * b1, s * b2, m3⟩ = 0
  H_B : FH.ev ⟨b1, b2, 0⟩ = 0
  H_W : FH.ev ⟨0, 0, zw⟩ = 0
  H_C : FH.ev ⟨0, 0, zv⟩ = 0
  H_A : FH.ev ⟨a1, a2, a3⟩ < 0
  H_G : FH.ev ⟨A, 0, 0⟩ < 0
  H_R : FH.ev ⟨r1, r2, 0⟩ < 0
  Qab_M : FQab.ev ⟨s * b1, s * b2, m3⟩ = 0
  Qab_A : FQab.ev ⟨a1, a2, a3⟩ = 0
  Qab_R : FQab.ev ⟨r1, r2, 0⟩ = 0
  Qab_B : FQab.ev ⟨b1, b2, 0⟩ = 0
  Qab_C : FQab.ev ⟨0, 0, zv⟩ < 0
  Qab_W : FQab.ev ⟨0, 0, zw⟩ < 0
  Qab_G : FQab.ev ⟨A, 0, 0⟩ < 0
  Qac_M : FQac.ev ⟨s * b1, s * b2, m3⟩ = 0
  Qac_A : FQac.ev ⟨a1, a2, a3⟩ = 0
  Qac_G : FQac.ev ⟨A, 0, 0⟩ = 0
  Qac_C : FQac.ev ⟨0, 0, zv⟩ = 0
  Qac_W : FQac.ev ⟨0, 0, zw⟩ < 0
  Qac_B : FQac.ev ⟨b1, b2, 0⟩ < 0
  Qac_R : FQac.ev ⟨r1, r2, 0⟩ < 0
  T1_A : FT1.ev ⟨a1, a2, a3⟩ = 0
  T1_R : FT1.ev ⟨r1, r2, 0⟩ = 0
  T1_G : FT1.ev ⟨A, 0, 0⟩ = 0
  T1_W : FT1.ev ⟨0, 0, zw⟩ < 0
  T1_B : FT1.ev ⟨b1, b2, 0⟩ < 0
  T1_C : FT1.ev ⟨0, 0, zv⟩ < 0
  T1_M : FT1.ev ⟨s * b1, s * b2, m3⟩ < 0
  T2_R : FT2.ev ⟨r1, r2, 0⟩ = 0
  T2_B : FT2.ev ⟨b1, b2, 0⟩ = 0
  T2_W : FT2.ev ⟨0, 0, zw⟩ = 0
  T2_A : FT2.ev ⟨a1, a2, a3⟩ < 0
  T2_G : FT2.ev ⟨A, 0, 0⟩ < 0
  T2_C : FT2.ev ⟨0, 0, zv⟩ < 0
  T2_M : FT2.ev ⟨s * b1, s * b2, m3⟩ < 0
  T3_R : FT3.ev ⟨r1, r2, 0⟩ = 0
  T3_G : FT3.ev ⟨A, 0, 0⟩ = 0
  T3_W : FT3.ev ⟨0, 0, zw⟩ = 0
  T3_A : FT3.ev ⟨a1, a2, a3⟩ < 0
  T3_B : FT3.ev ⟨b1, b2, 0⟩ < 0
  T3_C : FT3.ev ⟨0, 0, zv⟩ < 0
  T3_M : FT3.ev ⟨s * b1, s * b2, m3⟩ < 0

/-! ### Scalar algebra of Lemma 30.3 -/

theorem n2_pos_of_mul {x y : ℝ} (hy : 0 < y) (h : 0 < x * y) : 0 < x := pos_of_mul_pos_left h hy.le

theorem n2_beta1 {A r1 r2 β δ : ℝ} (hA : 0 < A) (hr2 : 0 < r2) (hAr : A < r1) (hδ : δ < 0)
    (e : A * β * r2 + δ * (A - r1) < 0) : β < 0 := by
  have h1 : 0 < δ * (A - r1) := mul_pos_of_neg_of_neg hδ (by linarith)
  have h2 : A * β * r2 < 0 := by linarith
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (mul_pos hA hr2).le hc]

theorem n2_edgeH {b1 b2 t1 t2 α β : ℝ} (hb2 : 0 < b2) (hα : α < 0) (e : α * b1 + β * b2 = 0)
    (h : α * t1 + β * t2 < 0) : b2 * t1 - b1 * t2 > 0 := by
  have : α * (b2 * t1 - b1 * t2) < 0 := by
    have e2 : α * (b2 * t1 - b1 * t2) = b2 * (α * t1 + β * t2) - t2 * (α * b1 + β * b2) := by ring
    rw [e2, e]; nlinarith
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (neg_nonneg.mpr hα.le) (neg_nonneg.mpr hc)]

theorem n2_t1_pos {zv b1 b2 t1 t2 t3 α1 β1 γ1 δ1 α2 β2 γ2 δ2 : ℝ} (hzv : 0 < zv) (hb2 : 0 < b2)
    (d1 : δ1 < 0) (d2 : δ2 < 0) (hα1 : 0 < α1) (hα2 : α2 < 0) (hγ1 : 0 < γ1) (hγ2 : 0 < γ2)
    (hβ1 : β1 < 0) (hβ2 : 0 < β2)
    (Qac_C : α1 * 0 + β1 * 0 + γ1 * zv + δ1 = 0)
    (Qac_B : α1 * b1 + β1 * b2 + γ1 * 0 + δ1 < 0)
    (Qab_B : α2 * b1 + β2 * b2 + γ2 * 0 + δ2 = 0)
    (Qab_C : α2 * 0 + β2 * 0 + γ2 * zv + δ2 < 0)
    (E1 : α1 * t1 + β1 * t2 + γ1 * t3 = 0) (E2 : α2 * t1 + β2 * t2 + γ2 * t3 = 0)
    (hH : b2 * t1 - b1 * t2 > 0) : 0 < t1 := by
  have hc1 : α2 * γ1 - γ2 * α1 < 0 := by nlinarith [mul_pos hγ2 hα1, mul_neg_of_neg_of_pos hα2 hγ1]
  have hc2 : 0 < β2 * γ1 - γ2 * β1 := by nlinarith [mul_pos hβ2 hγ1, mul_pos hγ2 (neg_pos.mpr hβ1)]
  have hlin : (α2 * γ1 - γ2 * α1) * t1 + (β2 * γ1 - γ2 * β1) * t2 = 0 := by
    linear_combination (-γ2) * E1 + γ1 * E2
  have hK : 0 < b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1) := by
    have e : b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1) =
        γ1 * (α2 * b1 + β2 * b2) - γ2 * (α1 * b1 + β1 * b2) := by ring
    rw [e]
    have e1 : α2 * b1 + β2 * b2 = -δ2 := by linarith
    have e2 : α1 * b1 + β1 * b2 < -δ1 := by linarith
    have e3 : γ1 * zv = -δ1 := by linarith
    have e4 : γ2 * zv < -δ2 := by linarith
    rw [e1]
    -- zv * (γ1 (−δ2) − γ2 (..)) > zv γ1 (−δ2) + γ2 zv δ1 = −δ1(−δ2) + δ1 γ2 zv = δ1 (δ2 + γ2 zv) > 0
    have : 0 < zv * (γ1 * -δ2 - γ2 * (α1 * b1 + β1 * b2)) := by
      nlinarith [mul_pos hγ2 (show 0 < -δ1 - (α1 * b1 + β1 * b2) by linarith),
        mul_pos (neg_pos.mpr d1) (show 0 < -δ2 - γ2 * zv by linarith), mul_pos hγ2 hzv]
    exact pos_of_mul_pos_right this hzv.le
  have key : (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1)) * t1 =
      (β2 * γ1 - γ2 * β1) * (b2 * t1 - b1 * t2) := by
    linear_combination b1 * hlin
  have : 0 < (b2 * (β2 * γ1 - γ2 * β1) + b1 * (α2 * γ1 - γ2 * α1)) * t1 := by
    rw [key]; exact mul_pos hc2 hH
  exact pos_of_mul_pos_right this hK.le

/-- The facet `G`: `y = 0` (`f = −y`). -/
def gFace : Fc := ⟨0, -1, 0, 0⟩

theorem gFace_ev (p : V3) : gFace.ev p = -p.y := by simp [gFace, Fc.ev]

theorem gFace_lin (E U δ : ℝ) : gFace.lin (vw E U δ) = 0 := by simp [gFace, Fc.lin, vw]

theorem gFace_ev0 {p : V3} (h : p.y = 0) : gFace.ev p = 0 := by rw [gFace_ev, h]; simp

theorem gFace_evneg {p : V3} (h : 0 < p.y) : gFace.ev p < 0 := by rw [gFace_ev]; linarith

/-- The rim of case 1 (`r₂ > b₂`): `c' a d c a'`. -/
def rim1 (zv zw r1 r2 s b1 b2 m3 a1 a2 a3 : ℝ) : ZMod 5 → V3 :=
  ![⟨r1, r2, 0⟩, ⟨a1, a2, a3⟩, ⟨s * b1, s * b2, m3⟩, ⟨0, 0, zv⟩, ⟨0, 0, zw⟩]

/-- The rim of case 2 (`b₂ > r₂`): `b d c a'`. -/
def rim2 (zv zw s b1 b2 m3 : ℝ) : ZMod 4 → V3 :=
  ![⟨b1, b2, 0⟩, ⟨s * b1, s * b2, m3⟩, ⟨0, 0, zv⟩, ⟨0, 0, zw⟩]

theorem yok_mk {E U : ℝ} {F₁ F₂ : Fc} {Y : V3} (h1 : F₁.ev Y ≤ 0) (h2 : F₂.ev Y ≤ 0)
    (h : F₁.ev Y < 0 ∨ (F₂.ev Y < 0 ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < F₁.lin (vw E U δ))) :
    YOk E U F₁ F₂ Y := ⟨h1, h2, h⟩

namespace N2Cfg
variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}

/-- Straddling: `zw < 0`. -/
theorem zw_neg (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3) :
    zw < 0 := by
  have hg := h.T3_G
  have hr := h.T3_R
  have hw := h.T3_W
  have hc := h.T3_C
  have hb := h.T3_B
  simp only [Fc.ev] at hg hr hw hc hb
  have hA := h.hA
  have hr2 := h.hr2
  have hDr := h.hDr
  -- c < 0 : the z-coefficient of T3
  have hγ : FT3.c < 0 := by nlinarith [h.hzw]
  -- δ < 0
  have key : A * r2 * (FT3.a * b1 + FT3.b * b2 + FT3.d) = FT3.d * (-( (A - r1) * (b2 - r2) + r2 * (b1 - r1))) := by
    linear_combination (A * b2) * hr + (r2 * b1 - r1 * b2) * hg
  have hδ : FT3.d < 0 := by
    have h1 : A * r2 * (FT3.a * b1 + FT3.b * b2 + FT3.d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hA hr2) (by linarith)
    rw [key] at h1
    have : 0 < -((A - r1) * (b2 - r2) + r2 * (b1 - r1)) := by linarith
    by_contra hc; push Not at hc
    nlinarith
  nlinarith

/-- A facet with `C`, `W` on or beneath it, one strictly, has negative constant term. -/
theorem delta_neg (F : Fc) {zv zw : ℝ} (hzv : 0 < zv) (hzw : zw < 0)
    (hC : F.c * zv + F.d ≤ 0) (hW : F.c * zw + F.d ≤ 0)
    (hs : F.c * zv + F.d < 0 ∨ F.c * zw + F.d < 0) : F.d < 0 := by
  have e : F.d * (zv - zw) = zv * (F.c * zw + F.d) + (-zw) * (F.c * zv + F.d) := by ring
  have hneg : F.d * (zv - zw) < 0 := by
    rw [e]
    rcases hs with h | h
    · nlinarith [mul_nonneg hzv.le (show 0 ≤ -(F.c * zw + F.d) by linarith),
        mul_pos (show 0 < -zw by linarith) (show 0 < -(F.c * zv + F.d) by linarith)]
    · nlinarith [mul_pos hzv (show 0 < -(F.c * zw + F.d) by linarith),
        mul_nonneg (show 0 ≤ -zw by linarith) (show 0 ≤ -(F.c * zv + F.d) by linarith)]
  have hpos : 0 < zv - zw := by linarith
  by_contra hc; push Not at hc
  nlinarith

variable (h : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3)
include h

theorem delta_T1 : FT1.d < 0 := by
  have := h.T1_C; have := h.T1_W; simp only [Fc.ev] at *
  exact delta_neg FT1 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_T3 : FT3.d < 0 := by
  have := h.T3_C; have := h.T3_W; simp only [Fc.ev] at *
  exact delta_neg FT3 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_Qac : FQac.d < 0 := by
  have := h.Qac_C; have := h.Qac_W; simp only [Fc.ev] at *
  exact delta_neg FQac h.hzv h.zw_neg (by linarith) (by linarith) (Or.inr (by linarith))

theorem delta_Qab : FQab.d < 0 := by
  have := h.Qab_C; have := h.Qab_W; simp only [Fc.ev] at *
  exact delta_neg FQab h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem delta_T2 : FT2.d < 0 := by
  have := h.T2_C; have := h.T2_W; simp only [Fc.ev] at *
  exact delta_neg FT2 h.hzv h.zw_neg (by linarith) (by linarith) (Or.inl (by linarith))

theorem H_cd : FH.c = 0 ∧ FH.d = 0 := by
  have h1 := h.H_C; have h2 := h.H_W; simp only [Fc.ev] at h1 h2
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

theorem T1_a_pos : 0 < FT1.a := by
  have h1 := h.T1_G; simp only [Fc.ev] at h1
  have := h.delta_T1; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem T3_a_pos : 0 < FT3.a := by
  have h1 := h.T3_G; simp only [Fc.ev] at h1
  have := h.delta_T3; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem Qac_a_pos : 0 < FQac.a := by
  have h1 := h.Qac_G; simp only [Fc.ev] at h1
  have := h.delta_Qac; have := h.hA
  by_contra hh; push Not at hh
  nlinarith

/-- `r1 b2 − r2 b1 > 0`: the shadow of `H` is on the side of `g`. -/
theorem S3_pos : 0 < r1 * b2 - r2 * b1 := by
  have h1 := h.H_B; have h2 := h.H_R; simp only [Fc.ev] at h1 h2
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1 h2
  have ha := h.H_a_neg; have hb2 := h.hb2
  -- a (r1 b2 − r2 b1) = b2 (a r1 + b r2) − r2 (a b1 + b b2)
  have e : FH.a * (r1 * b2 - r2 * b1) = b2 * (FH.a * r1 + FH.b * r2 + 0 * 0 + 0) -
      r2 * (FH.a * b1 + FH.b * b2 + 0 * 0 + 0) := by ring
  have hneg : FH.a * (r1 * b2 - r2 * b1) < 0 := by
    rw [e, h1]; have := mul_neg_of_pos_of_neg hb2 h2; linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hh]

theorem Qab_a_eq : FQab.a * (r1 * b2 - r2 * b1) = (-FQab.d) * (b2 - r2) := by
  have h1 := h.Qab_R; have h2 := h.Qab_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem T2_a_eq : FT2.a * (r1 * b2 - r2 * b1) = (-FT2.d) * (b2 - r2) := by
  have h1 := h.T2_R; have h2 := h.T2_B; simp only [Fc.ev] at h1 h2
  linear_combination b2 * h1 - r2 * h2

theorem Qab_a_neg_of (hr : b2 < r2) : FQab.a < 0 := by
  have e := h.Qab_a_eq
  have hS := h.S3_pos
  have hd := h.delta_Qab
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FQab.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem T2_a_neg_of (hr : b2 < r2) : FT2.a < 0 := by
  have e := h.T2_a_eq
  have hS := h.S3_pos
  have hd := h.delta_T2
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_pos (show 0 < -FT2.d by linarith) (show 0 < r2 - b2 by linarith)]

theorem Qab_a_pos_of (hr : r2 < b2) : 0 < FQab.a := by
  have e := h.Qab_a_eq
  have hS := h.S3_pos
  have hd := h.delta_Qab
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FQab.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem T2_a_pos_of (hr : r2 < b2) : 0 < FT2.a := by
  have e := h.T2_a_eq
  have hS := h.S3_pos
  have hd := h.delta_T2
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg (neg_nonneg.mpr hh) hS.le, mul_pos (show 0 < -FT2.d by linarith) (show 0 < b2 - r2 by linarith)]

theorem tests1 (hr : b2 < r2) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw E U δ) (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 i)
          (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 (i + 1))
          (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 j)) ∧
      ∀ i, 0 < σ * tst (vw E U δ) (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 i)
          (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hE := h.hE
  have hT1 := eventually_lin_pos E U FT1 hE h.T1_a_pos
  have hT3 := eventually_lin_pos E U FT3 hE h.T3_a_pos
  have hQac := eventually_lin_pos E U FQac hE h.Qac_a_pos
  have hQab := eventually_lin_neg E U FQab hE (h.Qab_a_neg_of hr)
  have hT2 := eventually_lin_neg E U FT2 hE (h.T2_a_neg_of hr)
  have hH := eventually_lin_neg E U FH hE h.H_a_neg
  have hG0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ gFace.lin (vw E U δ) :=
    Eventually.of_forall fun δ => by rw [gFace_lin]
  have hb2 := h.hb2; have hr2 := h.hr2; have ha2 := h.ha2; have hs0 := h.hs0
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  obtain ⟨σ, hσ⟩ := rim_assemble (by norm_num) E U (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3)
    ⟨b1, b2, 0⟩ ⟨b1, b2, 0⟩ (by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · -- c' → a  (T1 | Qab)
      refine edge5 E U FT1 FQab _ _ _ 0 ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ ?_ h.T1_R h.T1_A h.Qab_R h.Qab_A
        h.Qab_B h.T1_B h.T1_G h.Qab_G (hT1.mono fun _ h => h.le) hQab ?_ ?_ ?_ ?_ ?_
      · exact ne_of_ev (F := FT2) h.T2_R h.T2_A
      · exact yok_mk h.T1_M.le h.Qab_M.le (Or.inl h.T1_M)
      · exact yok_mk h.T1_C.le h.Qab_C.le (Or.inl h.T1_C)
      · exact yok_mk h.T1_W.le h.Qab_W.le (Or.inl h.T1_W)
      · exact yok_mk h.T1_B.le h.Qab_B.le (Or.inl h.T1_B)
      · exact yok_mk h.T1_B.le h.Qab_B.le (Or.inl h.T1_B)
    · -- a → d  (Qac | Qab)
      refine edge5 E U FQac FQab _ _ _ 1 ⟨r1, r2, 0⟩ ⟨0, 0, zv⟩ ?_ h.Qac_A h.Qac_M
        h.Qab_A h.Qab_M h.Qab_R h.Qac_R h.Qac_C h.Qab_C (hQac.mono fun _ h => h.le) hQab
        ?_ ?_ ?_ ?_ ?_
      · exact ne_of_ev (F := FT1) h.T1_A h.T1_M
      · exact yok_mk h.Qac_C.le h.Qab_C.le (Or.inr ⟨h.Qab_C, hQac⟩)
      · exact yok_mk h.Qac_W.le h.Qab_W.le (Or.inl h.Qac_W)
      · exact yok_mk h.Qac_R.le h.Qab_R.le (Or.inl h.Qac_R)
      · exact yok_mk h.Qac_B.le h.Qab_B.le (Or.inl h.Qac_B)
      · exact yok_mk h.Qac_B.le h.Qab_B.le (Or.inl h.Qac_B)
    · -- d → c  (Qac | H)
      refine edge5 E U FQac FH _ _ _ 2 ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ ?_ h.Qac_M h.Qac_C
        h.H_M h.H_C h.H_B h.Qac_B h.Qac_G h.H_G (hQac.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_ ?_
      · exact ne_of_ev (F := FQab) h.Qab_M h.Qab_C
      · exact yok_mk h.Qac_W.le h.H_W.le (Or.inl h.Qac_W)
      · exact yok_mk h.Qac_R.le h.H_R.le (Or.inl h.Qac_R)
      · exact yok_mk h.Qac_A.le h.H_A.le (Or.inr ⟨h.H_A, hQac⟩)
      · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
      · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
    · -- c → a'  (G | H)
      refine edge5 E U gFace FH _ _ _ 3 ⟨s * b1, s * b2, m3⟩ ⟨A, 0, 0⟩ ?_ (gFace_ev0 rfl)
        (gFace_ev0 rfl) h.H_C h.H_W h.H_M (gFace_evneg hsb) (gFace_ev0 rfl) h.H_G hG0 hH
        ?_ ?_ ?_ ?_ ?_
      · exact ne_of_ev (F := FQac) h.Qac_C h.Qac_W
      · exact yok_mk (gFace_evneg hr2).le h.H_R.le (Or.inl (gFace_evneg hr2))
      · exact yok_mk (gFace_evneg ha2).le h.H_A.le (Or.inl (gFace_evneg ha2))
      · exact yok_mk (gFace_evneg hsb).le h.H_M.le (Or.inl (gFace_evneg hsb))
      · exact yok_mk (gFace_evneg hb2).le h.H_B.le (Or.inl (gFace_evneg hb2))
      · exact yok_mk (gFace_evneg hb2).le h.H_B.le (Or.inl (gFace_evneg hb2))
    · -- a' → c'  (T3 | T2)
      refine edge5 E U FT3 FT2 _ _ _ 4 ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ ?_ h.T3_W h.T3_R h.T2_W h.T2_R
        h.T2_B h.T3_B h.T3_G h.T2_G (hT3.mono fun _ h => h.le) hT2 ?_ ?_ ?_ ?_ ?_
      · exact (ne_of_ev (F := FT1) h.T1_R h.T1_W).symm
      · exact yok_mk h.T3_A.le h.T2_A.le (Or.inl h.T3_A)
      · exact yok_mk h.T3_M.le h.T2_M.le (Or.inl h.T3_M)
      · exact yok_mk h.T3_C.le h.T2_C.le (Or.inl h.T3_C)
      · exact yok_mk h.T3_B.le h.T2_B.le (Or.inl h.T3_B)
      · exact yok_mk h.T3_B.le h.T2_B.le (Or.inl h.T3_B))
  exact ⟨σ, hσ.mono fun δ hδ => ⟨hδ.1, hδ.2.1⟩⟩

/-- `r` is the farthest corner in `x`: `a` lies in the cone of the shadow at `r`. -/
theorem a1_lt_r1 (hA : A < r1) (hb : b1 < r1) : a1 < r1 := by
  have hD := h.hDr; have h1 := h.hTa1; have h2 := h.hTa2
  have key : ((A - r1) * (b2 - r2) + r2 * (b1 - r1)) * (a1 - r1) =
      ((a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1)) * (A - r1) +
        ((A - r1) * (a2 - r2) + r2 * (a1 - r1)) * (b1 - r1) := by ring
  by_contra hc; push Not at hc
  nlinarith [mul_pos_of_neg_of_neg h2 (show A - r1 < 0 by linarith),
    mul_pos_of_neg_of_neg h1 (show b1 - r1 < 0 by linarith),
    mul_nonneg (neg_nonneg.mpr hD.le) (sub_nonneg.mpr hc)]

/-- **Lemma 30.3.**  `a` is deeper than the cap `d` along `e`: `x(a) > x(d)`. -/
theorem m1_lt_a1 (hr : b2 < r2) (hA : A < r1) (hb : b1 < r1) : s * b1 < a1 := by
  have Qac_G := h.Qac_G; have Qac_C := h.Qac_C; have Qac_M := h.Qac_M; have Qac_A := h.Qac_A
  have Qac_R := h.Qac_R; have Qac_B := h.Qac_B
  have Qab_R := h.Qab_R; have Qab_B := h.Qab_B; have Qab_M := h.Qab_M; have Qab_A := h.Qab_A
  have Qab_C := h.Qab_C
  have H_B := h.H_B; have H_A := h.H_A; have H_M := h.H_M
  obtain ⟨Hc, Hd⟩ := h.H_cd
  simp only [Fc.ev] at Qac_G Qac_C Qac_M Qac_A Qac_R Qac_B Qab_R Qab_B Qab_M Qab_A Qab_C H_B H_A H_M
  rw [Hc, Hd] at H_B H_A H_M
  have hα1 : 0 < FQac.a := h.Qac_a_pos
  have hα2 : FQab.a < 0 := h.Qab_a_neg_of hr
  have hHα := h.H_a_neg
  have d1 := h.delta_Qac; have d2 := h.delta_Qab
  have hS3 := h.S3_pos
  have hβ2S : FQab.b * (r1 * b2 - r2 * b1) = (-FQab.d) * (r1 - b1) := by
    linear_combination (-b1) * Qab_R + r1 * Qab_B
  have hγ1 : 0 < FQac.c := n2_pos_of_mul h.hzv (by linarith)
  have hγ2 : 0 < FQab.c := by
    have e : FQab.c * m3 = -(1 - s) * FQab.d := by linear_combination Qab_M - s * Qab_B
    exact n2_pos_of_mul h.hm3 (by rw [e]; nlinarith [h.hs1])
  have hβ1 : FQac.b < 0 := by
    have e : A * FQac.b * r2 + FQac.d * (A - r1) < 0 := by
      nlinarith [Qac_G, Qac_R, h.hA]
    exact n2_beta1 h.hA h.hr2 hA d1 e
  have hβ2 : 0 < FQab.b := n2_pos_of_mul hS3 (by rw [hβ2S]; exact mul_pos (neg_pos.mpr d2) (sub_pos.mpr hb))
  -- the edge `d a`
  have E1 : FQac.a * (a1 - s * b1) + FQac.b * (a2 - s * b2) + FQac.c * (a3 - m3) = 0 := by
    linear_combination Qac_A - Qac_M
  have E2 : FQab.a * (a1 - s * b1) + FQab.b * (a2 - s * b2) + FQab.c * (a3 - m3) = 0 := by
    linear_combination Qab_A - Qab_M
  have hH : b2 * (a1 - s * b1) - b1 * (a2 - s * b2) > 0 := by
    have e : FH.a * b1 + FH.b * b2 = 0 := by linarith
    have hh : FH.a * (a1 - s * b1) + FH.b * (a2 - s * b2) < 0 := by
      have : FH.a * (s * b1) + FH.b * (s * b2) = 0 := by linear_combination s * e
      linarith
    exact n2_edgeH h.hb2 hHα e hh
  have := n2_t1_pos h.hzv h.hb2 d1 d2 hα1 hα2 hγ1 hγ2 hβ1 hβ2 Qac_C Qac_B Qab_B Qab_C E1 E2 hH
  linarith


theorem depth1_pos (hr : b2 < r2) (hA : A < r1) (hb : b1 < r1) (hb1 : 0 < b1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal
      (dep (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3) δ) := by
  have F6 := h.a1_lt_r1 hA hb
  have F7 := h.m1_lt_a1 hr hA hb
  have hs0 := h.hs0
  have hzvw := h.hzw
  have hsb : 0 < s * b1 := mul_pos hs0 hb1
  have e1 := eventually_pos_affine (A := r1 - a1) (B := a3) (Or.inl (by linarith))
  have e2 := eventually_pos_affine (A := a1 - s * b1) (B := m3 - a3) (Or.inl (by linarith))
  have e3 := eventually_pos_affine (A := s * b1) (B := zw - m3) (Or.inl hsb)
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  filter_upwards [e1, e2, e3, e4] with δ h1 h2 h3 h4
  refine uni5_chain ?_ ?_ ?_ ?_
  · show a1 - δ * a3 < r1 - δ * 0; linarith
  · show s * b1 - δ * m3 < a1 - δ * a3; linarith
  · show 0 - δ * zw < s * b1 - δ * m3; linarith
  · show 0 - δ * zv < 0 - δ * zw; nlinarith

theorem depth1_neg (hA : A < r1) (hb : b1 < r1) (hb1 : b1 < 0)
    (hn2 : ¬ (a1 = s * b1 ∧ a3 = m3)) (hn3 : ¬ (a1 = 0 ∧ a3 = zv))
    (hn4 : ¬ (a1 = 0 ∧ a3 = zw)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal
      (dep (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3) δ) := by
  have F6 := h.a1_lt_r1 hA hb
  have hs0 := h.hs0
  have hzvw := h.hzw
  have hsb : s * b1 < 0 := mul_neg_of_pos_of_neg hs0 hb1
  have hrp : 0 < r1 := by linarith [h.hA]
  have e1 := eventually_pos_affine (A := r1 - a1) (B := a3) (Or.inl (by linarith))
  have e2 := eventually_pos_affine (A := -(s * b1)) (B := m3 - zv) (Or.inl (by linarith))
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have e5 := eventually_pos_affine (A := r1) (B := zw) (Or.inl hrp)
  have n12 := eventually_depth_ne (p := a1) (P := a3) (q := s * b1) (Q := m3) hn2
  have n13 := eventually_depth_ne (p := a1) (P := a3) (q := 0) (Q := zv) hn3
  have n14 := eventually_depth_ne (p := a1) (P := a3) (q := 0) (Q := zw) hn4
  filter_upwards [e1, e2, e4, e5, n12, n13, n14] with δ h1 h2 h4 h5 m12 m13 m14
  refine uni5_valley ?_ ?_ ?_ ?_ ?_
  · refine injective5 (z := dep (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3) δ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · show r1 - δ * 0 ≠ a1 - δ * a3; intro e; linarith
    · show r1 - δ * 0 ≠ s * b1 - δ * m3; intro e; nlinarith
    · show r1 - δ * 0 ≠ 0 - δ * zv; intro e; nlinarith
    · show r1 - δ * 0 ≠ 0 - δ * zw; intro e; nlinarith
    · exact m12
    · exact m13
    · exact m14
    · show s * b1 - δ * m3 ≠ 0 - δ * zv; intro e; nlinarith
    · show s * b1 - δ * m3 ≠ 0 - δ * zw; intro e; nlinarith
    · show 0 - δ * zv ≠ 0 - δ * zw; intro e; nlinarith
  · show a1 - δ * a3 < r1 - δ * 0; linarith
  · show s * b1 - δ * m3 < 0 - δ * zv; linarith
  · show 0 - δ * zv < 0 - δ * zw; nlinarith
  · show 0 - δ * zw < r1 - δ * 0; linarith

theorem tests2 (hr : r2 < b2) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw E U δ) (rim2 zv zw s b1 b2 m3 i) (rim2 zv zw s b1 b2 m3 (i + 1))
          (rim2 zv zw s b1 b2 m3 j)) ∧
      (∀ i, 0 < σ * tst (vw E U δ) (rim2 zv zw s b1 b2 m3 i) (rim2 zv zw s b1 b2 m3 (i + 1))
          ⟨r1, r2, 0⟩) ∧
      ∀ i, 0 < σ * tst (vw E U δ) (rim2 zv zw s b1 b2 m3 i) (rim2 zv zw s b1 b2 m3 (i + 1))
          ⟨a1, a2, a3⟩ := by
  have hE := h.hE
  have hT2 := eventually_lin_pos E U FT2 hE (h.T2_a_pos_of hr)
  have hQac := eventually_lin_pos E U FQac hE h.Qac_a_pos
  have hQab := eventually_lin_pos E U FQab hE (h.Qab_a_pos_of hr)
  have hH := eventually_lin_neg E U FH hE h.H_a_neg
  have hG0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ gFace.lin (vw E U δ) :=
    Eventually.of_forall fun δ => by rw [gFace_lin]
  have hb2 := h.hb2; have hr2 := h.hr2; have ha2 := h.ha2; have hs0 := h.hs0
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  refine rim_assemble (by norm_num) E U (rim2 zv zw s b1 b2 m3) ⟨r1, r2, 0⟩ ⟨a1, a2, a3⟩ ?_
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · -- b → d  (Qab | H)
    refine edge4 E U FQab FH _ _ _ 0 ⟨0, 0, zv⟩ ⟨r1, r2, 0⟩ ?_ h.Qab_B h.Qab_M h.H_B h.H_M
      h.H_C h.Qab_C h.Qab_R h.H_R (hQab.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FQac) h.Qac_M h.Qac_B).symm
    · exact yok_mk h.Qab_C.le h.H_C.le (Or.inl h.Qab_C)
    · exact yok_mk h.Qab_W.le h.H_W.le (Or.inl h.Qab_W)
    · exact yok_mk h.Qab_R.le h.H_R.le (Or.inr ⟨h.H_R, hQab⟩)
    · exact yok_mk h.Qab_A.le h.H_A.le (Or.inr ⟨h.H_A, hQab⟩)
  · -- d → c  (Qac | H)
    refine edge4 E U FQac FH _ _ _ 1 ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ ?_ h.Qac_M h.Qac_C h.H_M h.H_C
      h.H_B h.Qac_B h.Qac_G h.H_G (hQac.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FQab) h.Qab_M h.Qab_C
    · exact yok_mk h.Qac_W.le h.H_W.le (Or.inl h.Qac_W)
    · exact yok_mk h.Qac_B.le h.H_B.le (Or.inl h.Qac_B)
    · exact yok_mk h.Qac_R.le h.H_R.le (Or.inl h.Qac_R)
    · exact yok_mk h.Qac_A.le h.H_A.le (Or.inr ⟨h.H_A, hQac⟩)
  · -- c → a'  (G | H)
    refine edge4 E U gFace FH _ _ _ 2 ⟨s * b1, s * b2, m3⟩ ⟨A, 0, 0⟩ ?_ (gFace_ev0 rfl)
      (gFace_ev0 rfl) h.H_C h.H_W h.H_M (gFace_evneg hsb) (gFace_ev0 rfl) h.H_G hG0 hH
      ?_ ?_ ?_ ?_
    · exact ne_of_ev (F := FQac) h.Qac_C h.Qac_W
    · exact yok_mk (gFace_evneg hb2).le h.H_B.le (Or.inl (gFace_evneg hb2))
    · exact yok_mk (gFace_evneg hsb).le h.H_M.le (Or.inl (gFace_evneg hsb))
    · exact yok_mk (gFace_evneg hr2).le h.H_R.le (Or.inl (gFace_evneg hr2))
    · exact yok_mk (gFace_evneg ha2).le h.H_A.le (Or.inl (gFace_evneg ha2))
  · -- a' → b  (T2 | H)
    refine edge4 E U FT2 FH _ _ _ 3 ⟨s * b1, s * b2, m3⟩ ⟨r1, r2, 0⟩ ?_ h.T2_W h.T2_B h.H_W h.H_B
      h.H_M h.T2_M h.T2_R h.H_R (hT2.mono fun _ h => h.le) hH ?_ ?_ ?_ ?_
    · exact (ne_of_ev (F := FT3) h.T3_W h.T3_B)
    · exact yok_mk h.T2_M.le h.H_M.le (Or.inl h.T2_M)
    · exact yok_mk h.T2_C.le h.H_C.le (Or.inl h.T2_C)
    · exact yok_mk h.T2_R.le h.H_R.le (Or.inr ⟨h.H_R, hT2⟩)
    · exact yok_mk h.T2_A.le h.H_A.le (Or.inl h.T2_A)

theorem depth2_pos (hb1 : 0 < b1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (dep (rim2 zv zw s b1 b2 m3) δ) := by
  have hs0 := h.hs0; have hs1 := h.hs1
  have hzvw := h.hzw
  have hsb : 0 < s * b1 := mul_pos hs0 hb1
  have e1 := eventually_pos_affine (A := (1 - s) * b1) (B := m3) (Or.inl (mul_pos (by linarith) hb1))
  have e2 := eventually_pos_affine (A := s * b1) (B := zw - m3) (Or.inl hsb)
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  filter_upwards [e1, e2, e4] with δ h1 h2 h4
  refine uni4_down ?_ ?_ ?_
  · show s * b1 - δ * m3 < b1 - δ * 0; nlinarith
  · show 0 - δ * zw < s * b1 - δ * m3; linarith
  · show 0 - δ * zv < 0 - δ * zw; nlinarith

theorem depth2_neg (hb1 : b1 < 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (dep (rim2 zv zw s b1 b2 m3) δ) := by
  have hs0 := h.hs0; have hs1 := h.hs1
  have hzvw := h.hzw
  have hsb : s * b1 < 0 := mul_neg_of_pos_of_neg hs0 hb1
  have e1 := eventually_pos_affine (A := (1 - s) * (-b1)) (B := -m3)
    (Or.inl (mul_pos (by linarith) (by linarith)))
  have e2 := eventually_pos_affine (A := -(s * b1)) (B := m3 - zv) (Or.inl (by linarith))
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  filter_upwards [e1, e2, e4] with δ h1 h2 h4
  refine uni4_up ?_ ?_ ?_
  · show b1 - δ * 0 < s * b1 - δ * m3; nlinarith
  · show s * b1 - δ * m3 < 0 - δ * zv; linarith
  · show 0 - δ * zv < 0 - δ * zw; nlinarith

end N2Cfg

end Minimality
end
