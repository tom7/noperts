module

public import Minimality.HEndT4
public import Minimality.HFrame
public import Minimality.HEndFinal
public import Minimality.UniformTilt
public import Minimality.Type08Slide
public import Minimality.Type08T4
public import Minimality.Type08Sector

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

section T4

variable {a a' b b' c c' d : ℝ³}

/-- The frame of case T4: the edge `d b` (`u₀ = b − d`), the face `G = Q_bc = d b a' c` with far
corner `g = c`. -/
theorem t4_frame (F : OctFacets a a' b b' c c') (hd : IsCap F d) :
    HFrame b c (b - d) F.a'bc.N F.a'bc.f := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set G := F.a'bc with hG
  have hNu : ⟪G.N, b - d⟫ = 0 := by rw [← G.hN, G.hQ, hd.a'bc]; ring
  refine ⟨?_, G.hN, G.hQ, G.hR, hNu, ?_, ?_⟩
  · have : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
    exact real_inner_self_pos.mpr this
  · have hn : G.N ≠ 0 := by
      intro h0
      have := G.hN a b
      rw [h0, inner_zero_left, G.hQ] at this
      have h2 := G.neg a (by simp) haa' hab hac
      linarith
    exact real_inner_self_pos.mpr hn
  · have hne : hfE b c (b - d) ≠ 0 := by
      intro h0
      have h1 : c - b = hfTau b c (b - d) • (b - d) := by
        have : hfE b c (b - d) = (c - b) - hfTau b c (b - d) • (b - d) := rfl
        rw [h0] at this; exact (sub_eq_zero.mp this.symm)
      set H := F.abc' with hH
      have hdH : H.f d = 0 := hd.abc'
      have e1 : H.f c - H.f b = ⟪H.N, c - b⟫ := H.hN c b
      have e2 : H.f b - H.f d = ⟪H.N, b - d⟫ := H.hN b d
      rw [h1, real_inner_smul_right, ← e2, H.hQ, hdH] at e1
      have h2 := H.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
      linarith
    exact real_inner_self_pos.mpr hne


/-- In the T4 case `b'` is a corner of the view along `d b` (Lemma G: `b'` never lies on
the side `[P c', P c]`): `κ' = α + α₁ (β − 1) > 0`, since `c'` lies beneath the face
`a'b'c` of `O` and `β₂ < 1`. -/
theorem t4_kappa_pos {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hα : 0 < α) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂) (hβ₂1 : β₂ ≤ 1) : 0 < α + α₁ * (β - 1) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set f := F.a'b'c.f
  have fb' := affine_frame F.a'b'c.hN d a c α β
  have fa' := affine_frame F.a'b'c.hN d b c α₂ β₂
  have fc' := affine_frame F.a'b'c.hN d a b α₁ β₁
  rw [← hb', F.a'b'c.hQ, F.a'b'c.hR] at fb'
  rw [← ha', F.a'b'c.hP, F.a'b'c.hR] at fa'
  rw [← hc'] at fc'
  have hc'n := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  have hdn := hd.a'b'c
  set D := F.a'b'c.f d
  set X := F.a'b'c.f a - D
  set Y := F.a'b'c.f b - D
  have h1 : α * X = (β - 1) * D := by linarith
  have h2 : α₂ * Y = (β₂ - 1) * D := by linarith
  have h3 : D + α₁ * X + β₁ * Y < 0 := by linarith
  have h4 : α * α₂ * (D + α₁ * X + β₁ * Y) < 0 := mul_neg_of_pos_of_neg (mul_pos hα hα₂) h3
  have h5 : α * α₂ * (D + α₁ * X + β₁ * Y) =
      D * (α * α₂ + α₁ * α₂ * (β - 1) + α * β₁ * (β₂ - 1)) := by
    linear_combination (α₁ * α₂) * h1 + (α * β₁) * h2
  have h6 : 0 < α * α₂ + α₁ * α₂ * (β - 1) + α * β₁ * (β₂ - 1) :=
    pos_of_mul_neg_right (h5 ▸ h4) hdn.le
  have h7 : 0 ≤ α * β₁ * (1 - β₂) := mul_nonneg (mul_pos hα hβ₁).le (by linarith)
  have h8 : 0 < α₂ * (α + α₁ * (β - 1)) := by nlinarith
  exact pos_of_mul_pos_right h8 hα₂.le

/-- **General position at the far triple tie, T4** (Propositions 29.3 and 30.4).  Put
`u₀ = b − d`, `e` the horizontal direction of `c − b`, `G = Q_bc`.  (E): `c'` is not over the line
through `b` normal to `e` (`b₁ ≠ 0`), `b'` and `c'` are at different distances from the plane of
`G` and `z a' ≠ z b`; the vertex `a'` does not tie in depth with `a` along the whole circle; if
`b'` is farther than `c'` from the plane of `G`, its abscissa `r₁` along `e` is not `max (A, b₁)`
(`A` the abscissa of `c`); and, when moreover `b'` has the largest abscissa among the far corners
(`A < r₁`, `b₁ < r₁`: "`r` beyond", the horizontal end of the face circle), (no persistent HDN) the
rim of the horizontal end has no horizontal double normal at arbitrarily small tilts.  Without
"`r` beyond" the sector tilt at `u₀` (Proposition 29.3) closes `K` with no further condition. -/
def Touch30T4 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (F : OctFacets a a' b b' c c') (_ : IsCap F d),
    ⟪c' - b, hfE b c (b - d)⟫ ≠ 0 ∧ F.a'bc.f b' ≠ F.a'bc.f c' ∧ ⟪a' - b, b - d⟫ ≠ 0 ∧
    ¬ (⟪a' - a, hfE b c (b - d)⟫ = 0 ∧ ⟪a' - a, b - d⟫ = 0) ∧
    (F.a'bc.f b' < F.a'bc.f c' →
      ⟪b' - b, hfE b c (b - d)⟫ ≠ max ⟪c - b, hfE b c (b - d)⟫ ⟪c' - b, hfE b c (b - d)⟫) ∧
    (F.a'bc.f b' < F.a'bc.f c' → ⟪c - b, hfE b c (b - d)⟫ < ⟪b' - b, hfE b c (b - d)⟫ →
      ⟪c' - b, hfE b c (b - d)⟫ < ⟪b' - b, hfE b c (b - d)⟫ → ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      NoHDNAt ({b', a', d, a} : Finset ℝ³) (hfE b c (b - d) - δ • (b - d))) ∧
    (F.a'bc.f c' < F.a'bc.f b' → 0 < ⟪a' - b, b - d⟫ → ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      NoHDNAt ({c', a', d, a} : Finset ℝ³) (hfE b c (b - d) - δ • (b - d))) ∧
    (F.a'bc.f c' < F.a'bc.f b' → ⟪a' - b, b - d⟫ < 0 → ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      NoHDNAt ({c', b, d, a} : Finset ℝ³) (hfE b c (b - d) - δ • (b - d)))

set_option maxHeartbeats 2000000 in
/-- **Proposition 30.4, case T4.**  At the far triple tie of the named closing T4
(`z c = z b' = z c'` along `u₀ = b − d`, `z b > z c`), the horizontal end of the face circle of
`Q_bc` closes `K`, under the general position `Touch30T4`. -/
theorem isRupert_touchT4 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfc : F.abc'.f c < F.abc'.f a') (hfc' : F.a'bc.f c' < F.a'bc.f a)
    (hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (T : Touch30T4 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨Tb1, Tr2, Tz, Tnt, Tmax, Thd1, Thd2, Thd3⟩ := T F hd
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  -- the coordinates of the cap in the frame `d; a, c, b`
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
  have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
  have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
  have hEf := hd.det_Qac_ne
  generalize F.a'bc.f c' / F.a'bc.f a = α₁ at *
  generalize F.ab'c.f c' / F.ab'c.f b = β₁ at *
  generalize F.ab'c.f a' / F.ab'c.f b = α₂ at *
  generalize F.abc'.f a' / F.abc'.f c = β₂ at *
  generalize F.a'bc.f b' / F.a'bc.f a = α at *
  generalize F.abc'.f b' / F.abc'.f c = β at *
  have Fr := t4_frame F hd
  set u0 : ℝ³ := b - d with hu0
  set e : ℝ³ := hfE b c u0 with he
  set fG : ℝ³ → ℝ := F.a'bc.f with hfG
  set N : ℝ³ := F.a'bc.N with hN
  -- the real coordinates
  set E : ℝ := ⟪e, e⟫ with hE
  set U : ℝ := ⟪u0, u0⟫ with hU
  set zv : ℝ := ⟪b - c, u0⟫ with hzv
  set zw : ℝ := ⟪d - c, u0⟫ with hzw
  set A : ℝ := ⟪c - b, e⟫ with hA
  set b1 : ℝ := ⟪c' - b, e⟫ with hb1
  set b2 : ℝ := -fG c' with hb2
  set r1 : ℝ := ⟪b' - b, e⟫ with hr1
  set r2 : ℝ := -fG b' with hr2
  set xa : ℝ := ⟪a' - b, e⟫ with hxa
  set za : ℝ := ⟪a' - c, u0⟫ with hza
  set a3 : ℝ := ⟪a - c, u0⟫ with ha3
  have heu : ⟪e, u0⟫ = 0 := Fr.inner_e_u
  have heu' : ⟪u0, e⟫ = 0 := by rw [real_inner_comm]; exact heu
  have hNe : ⟪N, e⟫ = 0 := Fr.inner_N_e
  have hNu : ⟪N, u0⟫ = 0 := Fr.hNu
  have hfGa' : fG a' = 0 := F.a'bc.hP
  have hfGb : fG b = 0 := F.a'bc.hQ
  have hfGc : fG c = 0 := F.a'bc.hR
  have hfGd : fG d = 0 := hd.a'bc
  have hZc' : ⟪c' - c, u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hZb' : ⟪b' - c, u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hbpc : c - b = e + hfTau b c u0 • u0 := by simp [he, hfE]
  have hAE : A = E := by
    rw [hA, hbpc, inner_add_left, real_inner_smul_left, heu', hE]; ring
  have hΦb : hfΦ b c u0 fG b = ⟨0, 0, zv⟩ := by
    show (⟨⟪b - b, e⟫, -fG b, ⟪b - c, u0⟫⟩ : V3) = ⟨0, 0, zv⟩
    rw [hfGb, sub_self, inner_zero_left]; simp [hzv]
  have hΦd : hfΦ b c u0 fG d = ⟨0, 0, zw⟩ := by
    show (⟨⟪d - b, e⟫, -fG d, ⟪d - c, u0⟫⟩ : V3) = ⟨0, 0, zw⟩
    have : d - b = -u0 := by rw [hu0]; abel
    rw [hfGd, this, inner_neg_left, heu']; simp [hzw]
  have hΦc : hfΦ b c u0 fG c = ⟨A, 0, 0⟩ := by
    show (⟨⟪c - b, e⟫, -fG c, ⟪c - c, u0⟫⟩ : V3) = ⟨A, 0, 0⟩
    rw [hfGc, sub_self, inner_zero_left]; simp [hA]
  have hΦc' : hfΦ b c u0 fG c' = ⟨b1, b2, 0⟩ := by
    show (⟨⟪c' - b, e⟫, -fG c', ⟪c' - c, u0⟫⟩ : V3) = ⟨b1, b2, 0⟩
    rw [hZc']
  have hΦb' : hfΦ b c u0 fG b' = ⟨r1, r2, 0⟩ := by
    show (⟨⟪b' - b, e⟫, -fG b', ⟪b' - c, u0⟫⟩ : V3) = ⟨r1, r2, 0⟩
    rw [hZb']
  have hΦa' : hfΦ b c u0 fG a' = ⟨xa, 0, za⟩ := by
    show (⟨⟪a' - b, e⟫, -fG a', ⟪a' - c, u0⟫⟩ : V3) = ⟨xa, 0, za⟩
    rw [hfGa']; simp [hxa, hza]
  -- the representation of `a` and `a'`
  have hα₁pos : 0 < α₁ := by linarith
  have hXa : ⟪a - b, e⟫ = b1 / α₁ := by
    have h1 : α₁ • (a - d) = (c' - d) - β₁ • u0 := by
      have := hc'; rw [hu0]; rw [eq_sub_iff_add_eq]; rw [hc']; module
    have h2 : a - b = α₁⁻¹ • ((c' - d) - β₁ • u0) - u0 := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hα₁pos.ne', one_smul, hu0]; abel
    rw [h2, inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left, heu',
      show c' - d = (c' - b) + u0 by rw [hu0]; abel, inner_add_left, heu', hb1]
    field_simp
    ring
  have hYa : fG a = fG c' / α₁ := by
    have h1 : α₁ • (a - d) = (c' - d) - β₁ • u0 := by
      have := hc'; rw [hu0]; rw [eq_sub_iff_add_eq]; rw [hc']; module
    have h2 : a - d = α₁⁻¹ • ((c' - d) - β₁ • u0) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hα₁pos.ne', one_smul]
    have h3 : fG a - fG d = ⟪N, a - d⟫ := F.a'bc.hN a d
    have h4 : fG c' - fG d = ⟪N, c' - d⟫ := F.a'bc.hN c' d
    rw [h2, real_inner_smul_right, inner_sub_right, real_inner_smul_right, hNu, ← h4, hfGd] at h3
    rw [div_eq_inv_mul]
    linarith
  have hXa' : xa = β₂ * A := by
    have h1 : a' - b = (α₂ - 1 + β₂) • u0 + β₂ • (c - b) := by
      rw [ha', hu0]; module
    rw [hxa, h1, inner_add_left, real_inner_smul_left, real_inner_smul_left, heu', hA]; ring
  have hZa' : za = (1 - β₂) * zw + α₂ * U := by
    have h1 : a' - c = (1 - β₂) • (d - c) + α₂ • u0 := by
      rw [ha', hu0]; module
    rw [hza, h1, inner_add_left, real_inner_smul_left, real_inner_smul_left, hzw, hU]
  have hΦa : hfΦ b c u0 fG a = ⟨α₁⁻¹ * b1, α₁⁻¹ * b2, a3⟩ := by
    show (⟨⟪a - b, e⟫, -fG a, ⟪a - c, u0⟫⟩ : V3) = ⟨α₁⁻¹ * b1, α₁⁻¹ * b2, a3⟩
    rw [hXa, hYa]
    simp only [V3.mk.injEq, hb2]
    refine ⟨by ring, by ring, rfl⟩
  -- positivity
  have hUpos : 0 < U := Fr.hu
  have hEpos : 0 < E := Fr.hee
  have hApos : 0 < A := by rw [hAE]; exact hEpos
  have hzvw : zv - zw = U := by
    rw [hzv, hzw, ← inner_sub_left]
    have : (b - c) - (d - c) = u0 := by rw [hu0]; abel
    rw [this]
  have hzvpos : 0 < zv := by
    have h1 : ⟪b, u0⟫ - ⟪c, u0⟫ = zv := by rw [hzv, inner_sub_left]
    have hl : ⟪b', u0⟫ = ⟪c, u0⟫ := htouch.1.symm
    have hl' : ⟪c', u0⟫ = ⟪c, u0⟫ := by rw [htouch.2]; exact hl
    rw [hl, hl', min_self, max_le_iff] at hgood
    have h2 : ⟪c, u0⟫ < ⟪b, u0⟫ := by
      by_contra hc; push Not at hc; exact hgood ⟨hc, le_refl _⟩
    linarith
  have hb2pos : 0 < b2 := by
    rw [hb2]; have := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'); linarith
  have hr2pos : 0 < r2 := by
    rw [hr2]; have := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c; linarith
  -- the shadow convexity at `c`
  have hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0 := by
    obtain ⟨-, d2, -, -, -, d6, -⟩ := t4_slide_dets hb' hc' ha'
    have hEf2 : 0 < det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d) :=
      mul_self_pos.mpr hEf
    have hprod : 0 < det3 (c - b') (c' - b') (b - d) * det3 (c' - b) (c - b) (b - d) := by
      rw [d6, d2]
      have : (α + β * α₁ - α₁) * det3 (a - d) (c - d) (b - d) * (α₁ * det3 (a - d) (c - d) (b - d)) =
          ((α + α₁ * (β - 1)) * α₁) * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) := by
        ring
      rw [this]; exact mul_pos (mul_pos hκ hα₁pos) hEf2
    have h2 := Fr.shadow_sign b' c c' b c' c hprod
    rw [hΦb', hΦc, hΦc', hΦb] at h2
    have e1 : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨b1, b2, 0⟩ =
        (A - r1) * (b2 - r2) + r2 * (b1 - r1) := by simp only [crossXY]; ring
    have e2 : crossXY ⟨0, 0, zv⟩ ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ = -(b2 * A) := by
      simp only [crossXY]; ring
    rw [e1, e2] at h2
    exact neg_of_mul_pos_left h2 (neg_nonpos.mpr (mul_pos hb2pos hApos).le)
  -- the facets
  have evq0 : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ b c u0 fG p = q → f p = 0 → (hfFc b c u0 N f Nf).ev q = 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf, h0]
  have evql : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ b c u0 fG p = q → f p < 0 → (hfFc b c u0 N f Nf).ev q < 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf]; exact h0
  have hzwneg : zw < 0 := by
    refine zw_neg_of (hfFc b c u0 N F.ab'c.f F.ab'c.N) hApos hr2pos hDr (by linarith)
      (evq0 _ _ F.ab'c.hN c _ hΦc F.ab'c.hR) (evq0 _ _ F.ab'c.hN b' _ hΦb' F.ab'c.hQ)
      (evq0 _ _ F.ab'c.hN d _ hΦd hd.ab'c) (evql _ _ F.ab'c.hN b _ hΦb
        (F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc))
      (evql _ _ F.ab'c.hN c' _ hΦc' (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c')
        (Ne.symm hcc')))
  have hxapos : 0 < xa := by rw [hXa']; exact mul_pos hβ₂ hApos
  have hxaA : xa < A := by rw [hXa']; exact mul_lt_of_lt_one_left hApos hβ₂1
  have hzaw : zw < za := by
    have h1 := mul_pos hβ₂ (neg_pos.mpr hzwneg)
    have h2 := mul_pos hα₂ hUpos
    rw [hZa']; linarith
  have hua0 : 0 < α₁⁻¹ := inv_pos.mpr hα₁pos
  have hua1 : α₁⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα₁1
  have cfg : T4Cfg E U zv zw A b1 b2 r1 r2 xa za α₁⁻¹ a3
      (hfFc b c u0 N F.abc'.f F.abc'.N) (hfFc b c u0 N F.ab'c.f F.ab'c.N)
      (hfFc b c u0 N F.ab'c'.f F.ab'c'.N) (hfFc b c u0 N F.a'bc'.f F.a'bc'.N)
      (hfFc b c u0 N F.a'b'c'.f F.a'b'c'.N) (hfFc b c u0 N F.a'b'c.f F.a'b'c.N) := by
    refine ⟨hEpos, hUpos, hzvpos, by linarith, hApos, hb2pos, hr2pos, hxapos, hxaA, hzaw, hua0, hua1,
      hDr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- H = Q_ab = abc'
    · exact evq0 _ _ F.abc'.hN d _ hΦd hd.abc'
    · exact evq0 _ _ F.abc'.hN a _ hΦa F.abc'.hP
    · exact evq0 _ _ F.abc'.hN c' _ hΦc' F.abc'.hR
    · exact evq0 _ _ F.abc'.hN b _ hΦb F.abc'.hQ
    · exact evql _ _ F.abc'.hN a' _ hΦa' (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c')
    · exact evql _ _ F.abc'.hN b' _ hΦb' (F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c')
    · exact evql _ _ F.abc'.hN c _ hΦc (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
    -- Q_ac = ab'c
    · exact evq0 _ _ F.ab'c.hN d _ hΦd hd.ab'c
    · exact evq0 _ _ F.ab'c.hN a _ hΦa F.ab'c.hP
    · exact evq0 _ _ F.ab'c.hN b' _ hΦb' F.ab'c.hQ
    · exact evq0 _ _ F.ab'c.hN c _ hΦc F.ab'c.hR
    · exact evql _ _ F.ab'c.hN a' _ hΦa' (F.ab'c.neg a' (by simp) (Ne.symm haa') ha'b' ha'c)
    · exact evql _ _ F.ab'c.hN b _ hΦb (F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc)
    · exact evql _ _ F.ab'c.hN c' _ hΦc' (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
    -- T1 = ab'c'
    · exact evq0 _ _ F.ab'c'.hN a _ hΦa F.ab'c'.hP
    · exact evq0 _ _ F.ab'c'.hN c' _ hΦc' F.ab'c'.hR
    · exact evq0 _ _ F.ab'c'.hN b' _ hΦb' F.ab'c'.hQ
    · exact evql _ _ F.ab'c'.hN a' _ hΦa' (F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c')
    · exact evql _ _ F.ab'c'.hN b _ hΦb (F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc')
    · exact evql _ _ F.ab'c'.hN c _ hΦc (F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc')
    · exact evql _ _ F.ab'c'.hN d _ hΦd hd.ab'c'
    -- T2 = a'bc'
    · exact evq0 _ _ F.a'bc'.hN c' _ hΦc' F.a'bc'.hR
    · exact evq0 _ _ F.a'bc'.hN b _ hΦb F.a'bc'.hQ
    · exact evq0 _ _ F.a'bc'.hN a' _ hΦa' F.a'bc'.hP
    · exact evql _ _ F.a'bc'.hN a _ hΦa (F.a'bc'.neg a (by simp) haa' hab hac')
    · exact evql _ _ F.a'bc'.hN b' _ hΦb' (F.a'bc'.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c')
    · exact evql _ _ F.a'bc'.hN c _ hΦc (F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc')
    · exact evql _ _ F.a'bc'.hN d _ hΦd hd.a'bc'
    -- T3 = a'b'c'
    · exact evq0 _ _ F.a'b'c'.hN c' _ hΦc' F.a'b'c'.hR
    · exact evq0 _ _ F.a'b'c'.hN b' _ hΦb' F.a'b'c'.hQ
    · exact evq0 _ _ F.a'b'c'.hN a' _ hΦa' F.a'b'c'.hP
    · exact evql _ _ F.a'b'c'.hN a _ hΦa (F.a'b'c'.neg a (by simp) haa' hab' hac')
    · exact evql _ _ F.a'b'c'.hN b _ hΦb (F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc')
    · exact evql _ _ F.a'b'c'.hN c _ hΦc (F.a'b'c'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hb'c) hcc')
    · exact evql _ _ F.a'b'c'.hN d _ hΦd hd.a'b'c'
    -- T4 = a'b'c
    · exact evq0 _ _ F.a'b'c.hN b' _ hΦb' F.a'b'c.hQ
    · exact evq0 _ _ F.a'b'c.hN c _ hΦc F.a'b'c.hR
    · exact evq0 _ _ F.a'b'c.hN a' _ hΦa' F.a'b'c.hP
    · exact evql _ _ F.a'b'c.hN a _ hΦa (F.a'b'c.neg a (by simp) haa' hab' hac)
    · exact evql _ _ F.a'b'c.hN b _ hΦb (F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc)
    · exact evql _ _ F.a'b'c.hN c' _ hΦc' (F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'))
    · exact evql _ _ F.a'b'c.hN d _ hΦd hd.a'b'c
  -- the middles over the chords of `G`
  have rat : ∀ num den : ℝ, den < 0 → den < num → num < 0 → 0 < num / den ∧ num / den < 1 :=
    fun num den h1 h2 h3 => ⟨div_pos_of_neg_of_neg h3 h1, (div_lt_one_of_neg h1).mpr h2⟩
  have hmid12 : zv < za → (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
        b = a' + s • (d - a') + δ' • (e - δ • u0)) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
        c = a' + s • (d - a') + δ' • (e - δ • u0)) := by
    intro hz
    have hP : fG a' = 0 := hfGa'
    refine ⟨Fr.mid_ev hP hfGd hfGb ?_ ?_ ?_ ?_, Fr.mid_ev hP hfGd hfGc ?_ ?_ ?_ ?_⟩
    all_goals simp only [hΦa', hΦd, hΦb, hΦc]
    · intro h; linarith
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).1
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).2
    · have hr := (rat (zv - za) (zw - za) (by linarith) (by linarith) (by linarith)).2
      intro h0
      have : xa * (1 - (zv - za) / (zw - za)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hxapos.ne' h
      · linarith
    · intro h; linarith
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).1
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).2
    · have hr := (rat (0 - za) (zw - za) (by linarith) (by linarith) (by linarith)).2
      have hr0 := (rat (0 - za) (zw - za) (by linarith) (by linarith) (by linarith)).1
      have hh := mul_pos hxapos hr0
      intro h0
      linarith
  have hmid3 : za < zv → (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
        a' = b + s • (d - b) + δ' • (e - δ • u0)) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
        c = b + s • (d - b) + δ' • (e - δ • u0)) := by
    intro hz
    refine ⟨Fr.mid_ev hfGb hfGd hfGa' ?_ ?_ ?_ ?_, Fr.mid_ev hfGb hfGd hfGc ?_ ?_ ?_ ?_⟩
    all_goals simp only [hΦa', hΦd, hΦb, hΦc]
    · intro h; linarith
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).1
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).2
    · intro h0; simp at h0; exact hxapos.ne' h0
    · intro h; linarith
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).1
    · exact (rat _ _ (by linarith) (by linarith) (by linarith)).2
    · intro h0; simp at h0; exact hApos.ne' h0
  have hnt : ¬ (xa = α₁⁻¹ * b1 ∧ za = a3) := by
    rintro ⟨h1, h2⟩
    apply Tnt
    constructor
    · rw [show a' - a = (a' - b) - (a - b) by abel, inner_sub_left, hXa, ← hxa, h1, div_eq_inv_mul]
      ring
    · rw [show a' - a = (a' - c) - (a - c) by abel, inner_sub_left, ← hza, ← ha3, h2]; ring
  have hzaz : ⟪a' - b, u0⟫ = za - zv := by
    rw [show a' - b = (a' - c) - (b - c) by abel, inner_sub_left]
  have hrimA : ∀ i, rimA zw r1 r2 xa za α₁⁻¹ b1 b2 a3 i = hfΦ b c u0 fG (quad b' a' d a i) := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hΦb'.symm, hΦa'.symm, hΦd.symm, hΦa.symm]
  have hrimB : ∀ i, rimB zw b1 b2 xa za α₁⁻¹ a3 i = hfΦ b c u0 fG (quad c' a' d a i) := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hΦc'.symm, hΦa'.symm, hΦd.symm, hΦa.symm]
  have hrimC : ∀ i, rimC zv zw b1 b2 α₁⁻¹ a3 i = hfΦ b c u0 fG (quad c' b d a i) := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hΦc'.symm, hΦb.symm, hΦd.symm, hΦa.symm]
  rcases lt_or_gt_of_ne Tr2 with hlt | hgt
  · -- case (i): `b'` is farther than `c'` from the plane of `G`
    have hr : b2 < r2 := by rw [hb2, hr2]; linarith
    have hzz : zv < za := (cfg.T2_a_neg_iff).mp (cfg.T2_a_neg_of hr)
    by_cases hnb : ¬ (A < r1 ∧ b1 < r1)
    · -- `r` not beyond: the sector tilt at `u₀` (Proposition 29.3)
      have hr1 : r1 < A ∨ r1 < b1 := by
        have hne := Tmax hlt
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2⟩ := hcon
        apply hne
        refine le_antisymm ?_ (max_le h1 h2)
        by_contra hlt'
        push Not at hlt'
        exact hnb ⟨lt_of_le_of_lt (le_max_left _ _) hlt', lt_of_le_of_lt (le_max_right _ _) hlt'⟩
      have hq3 : 0 < r1 * b2 - b1 * r2 := by
        obtain ⟨-, d2, -, d4, -⟩ := t4_slide_dets hb' hc' ha'
        have hEf2 : 0 < det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d) :=
          mul_self_pos.mpr hEf
        have hprod : 0 < det3 (b' - c') (b - c') (b - d) * det3 (c' - b) (c - b) (b - d) := by
          rw [d4, d2]
          have : (β * α₁) * det3 (a - d) (c - d) (b - d) * (α₁ * det3 (a - d) (c - d) (b - d)) =
              (β * α₁ * α₁) * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) := by
            ring
          rw [this]; exact mul_pos (mul_pos (mul_pos hβ hα₁pos) hα₁pos) hEf2
        have h2 := Fr.shadow_sign c' b' b b c' c hprod
        rw [hΦc', hΦb', hΦb, hΦc] at h2
        have e : crossXY ⟨b1, b2, 0⟩ ⟨r1, r2, 0⟩ ⟨0, 0, zv⟩ * crossXY ⟨0, 0, zv⟩ ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ =
            (r1 * b2 - b1 * r2) * (b2 * A) := by simp only [crossXY]; ring
        rw [e] at h2
        exact pos_of_mul_pos_left h2 (mul_pos hb2pos hApos).le
      have hk : a3 < (1 - α₁⁻¹) * zv := by
        have h1 : ⟪c' - c, u0⟫ = zw + α₁ * (a3 - zw) + β₁ * U := by
          have : c' - c = (d - c) + α₁ • ((a - c) - (d - c)) + β₁ • u0 := by
            rw [hc', hu0]; module
          rw [this]
          simp only [hzw, ha3, hU, inner_add_left, real_inner_smul_left, inner_sub_left]
        have h2 : zw + α₁ * (a3 - zw) + β₁ * U = 0 := by rw [← h1]; exact hZc'
        have h3 : α₁ * a3 < (α₁ - 1) * zv := by nlinarith [mul_pos hβ₁ hUpos]
        rw [show (1 - α₁⁻¹) * zv = ((α₁ - 1) * zv) / α₁ by field_simp, lt_div_iff₀ hα₁pos]
        linarith
      have hm' : (1 - β₂) * zv < za := by
        rw [hZa']
        nlinarith [mul_pos (sub_pos.2 (show 1 - β₂ < α₂ by linarith)) hUpos]
      exact HFrame.sector5_t4 Fr (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        (cP := b) (mP := a') (fP := c) (rP := b') (gP := c') (wP := d) (aP := a)
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h | h | h | h | h | h
          exacts [Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))), Or.inr (Or.inl h), Or.inl h,
            Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inl h)),
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))])
        (by simp) (by simp) (by simp) (by simp) (by simp)
        hΦb hΦa' hΦc hΦb' hΦc' hΦd hΦa hβ₂ hβ₂1 hXa' hzvpos hm' (by linarith) hAE hApos hb2pos
        hr2pos hDr hq3 hua0 hua1 hk hr1
    obtain ⟨hA1, hb1'⟩ := not_not.mp hnb
    obtain ⟨σ, hσ⟩ := cfg.testsA hr
    have hdep := cfg.depthA hA1 hb1' Tb1 hnt
    obtain ⟨hmb, hmc⟩ := hmid12 hzz
    refine HFrame.rim_final Fr (by norm_num : 3 ≤ 4) _ {b, c} {b', a', d, a} (quad b' a' d a) ?_ ?_ ?_ σ ?_
      (Thd1 hlt hA1 hb1')
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad] <;> refine ⟨?_, ?_⟩ <;> intro h <;> subst h <;> tauto
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
    · filter_upwards [hσ, hdep, hmb, hmc] with δ h1 h2 h3 h4
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i j hi hj
        simpa only [hrimA] using h1.1 i j hi hj
      · intro y hy hyM hyx i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl (hyx 2)
        · exact absurd rfl (hyx 3)
        · exact absurd rfl (hyx 1)
        · exact absurd (Or.inl rfl) hyM
        · exact absurd rfl (hyx 0)
        · exact absurd (Or.inr rfl) hyM
        · simpa only [hrimA, hΦc'] using h1.2.1 i
      · have : dep (rimA zw r1 r2 xa za α₁⁻¹ b1 b2 a3) δ =
            dep (fun i => hfΦ b c u0 fG (quad b' a' d a i)) δ := by
          funext i; simp only [dep, hrimA]
        rw [← this]; exact h2
      · intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h3
          exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩
        · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h4
          exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩
  · have hr : r2 < b2 := by rw [hb2, hr2]; linarith
    rcases lt_or_gt_of_ne Tz with hneg | hpos
    · -- case (iii): `a'` is below `b`
      have hz' : za < zv := by linarith
      obtain ⟨σ, hσ⟩ := cfg.testsC hr hz'
      have hdep := cfg.depthC Tb1
      obtain ⟨hma, hmc⟩ := hmid3 hz'
      refine HFrame.rim_final Fr (by norm_num : 3 ≤ 4) _ {a', c} {c', b, d, a} (quad c' b d a) ?_ ?_ ?_ σ ?_
        (Thd3 hgt hneg)
      · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad] <;> refine ⟨?_, ?_⟩ <;> intro h <;> subst h <;> tauto
      · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
      · filter_upwards [hσ, hdep, hma, hmc] with δ h1 h2 h3 h4
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i j hi hj
          simpa only [hrimC] using h1.1 i j hi hj
        · intro y hy hyM hyx i
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl (hyx 2)
          · exact absurd rfl (hyx 3)
          · exact absurd (Or.inl rfl) hyM
          · exact absurd rfl (hyx 1)
          · simpa only [hrimC, hΦb'] using h1.2.1 i
          · exact absurd (Or.inr rfl) hyM
          · exact absurd rfl (hyx 0)
        · have : dep (rimC zv zw b1 b2 α₁⁻¹ a3) δ =
              dep (fun i => hfΦ b c u0 fG (quad c' b d a i)) δ := by
            funext i; simp only [dep, hrimC]
          rw [← this]; exact h2
        · intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h3
            exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩
          · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h4
            exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩
    · -- case (ii): `a'` is above `b`
      have hz' : zv < za := by linarith
      obtain ⟨σ, hσ⟩ := cfg.testsB hr hz'
      have hdep := cfg.depthB hz' Tb1 hnt
      obtain ⟨hmb, hmc⟩ := hmid12 hz'
      refine HFrame.rim_final Fr (by norm_num : 3 ≤ 4) _ {b, c} {c', a', d, a} (quad c' a' d a) ?_ ?_ ?_ σ ?_
        (Thd2 hgt hpos)
      · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad] <;> refine ⟨?_, ?_⟩ <;> intro h <;> subst h <;> tauto
      · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
      · filter_upwards [hσ, hdep, hmb, hmc] with δ h1 h2 h3 h4
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i j hi hj
          simpa only [hrimB] using h1.1 i j hi hj
        · intro y hy hyM hyx i
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl (hyx 2)
          · exact absurd rfl (hyx 3)
          · exact absurd rfl (hyx 1)
          · exact absurd (Or.inl rfl) hyM
          · simpa only [hrimB, hΦb'] using h1.2.1 i
          · exact absurd (Or.inr rfl) hyM
          · exact absurd rfl (hyx 0)
        · have : dep (rimB zw b1 b2 xa za α₁⁻¹ a3) δ =
              dep (fun i => hfΦ b c u0 fG (quad c' a' d a i)) δ := by
            funext i; simp only [dep, hrimB]
          rw [← this]; exact h2
        · intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h3
            exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩
          · obtain ⟨s', δ', hs0, hs1, hδ, heq⟩ := h4
            exact ⟨1, s', δ', hs0, hs1, hδ, heq⟩

end T4

end Minimality
end
