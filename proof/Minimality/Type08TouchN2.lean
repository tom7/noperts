module

public import Minimality.HEndN2
public import Minimality.HFrame
public import Minimality.HEndFinal
public import Minimality.UniformTilt
public import Minimality.Type08Slide

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

section N2

variable {a a' b b' c c' d : ℝ³}

/-- The frame of case N2: the edge `c a'` ( `u₀ = c − a'`), the face `G = a'b'c` with its far corner
`g = b'`. -/
theorem n2_frame (F : OctFacets a a' b b' c c') :
    HFrame c b' (c - a') F.a'b'c.N F.a'b'c.f := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set G := F.a'b'c with hG
  have hNu : ⟪G.N, c - a'⟫ = 0 := by rw [← G.hN, G.hR, G.hP]; ring
  refine ⟨?_, G.hN, G.hR, G.hQ, hNu, ?_, ?_⟩
  · have : c - a' ≠ 0 := sub_ne_zero.mpr (Ne.symm ha'c)
    exact real_inner_self_pos.mpr this
  · have hn : G.N ≠ 0 := by
      intro h0
      have := G.hN c' c
      rw [h0, inner_zero_left, G.hR] at this
      have h2 := G.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
      linarith
    exact real_inner_self_pos.mpr hn
  · have hne : hfE c b' (c - a') ≠ 0 := by
      intro h0
      have h1 : b' - c = hfTau c b' (c - a') • (c - a') := by
        have : hfE c b' (c - a') = (b' - c) - hfTau c b' (c - a') • (c - a') := rfl
        rw [h0] at this; exact (sub_eq_zero.mp this.symm)
      have H := F.a'bc
      have e1 : H.f b' - H.f c = ⟪H.N, b' - c⟫ := H.hN b' c
      have e2 : H.f c - H.f a' = ⟪H.N, c - a'⟫ := H.hN c a'
      rw [h1, real_inner_smul_right, ← e2, H.hR, H.hP] at e1
      have h2 := H.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c
      linarith
    exact real_inner_self_pos.mpr hne


/-- **General position at the far triple tie, N2** (`FEWER-FACES-PROOFS.md` Proposition 30.4;
codimension 3 inside the touching).  Put `u₀ = c − a'`, `e` the horizontal direction of `b' − c`,
`G = a'b'c`.  Then: (E) the point `b` is not over the line through `c` normal to `e`
(`b₁ ≠ 0`) and `c'`, `b` are at different distances from the plane of `G` (`r₂ ≠ b₂`);
(beyond) if `c'` is farther than `b` from the plane of `G` then `c'` has the largest abscissa along
`e` among the far corners; (distinct depths) if moreover `b₁ < 0` the vertex `a` does not tie in depth
with `d`, `c`, `a'` along the whole circle (`a − p` is not normal to `G`); (no persistent HDN)
the rim of the horizontal end has no horizontal double normal at arbitrarily small tilts. -/
def Touch30N2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (F : OctFacets a a' b b' c c') (_ : IsCap F d),
    ⟪b - c, hfE c b' (c - a')⟫ ≠ 0 ∧ F.a'b'c.f c' ≠ F.a'b'c.f b ∧
    (F.a'b'c.f c' < F.a'b'c.f b → ⟪b' - c, hfE c b' (c - a')⟫ < ⟪c' - c, hfE c b' (c - a')⟫ ∧
      ⟪b - c, hfE c b' (c - a')⟫ < ⟪c' - c, hfE c b' (c - a')⟫) ∧
    (F.a'b'c.f c' < F.a'b'c.f b → ⟪b - c, hfE c b' (c - a')⟫ < 0 →
      ¬ (⟪a - d, hfE c b' (c - a')⟫ = 0 ∧ ⟪a - d, c - a'⟫ = 0) ∧
      ¬ (⟪a - c, hfE c b' (c - a')⟫ = 0 ∧ ⟪a - c, c - a'⟫ = 0) ∧
      ¬ (⟪a - a', hfE c b' (c - a')⟫ = 0 ∧ ⟪a - a', c - a'⟫ = 0)) ∧
    (F.a'b'c.f c' < F.a'b'c.f b → ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      NoHDNAt ({c', a, d, c, a'} : Finset ℝ³) (hfE c b' (c - a') - δ • (c - a'))) ∧
    (F.a'b'c.f b < F.a'b'c.f c' → ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      NoHDNAt ({b, d, c, a'} : Finset ℝ³) (hfE c b' (c - a') - δ • (c - a')))


/-- **Proposition 30.4, case N2.**  At the far triple tie of the named closing N2 (`z b = z c' = z b'`
along `u₀ = c − a'`, `z c > z b'`), the horizontal end of the face circle of `a'b'c` closes `K`,
under the general position `Touch30N2`. -/
theorem isRupert_touchN2 (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfar : F.abc'.f a' < F.abc'.f c) (hq₂ : F.ab'c'.f a' < F.ab'c'.f c)
    (hgood : ¬ max ⟪c, c - a'⟫ ⟪c', c - a'⟫ ≤ min ⟪b, c - a'⟫ ⟪b', c - a'⟫)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (T : Touch30N2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨Tb1, Tr2, Tbey, Tnt, Thd1, Thd2⟩ := T F hd
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨s, δ0, hs0, hs1, hδ0, hdeq⟩ := hd.middle_Qbc hfar
  have Fr := n2_frame F
  -- the frame
  set u0 : ℝ³ := c - a' with hu0
  set e : ℝ³ := hfE c b' u0 with he
  set fG : ℝ³ → ℝ := F.a'b'c.f with hfG
  set N : ℝ³ := F.a'b'c.N with hN
  -- the real coordinates
  set E : ℝ := ⟪e, e⟫ with hE
  set U : ℝ := ⟪u0, u0⟫ with hU
  set zv : ℝ := ⟪c - b', u0⟫ with hzv
  set zw : ℝ := ⟪a' - b', u0⟫ with hzw
  set A : ℝ := ⟪b' - c, e⟫ with hA
  set b1 : ℝ := ⟪b - c, e⟫ with hb1
  set b2 : ℝ := -fG b with hb2
  set r1 : ℝ := ⟪c' - c, e⟫ with hr1
  set r2 : ℝ := -fG c' with hr2
  set a1 : ℝ := ⟪a - c, e⟫ with ha1
  set a2 : ℝ := -fG a with ha2
  set a3 : ℝ := ⟪a - b', u0⟫ with ha3
  set m3 : ℝ := ⟪d - b', u0⟫ with hm3
  have heu : ⟪e, u0⟫ = 0 := Fr.inner_e_u
  have heu' : ⟪u0, e⟫ = 0 := by rw [real_inner_comm]; exact heu
  have hNe : ⟪N, e⟫ = 0 := Fr.inner_N_e
  have hNu : ⟪N, u0⟫ = 0 := Fr.hNu
  have hfGa' : fG a' = 0 := F.a'b'c.hP
  have hfGb' : fG b' = 0 := F.a'b'c.hQ
  have hfGc : fG c = 0 := F.a'b'c.hR
  have hZb : ⟪b - b', u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hZc' : ⟪c' - b', u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hbpc : b' - c = e + hfTau c b' u0 • u0 := by simp [he, hfE]
  have hAE : A = E := by
    rw [hA, hbpc, inner_add_left, real_inner_smul_left, heu', hE]; ring
  have hΦc : hfΦ c b' u0 fG c = ⟨0, 0, zv⟩ := by
    show (⟨⟪c - c, e⟫, -fG c, ⟪c - b', u0⟫⟩ : V3) = ⟨0, 0, zv⟩
    rw [hfGc, sub_self, inner_zero_left]; simp [hzv]
  have hΦa' : hfΦ c b' u0 fG a' = ⟨0, 0, zw⟩ := by
    show (⟨⟪a' - c, e⟫, -fG a', ⟪a' - b', u0⟫⟩ : V3) = ⟨0, 0, zw⟩
    have : a' - c = -u0 := by rw [hu0]; abel
    rw [hfGa', this, inner_neg_left, heu']; simp [hzw]
  have hΦb' : hfΦ c b' u0 fG b' = ⟨A, 0, 0⟩ := by
    show (⟨⟪b' - c, e⟫, -fG b', ⟪b' - b', u0⟫⟩ : V3) = ⟨A, 0, 0⟩
    rw [hfGb', sub_self, inner_zero_left]; simp [hA]
  have hΦb : hfΦ c b' u0 fG b = ⟨b1, b2, 0⟩ := by
    show (⟨⟪b - c, e⟫, -fG b, ⟪b - b', u0⟫⟩ : V3) = ⟨b1, b2, 0⟩
    rw [hZb]
  have hΦc' : hfΦ c b' u0 fG c' = ⟨r1, r2, 0⟩ := by
    show (⟨⟪c' - c, e⟫, -fG c', ⟪c' - b', u0⟫⟩ : V3) = ⟨r1, r2, 0⟩
    rw [hZc']
  have hΦa : hfΦ c b' u0 fG a = ⟨a1, a2, a3⟩ := rfl
  have hdc : d - c = s • (b - c) + δ0 • u0 := by rw [hdeq, hu0]; abel
  have hΦd : hfΦ c b' u0 fG d = ⟨s * b1, s * b2, m3⟩ := by
    show (⟨⟪d - c, e⟫, -fG d, ⟪d - b', u0⟫⟩ : V3) = ⟨s * b1, s * b2, m3⟩
    have h1 : ⟪d - c, e⟫ = s * b1 := by
      rw [hdc, inner_add_left, real_inner_smul_left, real_inner_smul_left, heu', hb1]; ring
    have h2 : fG d = s * fG b := by
      have := F.a'b'c.hN d c
      have h3 := F.a'b'c.hN b c
      rw [hdc, inner_add_right, real_inner_smul_right, real_inner_smul_right, hNu] at this
      rw [← F.a'b'c.hN b c] at this
      have : fG d - fG c = s * (fG b - fG c) := by linarith
      rw [hfGc] at this; linarith
    rw [h1, h2]
    simp [hb2]; ring
  -- positivity
  have hUpos : 0 < U := Fr.hu
  have hEpos : 0 < E := Fr.hee
  have hzvw : zv - zw = U := by
    rw [hzv, hzw, ← inner_sub_left]
    have : (c - b') - (a' - b') = u0 := by rw [hu0]; abel
    rw [this]
  have hzvpos : 0 < zv := by
    have h1 : ⟪c, u0⟫ - ⟪b', u0⟫ = zv := by rw [hzv, inner_sub_left]
    rw [htouch.1, htouch.2, min_self, max_le_iff] at hgood
    have h2 : ⟪c', u0⟫ < ⟪c, u0⟫ := by
      by_contra hc; push Not at hc; exact hgood ⟨hc, le_refl _⟩
    linarith [htouch.2]
  have hm3eq : m3 = (1 - s) * zv + δ0 * U := by
    have h1 : d - b' = (c - b') + (s • (b - c) + δ0 • u0) := by rw [← hdc]; abel
    have h2 : ⟪b - c, u0⟫ = -zv := by
      have : b - c = (b - b') - (c - b') := by abel
      rw [this, inner_sub_left, hZb, hzv]; ring
    rw [hm3, h1, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2, hzv, hU]
    ring
  have hm3pos : 0 < m3 := by
    rw [hm3eq]; nlinarith [mul_pos hδ0 hUpos, mul_pos (show 0 < 1 - s by linarith) hzvpos]
  have hb2pos : 0 < b2 := by
    rw [hb2]; have := F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc; linarith
  have hr2pos : 0 < r2 := by
    rw [hr2]; have := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'); linarith
  have ha2pos : 0 < a2 := by
    rw [ha2]; have := F.a'b'c.neg a (by simp) haa' hab' hac; linarith
  have hApos : 0 < A := by rw [hAE]; exact hEpos
  -- the shadow tests
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F.swap₁.perm₂₃ hfar hq₂
  have hρc : crossXY (hfΦ c b' u0 fG c) (hfΦ c b' u0 fG b) (hfΦ c b' u0 fG b') = -(b2 * A) := by
    rw [hΦc, hΦb, hΦb']; simp only [crossXY]; ring
  have hρneg : -(b2 * A) ≤ 0 := neg_nonpos.mpr (mul_pos hb2pos hApos).le
  have hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0 := by
    have h := E3 b (by simp) hbc' hbb'
    have h2 := Fr.shadow_sign c b b' c' b' b h
    rw [hρc, hΦc', hΦb', hΦb] at h2
    have e : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨b1, b2, 0⟩ =
        (A - r1) * (b2 - r2) + r2 * (b1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  have hTa1 : (A - r1) * (a2 - r2) + r2 * (a1 - r1) < 0 := by
    have h := E3 a (by simp) hac' hab'
    have h2 := Fr.shadow_sign c b b' c' b' a h
    rw [hρc, hΦc', hΦb', hΦa] at h2
    have e : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨a1, a2, a3⟩ =
        (A - r1) * (a2 - r2) + r2 * (a1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  have hTa2 : (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) < 0 := by
    have h := E2 a (by simp) hab hac'
    have h2 := Fr.shadow_sign c b b' b c' a h
    rw [hρc, hΦb, hΦc', hΦa] at h2
    have e : crossXY ⟨b1, b2, 0⟩ ⟨r1, r2, 0⟩ ⟨a1, a2, a3⟩ =
        (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  -- the facets
  have evq0 : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ c b' u0 fG p = q → f p = 0 → (hfFc c b' u0 N f Nf).ev q = 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf, h0]
  have evql : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ c b' u0 fG p = q → f p < 0 → (hfFc c b' u0 N f Nf).ev q < 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf]; exact h0
  have cfg : N2Cfg E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      (hfFc c b' u0 N F.a'bc.f F.a'bc.N) (hfFc c b' u0 N F.abc'.f F.abc'.N)
      (hfFc c b' u0 N F.ab'c.f F.ab'c.N) (hfFc c b' u0 N F.ab'c'.f F.ab'c'.N)
      (hfFc c b' u0 N F.a'bc'.f F.a'bc'.N) (hfFc c b' u0 N F.a'b'c'.f F.a'b'c'.N) := by
    refine ⟨hEpos, hUpos, hzvpos, by linarith, hApos, hb2pos, hr2pos, ha2pos, hs0, hs1, hm3pos,
      hDr, hTa1, hTa2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- H = a'bc
    · exact evq0 _ _ F.a'bc.hN d _ hΦd hd.a'bc
    · exact evq0 _ _ F.a'bc.hN b _ hΦb F.a'bc.hQ
    · exact evq0 _ _ F.a'bc.hN a' _ hΦa' F.a'bc.hP
    · exact evq0 _ _ F.a'bc.hN c _ hΦc F.a'bc.hR
    · exact evql _ _ F.a'bc.hN a _ hΦa (F.a'bc.neg a (by simp) haa' hab hac)
    · exact evql _ _ F.a'bc.hN b' _ hΦb' (F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c)
    · exact evql _ _ F.a'bc.hN c' _ hΦc' (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
    -- Qab = abc'
    · exact evq0 _ _ F.abc'.hN d _ hΦd hd.abc'
    · exact evq0 _ _ F.abc'.hN a _ hΦa F.abc'.hP
    · exact evq0 _ _ F.abc'.hN c' _ hΦc' F.abc'.hR
    · exact evq0 _ _ F.abc'.hN b _ hΦb F.abc'.hQ
    · exact evql _ _ F.abc'.hN c _ hΦc (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
    · exact evql _ _ F.abc'.hN a' _ hΦa' (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c')
    · exact evql _ _ F.abc'.hN b' _ hΦb' (F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c')
    -- Qac = ab'c
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
  -- the middle `b'` over the chord `c a'`
  have hq0 : 0 < zv / U := div_pos hzvpos hUpos
  have hq1 : zv / U < 1 := by
    rw [div_lt_one hUpos]; linarith [cfg.zw_neg]
  have hτ : hfTau c b' u0 = -(zv / U) := by
    have : ⟪b' - c, u0⟫ = -zv := by
      rw [hzv, ← inner_neg_left, neg_sub]
    simp only [hfTau, this, hU]
    ring
  have hmidb' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s' : ℝ, 0 < s' ∧ s' < 1 ∧
      b' = c + s' • (a' - c) + (1 : ℝ) • (e - δ • u0) := by
    have h1 := eventually_pos_affine (A := zv / U) (B := -1) (Or.inl hq0)
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    filter_upwards [h1, h2] with δ hδ1 hδ2
    refine ⟨zv / U - δ, by linarith, by linarith, ?_⟩
    have : b' = c + (e + hfTau c b' u0 • u0) := by rw [← hbpc]; abel
    rw [this, hτ]
    have ha'c : a' - c = -u0 := by rw [hu0]; abel
    rw [ha'c]
    module
  have hXd : ⟪d - c, e⟫ = s * b1 := congrArg V3.x hΦd
  have hrim1 : ∀ i, rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3 i =
      hfΦ c b' u0 fG (quint c' a d c a' i) := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hΦc'.symm, hΦa.symm, hΦd.symm, hΦc.symm, hΦa'.symm]
  have hrim2 : ∀ i, rim2 zv zw s b1 b2 m3 i = hfΦ c b' u0 fG (quad b d c a' i) := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hΦb.symm, hΦd.symm, hΦc.symm, hΦa'.symm]
  rcases lt_or_gt_of_ne Tr2 with hlt | hgt
  · -- case 1: `c'` is farther than `b` from the plane of `G`
    have hr : b2 < r2 := by rw [hb2, hr2]; linarith
    obtain ⟨hA1, hb1'⟩ := Tbey hlt
    obtain ⟨σ, hσ⟩ := cfg.tests1 hr
    have hdep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal
        (dep (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3) δ) := by
      rcases lt_or_gt_of_ne Tb1 with hneg | hpos
      · obtain ⟨n2, n3, n4⟩ := Tnt hlt hneg
        refine cfg.depth1_neg hA1 hb1' hneg ?_ ?_ ?_
        · rintro ⟨h1, h2⟩
          apply n2; constructor
          · rw [show a - d = (a - c) - (d - c) by abel, inner_sub_left, hXd]; linarith
          · rw [show a - d = (a - b') - (d - b') by abel, inner_sub_left]; show a3 - m3 = 0; linarith
        · rintro ⟨h1, h2⟩
          apply n3; constructor
          · exact h1
          · rw [show a - c = (a - b') - (c - b') by abel, inner_sub_left]; show a3 - zv = 0; linarith
        · rintro ⟨h1, h2⟩
          apply n4; constructor
          · have : a' - c = -u0 := by rw [hu0]; abel
            rw [show a - a' = (a - c) - (a' - c) by abel, inner_sub_left, this, inner_neg_left, heu']
            simp only [neg_zero, sub_zero]; exact h1
          · rw [show a - a' = (a - b') - (a' - b') by abel, inner_sub_left]; show a3 - zw = 0; linarith
      · exact cfg.depth1_pos hr hA1 hb1' hpos
    refine HFrame.rim_final Fr (by norm_num : 3 ≤ 5) _ {b'} {c', a, d, c, a'} (quint c' a d c a') ?_ ?_ ?_ σ ?_
      (Thd1 hlt)
    · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [quint]
    · intro i
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [quint] <;> intro h <;> subst h <;> tauto
    · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [quint]
    · filter_upwards [hσ, hdep, hmidb'] with δ h1 h2 h3
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i j hi hj
        simpa only [hrim1] using h1.1 i j hi hj
      · intro y hy hyM hyx i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
        have hyb : y = b := by
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl (hyx 2)
          · exact absurd rfl (hyx 1)
          · exact absurd rfl (hyx 4)
          · rfl
          · exact absurd rfl hyM
          · exact absurd rfl (hyx 3)
          · exact absurd rfl (hyx 0)
        subst hyb
        simpa only [hrim1, hΦb] using h1.2 i
      · have : dep (rim1 zv zw r1 r2 s b1 b2 m3 a1 a2 a3) δ =
            dep (fun i => hfΦ c b' u0 fG (quint c' a d c a' i)) δ := by
          funext i; simp only [dep, hrim1]
        rw [← this]; exact h2
      · intro m hm
        rw [Finset.mem_singleton] at hm
        subst hm
        obtain ⟨s', hs0', hs1', heq⟩ := h3
        exact ⟨3, s', 1, hs0', hs1', one_ne_zero, heq⟩
  · -- case 2: `b` is farther than `c'` from the plane of `G`
    have hr : r2 < b2 := by rw [hb2, hr2]; linarith
    obtain ⟨σ, hσ⟩ := cfg.tests2 hr
    have hdep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsCyclicUnimodal
        (dep (rim2 zv zw s b1 b2 m3) δ) := by
      rcases lt_or_gt_of_ne Tb1 with hneg | hpos
      · exact cfg.depth2_neg hneg
      · exact cfg.depth2_pos hpos
    refine HFrame.rim_final Fr (by norm_num : 3 ≤ 4) _ {b'} {b, d, c, a'} (quad b d c a') ?_ ?_ ?_ σ ?_
      (Thd2 hgt)
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad] <;> intro h <;> subst h <;> tauto
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
    · filter_upwards [hσ, hdep, hmidb'] with δ h1 h2 h3
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i j hi hj
        simpa only [hrim2] using h1.1 i j hi hj
      · intro y hy hyM hyx i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl (hyx 1)
        · simpa only [hrim2, hΦa] using h1.2.2 i
        · exact absurd rfl (hyx 3)
        · exact absurd rfl (hyx 0)
        · exact absurd rfl hyM
        · exact absurd rfl (hyx 2)
        · simpa only [hrim2, hΦc'] using h1.2.1 i
      · have : dep (rim2 zv zw s b1 b2 m3) δ =
            dep (fun i => hfΦ c b' u0 fG (quad b d c a' i)) δ := by
          funext i; simp only [dep, hrim2]
        rw [← this]; exact h2
      · intro m hm
        rw [Finset.mem_singleton] at hm
        subst hm
        obtain ⟨s', hs0', hs1', heq⟩ := h3
        exact ⟨2, s', 1, hs0', hs1', one_ne_zero, heq⟩

end N2

end Minimality
end
