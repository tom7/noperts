module

public import Minimality.Type08Codim

@[expose] public section

/-!
# Type 08: one planar equator (`FEWER-FACES-PROOFS.md` §10 addendum, Lemma K)

Theorem 10.1 assumes that the octahedron `O = K − d` has no planar equator
(`κ_X ≠ 0` for its three pairs).  Lemma K of the addendum allows one: if `κ_X = 0`, take
for `W = {c, c'}` one of the other two pairs; since `[y w]` and `[x w]` have opposite
signs (pole coordinates for `W`), after mirroring so that the third pair `Y` is
unprimed, either `X` takes the role `a` (K-A: `κ_a = 0`, `κ_b > 0`, `[b c] < 0`) or the
role `b` (K-B: `κ_a > 0`, `κ_b = 0`, `[b c] < 0`).

* K-A: Lemma 7's quad edge needs only the pole signs of `B`, `C`, and `(G4)` for the face
  `ab'c'` (`[a' c] ≥ 0`; `type08_quad_edge`).  "Not bad", in case N2 for `a' → c` and in
  case T4 for `d → b`, follows from the planar equator `b c b' c'` of `A`: its diagonals
  `b b'` and `c c'` cross (`flat_cross`), so `max (z c, z c') ≥ z m ≥ min (z b, z b')` and
  the same with `b`, `c` exchanged; a bad edge needs the quadruple tie `z b = z b'`,
  `z c = z c'` (`not_bad_of_cross`), excluded by `Type08Gen.flatN2`, `flatT4`.
* K-B: `g_b ∥ g_b'`; the signs `[b a^±], [b' a^±] > 0 > [b c^±], [b' c^±]` come from
  `(G4)` (faces of `O`, `pair_sign`) instead of the pole signs of `B` (`flatB_signs`).
  Lemma 1 (a), (b) hold with `[b' a'] ≠ 0`, `[b' c'] ≠ 0` (`far_end_Qbc_iff'`,
  `far_end_Qab_iff'`); case N2 is Lemma 7 with `[b ·] ∝ [b' ·]`; the T4 case is empty by
  the far-end identity `α + β = κ_b` (`galeD_sum`).
* `isRupert_type08_flat`: Theorem 10.1′ (Lean form) with at most one planar equator.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Two products with a common factor of one sign: the other factors share a sign. -/
theorem pos_mul_of_neg_mul_neg {x y z : ℝ} (h1 : x * z < 0) (h2 : y * z < 0) : 0 < x * y := by
  have h := mul_pos_of_neg_of_neg h1 h2
  have hz : z ≠ 0 := by rintro rfl; simp at h1
  have e : x * z * (y * z) = x * y * (z * z) := by ring
  rw [e] at h
  exact (mul_pos_iff_of_pos_right (mul_self_pos.mpr hz)).mp h

/-- A weight `y / (x + y)` of two numbers of one sign lies in `(0, 1)`. -/
theorem frac_mem_Ioo {x y : ℝ} (hxy : 0 < x * y) : 0 < y / (x + y) ∧ y / (x + y) < 1 := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hxy) with hx | hx
  · have hy : y < 0 := by nlinarith
    exact ⟨div_pos_of_neg_of_neg hy (by linarith), (div_lt_one_of_neg (by linarith)).mpr
      (by linarith)⟩
  · have hy : 0 < y := by nlinarith
    exact ⟨div_pos hy (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

theorem add_ne_zero_of_mul_pos {x y : ℝ} (hxy : 0 < x * y) : x + y ≠ 0 := by
  intro h0
  have : y = -x := by linarith
  rw [this] at hxy; nlinarith [mul_self_nonneg x]

/-- **The diagonals of a planar equator cross.**  If `κ_A = 0`, the equator `b c b' c'`
is a planar convex quadrilateral whose diagonals `b b'` and `c c'` meet at a point inside
both. -/
theorem flat_cross {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκ : galeD G.l G.m a a' = 0) :
    ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧
      (1 - lam) • b + lam • b' = (1 - mu) • c + mu • c' := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  simp only [galeD] at hκ
  obtain ⟨α, β, hne, h1, h2⟩ : ∃ α β : ℝ, ¬(α = 0 ∧ β = 0) ∧ α * G.l a + β * G.m a = 0 ∧
      α * G.l a' + β * G.m a' = 0 := by
    by_cases ha : G.l a = 0 ∧ G.m a = 0
    · by_cases ha' : G.l a' = 0 ∧ G.m a' = 0
      · exact ⟨1, 0, by simp, by simp [ha.1], by simp [ha'.1]⟩
      · refine ⟨G.m a', -G.l a', fun h => ha' ⟨by linarith [h.2], h.1⟩, ?_, ?_⟩
        · linear_combination hκ
        · ring
    · refine ⟨G.m a, -G.l a, fun h => ha ⟨by linarith [h.2], h.1⟩, ?_, ?_⟩
      · ring
      · linear_combination -hκ
  have hL := G.hl.comb G.hm α β
  set L : ℝ³ → ℝ := fun t => α * G.l t + β * G.m t with hLdef
  have h1' : L a = 0 := h1
  have h2' : L a' = 0 := h2
  -- the four faces at `a`
  have r1 := hL.apply F.abc.hN
  rw [F.abc.hP, F.abc.hQ, F.abc.hR, h2'] at r1
  have r2 := hL.apply F.abc'.hN
  rw [F.abc'.hP, F.abc'.hQ, F.abc'.hR, h2'] at r2
  have r3 := hL.apply F.ab'c.hN
  rw [F.ab'c.hP, F.ab'c.hQ, F.ab'c.hR, h2'] at r3
  have r4 := hL.apply F.ab'c'.hN
  rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, h2'] at r4
  obtain ⟨s1, z1⟩ := pair_sign (L₁ := L b') (L₂ := L c') (by linarith)
    (F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c)
    (F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc'))
  obtain ⟨s2, z2⟩ := pair_sign (L₁ := L b') (L₂ := L c) (by linarith)
    (F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c')
    (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
  obtain ⟨s3, z3⟩ := pair_sign (L₁ := L b) (L₂ := L c') (by linarith)
    (F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc)
    (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
  obtain ⟨s4, z4⟩ := pair_sign (L₁ := L b) (L₂ := L c) (by linarith)
    (F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc')
    (F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc')
  have hLb : L b ≠ 0 := by
    intro h0
    have e4 := z4.mp h0; have e3 := z3.mp h0; have e2 := z2.mpr e4
    exact hne (G.indep α β h1 h2 h0 e2 e4 e3)
  have hLc : L c ≠ 0 := fun h0 => hLb (z4.mpr h0)
  have hLc' : L c' ≠ 0 := fun h0 => hLb (z3.mpr h0)
  have hLb' : L b' ≠ 0 := fun h0 => hLc (z2.mp h0)
  have q4 : L b * L c < 0 := lt_of_le_of_ne s4 (mul_ne_zero hLb hLc)
  have q2 : L b' * L c < 0 := lt_of_le_of_ne s2 (mul_ne_zero hLb' hLc)
  have q3 : L b * L c' < 0 := lt_of_le_of_ne s3 (mul_ne_zero hLb hLc')
  have hbb : 0 < L b * L b' := pos_mul_of_neg_mul_neg q4 q2
  have hcc2 : 0 < L c * L c' := by
    rw [mul_comm] at q4 q3; exact pos_mul_of_neg_mul_neg q4 q3
  have hs := hL.sum; have hv := hL.vsum
  rw [h1', h2'] at hs
  rw [h1', h2', zero_smul, zero_smul, zero_add, zero_add] at hv
  -- `lam = L b' / (L b + L b')`, `mu = L c' / (L c + L c')`
  have hsb : L b + L b' ≠ 0 := add_ne_zero_of_mul_pos hbb
  have hsc : L c + L c' ≠ 0 := add_ne_zero_of_mul_pos hcc2
  obtain ⟨hlam0, hlam1⟩ := frac_mem_Ioo hbb
  obtain ⟨hmu0, hmu1⟩ := frac_mem_Ioo hcc2
  refine ⟨L b' / (L b + L b'), L c' / (L c + L c'), hlam0, hlam1, hmu0, hmu1, ?_⟩
  have e1 : (1 - L b' / (L b + L b')) • b + (L b' / (L b + L b')) • b' =
      (1 / (L b + L b')) • (L b • b + L b' • b') := by
    match_scalars <;> field_simp
    ring
  have e2 : (1 - L c' / (L c + L c')) • c + (L c' / (L c + L c')) • c' =
      (1 / (L c + L c')) • (L c • c + L c' • c') := by
    match_scalars <;> field_simp
    ring
  have e3 : L c • c + L c' • c' = -(L b • b + L b' • b') := by
    rw [eq_neg_iff_add_eq_zero, ← hv]; abel
  have e4 : L c + L c' = -(L b + L b') := by linarith
  rw [e1, e2, e3, e4, smul_neg, ← neg_smul, one_div, one_div, inv_neg, neg_neg]

/-- **"Not bad" from crossing diagonals.**  If the segments `b b'` and `c c'` cross at a
point inside both, no depth puts `c, c'` weakly below `b, b'` unless `z b = z b'` and
`z c = z c'`. -/
theorem not_bad_of_cross {b b' c c' : ℝ³} {lam mu : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu)
    (hmu1 : mu < 1) (hm : (1 - lam) • b + lam • b' = (1 - mu) • c + mu • c') (u : ℝ³)
    (htie : ¬ (⟪b, u⟫ = ⟪b', u⟫ ∧ ⟪c, u⟫ = ⟪c', u⟫)) :
    ¬ max ⟪c, u⟫ ⟪c', u⟫ ≤ min ⟪b, u⟫ ⟪b', u⟫ := by
  intro hbad
  have hz := congrArg (fun v => ⟪v, u⟫) hm
  simp only [inner_add_left, real_inner_smul_left] at hz
  simp only [max_le_iff, le_min_iff] at hbad
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  apply htie
  constructor
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [mul_pos hlam0 (sub_pos.mpr h), mul_nonneg hmu0.le (sub_nonneg.mpr h4),
        mul_nonneg (sub_pos.mpr hmu1).le (sub_nonneg.mpr h2)]
    · nlinarith [mul_pos (sub_pos.mpr hlam1) (sub_pos.mpr h), mul_nonneg hmu0.le (sub_nonneg.mpr h3),
        mul_nonneg (sub_pos.mpr hmu1).le (sub_nonneg.mpr h1)]
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [mul_pos hmu0 (sub_pos.mpr h), mul_nonneg hlam0.le (sub_nonneg.mpr h4),
        mul_nonneg (sub_pos.mpr hlam1).le (sub_nonneg.mpr h3)]
    · nlinarith [mul_pos (sub_pos.mpr hmu1) (sub_pos.mpr h), mul_nonneg hlam0.le (sub_nonneg.mpr h2),
        mul_nonneg (sub_pos.mpr hlam1).le (sub_nonneg.mpr h1)]

/-- **Lemma 7, the quad edge, without the pole signs of `A`.**  In the labelling of
Lemma 6 with `κ_b > 0` (`κ_a` arbitrary), if the far end of `Q_bc` along `d b` is `a'`, then
`a' → c` is a quad edge of `O` (`a` hidden).  `(G4)` for the face `ab'c'` gives
`[a' c] ≥ 0`, which is all the Plücker step needs. -/
theorem type08_quad_edge {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hfar : F.abc'.f a' < F.abc'.f c) :
    F.ab'c'.f a' < F.ab'c'.f c := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨b1, -, b3⟩ := pole_signs F.perm₁₂ (hl.galeD hm b).perm₁₂ (self b) hκb.ne'
  have gba : 0 < galeD G.l G.m b a := pos_of_mul_neg_neg b3 hU
  have gba' : 0 < galeD G.l G.m b a' := pos_of_mul_pos_pos b1 gba
  obtain ⟨-, c2, -⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂ (self c) hκc
  have gcb : 0 < galeD G.l G.m c b := by rw [anti]; linarith
  have gcb' : 0 < galeD G.l G.m c b' := pos_of_mul_pos_pos c2 gcb
  have gb'c : galeD G.l G.m b' c < 0 := by rw [anti]; linarith
  obtain ⟨d1, -, d3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁ (self b')
    (by rw [anti]; linarith)
  have gb'a : 0 < galeD G.l G.m b' a := pos_of_mul_neg_neg d3 gb'c
  have gb'a' : 0 < galeD G.l G.m b' a' := pos_of_mul_pos_pos d1 gb'a
  -- `(G4)` for the face `ab'c'`: `[a' b] [a' c] ≤ 0`, so `[a' c] ≥ 0`
  have r := (hl.galeD hm a').apply F.ab'c'.hN
  rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, self a'] at r
  obtain ⟨sp, -⟩ := pair_sign (L₁ := galeD G.l G.m a' b) (L₂ := galeD G.l G.m a' c)
    (by linarith) (F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc')
    (F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc')
  have ga'b : galeD G.l G.m a' b < 0 := by rw [anti]; linarith
  have ga'c : 0 ≤ galeD G.l G.m a' c := by
    by_contra h; push Not at h; nlinarith
  -- Lemma 1 (a): `[b' a'] + [b' c] < 0`
  have hs : galeD G.l G.m b' a' + galeD G.l G.m b' c < 0 :=
    neg_of_mul_neg_pos (by rw [mul_comm]; exact (far_end_Qbc_iff F G hκb.ne').mp hfar) gb'a'
  have hpl := galeD_plucker G.l G.m b b' a' c
  have hsb : galeD G.l G.m b a' + galeD G.l G.m b c < 0 := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ -galeD G.l G.m b' c by linarith),
      mul_lt_mul_of_pos_left (show galeD G.l G.m b' a' < -galeD G.l G.m b' c by linarith)
        (show 0 < -galeD G.l G.m b c by linarith), mul_nonneg hκb.le ga'c]
  exact facet_lt_of_dep (hl.galeD hm b).swap₁.perm₂₃.swap₃ (F.swap₁.perm₂₃.swap₃).a'b'c
    (by simp) (by simp) (F.swap₁.perm₂₃.swap₃).nodup (self b) (mul_neg_of_pos_of_neg gba' hsb)

/-- **Theorem 10.1 by slides, normalized, K-A** (`κ_a = 0`: the equator of `A` is planar). -/
theorem isRupert_type08_flatA {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) (G : GaleData a a' b b' c c') (hκa : galeD G.l G.m a a' = 0)
    (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hgen : Type08Gen a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨lam, mu, hlam0, hlam1, hmu0, hmu1, hm⟩ := flat_cross F G hκa
  have hpl := G.planar_of_kappa hκa
  have e : det3 (b - c) (c' - c) (b' - c) = det3 (c - b) (b' - b) (c' - b) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫ :=
    not_bad_of_cross hmu0 hmu1 hlam0 hlam1 hm.symm _ (fun h => hgen.flatT4 hpl ⟨h.2, h.1⟩)
  exact isRupert_type08_slide_core F hd (fun hfar => ⟨type08_quad_edge F G hκb hκc hU hfar,
    not_bad_of_cross hlam0 hlam1 hmu0 hmu1 hm _ (hgen.flatN2 hpl)⟩) (fun _ _ => hgood)
    (type08_T_far F G hκb hκc hU) (type08_T'_far F G hκb hκc hU) (fun _ => hgood)
    (by rw [e, hpl, zero_mul]) (by rw [hpl, mul_zero]) hgen

/-- The signs of K-B (`κ_b = 0`): `(G4)` for the faces of `O` puts `g_a^±` and `g_c^±`
strictly on opposite sides of the line of `g_b ∥ g_b'`. -/
theorem flatB_signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0) :
    0 < galeD G.l G.m b a ∧ 0 < galeD G.l G.m b a' ∧ galeD G.l G.m b c' < 0 ∧
    0 < galeD G.l G.m b' a ∧ 0 < galeD G.l G.m b' a' ∧ galeD G.l G.m b' c < 0 ∧
      galeD G.l G.m b' c' < 0 ∧
    0 < galeD G.l G.m a c ∧ 0 < galeD G.l G.m a c' := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨-, c2, -⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂ (self c) hκc
  have gcb : 0 < galeD G.l G.m c b := by rw [anti]; linarith
  have gcb' : 0 < galeD G.l G.m c b' := pos_of_mul_pos_pos c2 gcb
  have gb'c : galeD G.l G.m b' c < 0 := by rw [anti]; linarith
  -- `(G4)`: a dependency vanishing at one point of a face's complement
  have pos_of_pair : ∀ {L₁ L₂ f₁ f₂ : ℝ}, L₁ * f₁ + L₂ * f₂ = 0 → f₁ < 0 → f₂ < 0 → L₂ < 0 →
      0 < L₁ := by
    intro L₁ L₂ f₁ f₂ h h₁ h₂ hL₂
    obtain ⟨s, z⟩ := pair_sign h h₁ h₂
    rcases lt_or_gt_of_ne (show L₁ ≠ 0 from fun h0 => hL₂.ne (z.mp h0)) with h' | h'
    · nlinarith
    · exact h'
  have neg_of_pair : ∀ {L₁ L₂ f₁ f₂ : ℝ}, L₁ * f₁ + L₂ * f₂ = 0 → f₁ < 0 → f₂ < 0 → 0 < L₁ →
      L₂ < 0 := by
    intro L₁ L₂ f₁ f₂ h h₁ h₂ hL₁
    obtain ⟨s, z⟩ := pair_sign h h₁ h₂
    rcases lt_or_gt_of_ne (show L₂ ≠ 0 from fun h0 => hL₁.ne' (z.mpr h0)) with h' | h'
    · exact h'
    · nlinarith
  -- `[b ·]` on the faces `a'b'c'`, `ab'c'`, `a'b'c`
  have r1 := (hl.galeD hm b).apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, self b] at r1
  have gba := pos_of_pair (L₁ := galeD G.l G.m b a) (L₂ := galeD G.l G.m b c) (by linarith)
    (F.a'b'c'.neg a (by simp) haa' hab' hac') (F.a'b'c'.neg c (by simp) (Ne.symm ha'c)
      (Ne.symm hb'c) hcc') hU
  have r2 := (hl.galeD hm b).apply F.ab'c'.hN
  rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, self b] at r2
  have gba' := pos_of_pair (L₁ := galeD G.l G.m b a') (L₂ := galeD G.l G.m b c) (by linarith)
    (F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c') (F.ab'c'.neg c (by simp) (Ne.symm hac)
      (Ne.symm hb'c) hcc') hU
  have r3 := (hl.galeD hm b).apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, self b] at r3
  have gbc' := neg_of_pair (L₁ := galeD G.l G.m b a) (L₂ := galeD G.l G.m b c') (by linarith)
    (F.a'b'c.neg a (by simp) haa' hab' hac) (F.a'b'c.neg c' (by simp) (Ne.symm ha'c')
      (Ne.symm hb'c') (Ne.symm hcc')) gba
  -- `[b' ·]` on the faces `a'bc'`, `abc'`, `a'bc`
  have r4 := (hl.galeD hm b').apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, self b'] at r4
  have gb'a := pos_of_pair (L₁ := galeD G.l G.m b' a) (L₂ := galeD G.l G.m b' c) (by linarith)
    (F.a'bc'.neg a (by simp) haa' hab hac') (F.a'bc'.neg c (by simp) (Ne.symm ha'c)
      (Ne.symm hbc) hcc') gb'c
  have r5 := (hl.galeD hm b').apply F.abc'.hN
  rw [F.abc'.hP, F.abc'.hQ, F.abc'.hR, self b'] at r5
  have gb'a' := pos_of_pair (L₁ := galeD G.l G.m b' a') (L₂ := galeD G.l G.m b' c) (by linarith)
    (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c') (F.abc'.neg c (by simp) (Ne.symm hac)
      (Ne.symm hbc) hcc') gb'c
  have r6 := (hl.galeD hm b').apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, self b'] at r6
  have gb'c' := neg_of_pair (L₁ := galeD G.l G.m b' a) (L₂ := galeD G.l G.m b' c') (by linarith)
    (F.a'bc.neg a (by simp) haa' hab hac) (F.a'bc.neg c' (by simp) (Ne.symm ha'c')
      (Ne.symm hbc') (Ne.symm hcc')) gb'a
  -- the pole signs of `A`
  obtain ⟨-, f2, f3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  have gab : galeD G.l G.m a b < 0 := by rw [anti]; linarith
  have gac : 0 < galeD G.l G.m a c := pos_of_mul_neg_neg (by rwa [mul_comm] at f3) gab
  have gac' : 0 < galeD G.l G.m a c' := pos_of_mul_pos_pos f2 gac
  exact ⟨gba, gba', gbc', gb'a, gb'a', gb'c, gb'c', gac, gac'⟩

/-- **Theorem 10.1 by slides, normalized, K-B** (`κ_b = 0`: the equator of `B` is planar).
Case N2 is Lemma 7 with `[b ·] ∝ [b' ·]`; the T4 case is empty (`α + β = κ_b = 0`). -/
theorem isRupert_type08_flatB {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : galeD G.l G.m b b' = 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hgen : Type08Gen a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨hba, hba', -, hb'a, hb'a', hb'c, hb'c', hac, hac'⟩ := flatB_signs F G hκa hκc hU
  obtain ⟨e1, e2, e3⟩ := type08_tie_sums F G hb'a'.ne' hb'c'.ne
  rw [hκb] at e3
  have hsides := type08_rd_sides F.isOctahedron G hκa (by rw [anti]; linarith)
    (by rw [anti]; linarith) hac hac'
  refine isRupert_type08_slide_core F hd (fun hfar => ?_) (fun hfc hfc' => ?_)
    (fun hT => absurd ⟨hd.tieT_geom hT, hd.tieT'_geom (e2.mpr (by linarith [e1.mp hT]))⟩
      hgen.tieTT')
    (fun hT' hT => absurd (e1.mpr (by linarith [e2.mp hT'])) hT)
    (fun hTT => absurd (hTT.elim (fun hT => ⟨hd.tieT_geom hT,
        hd.tieT'_geom (e2.mpr (by linarith [e1.mp hT]))⟩)
      (fun hT' => ⟨hd.tieT_geom (e1.mpr (by linarith [e2.mp hT'])), hd.tieT'_geom hT'⟩))
      hgen.tieTT') hsides.1.le hsides.2.le hgen
  · -- case N2: Lemma 7 with `[b a'] [b' c] = [b c] [b' a']`
    have hs : galeD G.l G.m b' a' + galeD G.l G.m b' c < 0 :=
      neg_of_mul_neg_pos (by rw [mul_comm]; exact (far_end_Qbc_iff' F G hb'a'.ne').mp hfar) hb'a'
    have hpl := galeD_plucker G.l G.m b b' a' c
    rw [hκb, zero_mul, zero_sub] at hpl
    have hsb : galeD G.l G.m b a' + galeD G.l G.m b c < 0 := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos hba' (show 0 < -galeD G.l G.m b' c - galeD G.l G.m b' a' by linarith)]
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    refine ⟨facet_lt_of_dep (hl.galeD hm b).swap₁.perm₂₃.swap₃ (F.swap₁.perm₂₃.swap₃).a'b'c
      (by simp) (by simp) (F.swap₁.perm₂₃.swap₃).nodup (self b) (mul_neg_of_pos_of_neg hba' hsb),
      ?_⟩
    exact not_bad_of_dep (L := fun t => galeD G.l G.m t a) (hl.galeD' hm a).swap₁.perm₂₃
      hnd.2.1.2.2.1 (self a) (by rw [anti]; linarith) (by rw [anti a a', anti a c]; linarith)
      (by rw [anti]; linarith) hba.le hb'a.le
  · -- case T4 is empty: `[b' a] + [b' c'] > 0`, `[b' a'] + [b' c] ≥ 0`, sum `κ_b = 0`
    exfalso
    have h1 : 0 < galeD G.l G.m b' c' + galeD G.l G.m b' a := by
      have := (far_end_Qab_iff' F G hb'c'.ne).mp hfc'
      nlinarith
    have h2 : 0 ≤ galeD G.l G.m b' a' + galeD G.l G.m b' c := by
      by_contra h; push Not at h
      have := (far_end_Qbc_iff' F G hb'a'.ne').mpr (mul_neg_of_pos_of_neg hb'a' h)
      linarith
    have hsum := galeD_sum hl hm b'
    rw [self b', anti b b', hκb, neg_zero] at hsum
    linarith

/-- **Theorem 10.1′ (type 08), Lean form, with at most one planar equator.**  As
`isRupert_type08_slide`, but `O` may have one planar equator (Lemma K): two planar
equators are excluded (codimension 2), and at a planar equator `Type08Gen` excludes a
quadruple tie at the named views (`flatN2`, `flatT4`). -/
theorem isRupert_type08_flat {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d)
    (hflat : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (c - a) (a' - a) (c' - a) = 0) ∧
      ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0) ∧
      ¬ (det3 (c - a) (a' - a) (c' - a) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0))
    (hgen : Type08GenAll a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := hflat
  obtain ⟨G⟩ := F.nonempty_galeData
  have pA : galeD G.l G.m a a' = 0 → det3 (c - b) (b' - b) (c' - b) = 0 := G.planar_of_kappa
  have pB : galeD G.l G.m b b' = 0 → det3 (c - a) (a' - a) (c' - a) = 0 :=
    G.perm₁₂.planar_of_kappa
  have pC : galeD G.l G.m c c' = 0 → det3 (b - a) (a' - a) (b' - a) = 0 :=
    G.perm₂₃.perm₁₂.planar_of_kappa
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen
  have e := type08_set_perm a a' b b' c c' d
  -- mirror the Gale vectors so that a given `κ` is positive
  have mirror : ∀ (s t : ℝ³), galeD G.l G.m s t ≠ 0 → ∃ G' : GaleData a a' b b' c c',
      0 < galeD G'.l G'.m s t ∧ ∀ x y, galeD G'.l G'.m x y = 0 ↔ galeD G.l G.m x y = 0 := by
    intro s t hst
    rcases lt_or_gt_of_ne hst with hn | hp
    · exact ⟨G.mirror, by rw [G.galeD_mirror]; linarith,
        fun x y => by rw [G.galeD_mirror, neg_eq_zero]⟩
    · exact ⟨G, hp, fun x y => Iff.rfl⟩
  by_cases ha : galeD G.l G.m a a' = 0
  · have hb : galeD G.l G.m b b' ≠ 0 := fun h => hf1 ⟨pA ha, pB h⟩
    have hc : galeD G.l G.m c c' ≠ 0 := fun h => hf2 ⟨pA ha, pC h⟩
    obtain ⟨G', hb', hz⟩ := mirror b b' hb
    have ha' : galeD G'.l G'.m a a' = 0 := (hz a a').mpr ha
    have hc' : galeD G'.l G'.m c c' ≠ 0 := fun h => hc ((hz c c').mp h)
    obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G'.hl.galeD G'.hm c).perm₂₃.perm₁₂
      (galeD_self _ _ c) hc'
    rcases lt_or_ge (galeD G'.l G'.m b c) 0 with hU | hU
    · exact isRupert_type08_flatA F hd G' ha' hb' hc' hU g1
    · have hU' : galeD G'.l G'.m a c < 0 := by
        rw [galeD_anti _ _ a c, galeD_anti _ _ b c] at c3; nlinarith
      rw [← e.2.1]
      exact isRupert_type08_flatB F.perm₁₂ hd.perm₁₂ G'.perm₁₂ hb' ha' hc' hU' g2
  · by_cases hb : galeD G.l G.m b b' = 0
    · have hc : galeD G.l G.m c c' ≠ 0 := fun h => hf3 ⟨pB hb, pC h⟩
      obtain ⟨G', ha', hz⟩ := mirror a a' ha
      have hb' : galeD G'.l G'.m b b' = 0 := (hz b b').mpr hb
      have hc' : galeD G'.l G'.m c c' ≠ 0 := fun h => hc ((hz c c').mp h)
      obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G'.hl.galeD G'.hm c).perm₂₃.perm₁₂
        (galeD_self _ _ c) hc'
      rcases lt_or_ge (galeD G'.l G'.m a c) 0 with hU | hU
      · rw [← e.2.1]
        exact isRupert_type08_flatA F.perm₁₂ hd.perm₁₂ G'.perm₁₂ hb' ha' hc' hU g2
      · have hU' : galeD G'.l G'.m b c < 0 := by
          rw [galeD_anti _ _ a c, galeD_anti _ _ b c] at c3; nlinarith
        exact isRupert_type08_flatB F hd G' ha' hb' hc' hU' g1
    · by_cases hc : galeD G.l G.m c c' = 0
      · obtain ⟨G', ha', hz⟩ := mirror a a' ha
        have hb' : galeD G'.l G'.m b b' ≠ 0 := fun h => hb ((hz b b').mp h)
        have hc' : galeD G'.l G'.m c c' = 0 := (hz c c').mpr hc
        obtain ⟨-, -, b3⟩ := pole_signs F.perm₁₂ (G'.hl.galeD G'.hm b).perm₁₂
          (galeD_self _ _ b) hb'
        rcases lt_or_ge (galeD G'.l G'.m a b) 0 with hU | hU
        · rw [← e.2.2.2.1]
          exact isRupert_type08_flatA F.perm₂₃.perm₁₂ hd.perm₂₃.perm₁₂ G'.perm₂₃.perm₁₂ hc' ha'
            hb' hU g4
        · have hU' : galeD G'.l G'.m c b < 0 := by
            rw [galeD_anti _ _ a b, galeD_anti _ _ c b] at b3; nlinarith
          rw [← e.2.2.1]
          exact isRupert_type08_flatB F.perm₂₃ hd.perm₂₃ G'.perm₂₃ ha' hc' hb' hU' g3
      · exact isRupert_type08_slide_gale F hd G ha hb hc ⟨g1, g2, g3, g4, g5, g6⟩


/-- **Theorem 10.1′, facet form (type 08).**  Seven points labelled as type 08
(`typeb_lib.load('08-7f')`: the quadrilaterals `0123`, `0245`, `2356` and the triangles
`014`, `136`, `146`, `456` are facets), such that the octahedron `x 0, …, x 6` without
`x 2` (pairs `(0, 6)`, `(3, 4)`, `(5, 1)`) has at most one planar equator and
`Type08GenAll` holds for it and the cap `x 2`, are Rupert. -/
theorem isRupert_type08_flat_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hflat : ¬ (det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) = 0 ∧
        det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) = 0) ∧
      ¬ (det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) = 0 ∧
        det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) = 0) ∧
      ¬ (det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) = 0 ∧
        det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) = 0))
    (hgen : Type08GenAll (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2)) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact isRupert_type08_flat F hcap hflat hgen

end Minimality

end
