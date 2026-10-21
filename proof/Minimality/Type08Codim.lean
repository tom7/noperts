module

public import Minimality.Type08Tie
public import Minimality.Type08R0

@[expose] public section

/-!
# Type 08: Theorem 10.1′ (Lean form) (`FEWER-FACES-PROOFS.md` §10 addendum)

The case analysis of Theorem 10.1 with the slides of Lemma C (`Type08Slide.lean`), the
five-corner rims of Lemma H, and the far-end ties `T`, `T'` of Lemma X
(`Type08Tie.lean`): `Type08Gen` collects what is used in one labelling, `Type08GenAll`
in all six.

For the one-circle closings `K_c` (N2) and `K_b` (T4), `Type08Gen` also accepts the
two-peaked five-corner rim of `R_d` (`RdCond`; Lemma R0 and Theorem R of A.10,
`Type08R0.lean`, `Type08Rd.lean`).

* `t4_kappa_pos`: in the T4 case `b'` is a corner of the view along `d b` (part of
  Lemma G: no (G1) failure there).
* `isRupert_type08_slide_core`: the case analysis, given the Gale inputs of Lemma 7, of the
  T4 "not bad" and of (H4) in Lemma R0 (weakly), and the far ends at the ties.
* `isRupert_type08_slide_normalized`, `isRupert_type08_slide_gale`,
  `isRupert_type08_slide`, `isRupert_type08_slide_facets`: Theorem 10.1′ without planar
  equators (Lemma K is `Type08Flat.lean`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Theorem 10.1 by slides -/

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

/-- **Lemma 1 (a) of §10, Gale form, with `[b' a'] ≠ 0`** (no assumption on `κ_b`). -/
theorem far_end_Qbc_iff' {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hne : galeD G.l G.m b' a' ≠ 0) :
    F.abc'.f a' < F.abc'.f c ↔
      galeD G.l G.m b' a' * (galeD G.l G.m b' a' + galeD G.l G.m b' c) < 0 :=
  facet_lt_iff_of_dep (G.hl.galeD G.hm b').swap₁.perm₂₃ (F.swap₁.perm₂₃).a'b'c
    (by simp) (by simp) (F.swap₁.perm₂₃).nodup (galeD_self _ _ b') hne

/-- **Lemma 1 (b) of §10, Gale form, with `[b' c'] ≠ 0`.** -/
theorem far_end_Qab_iff' {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hne : galeD G.l G.m b' c' ≠ 0) :
    F.a'bc.f c' < F.a'bc.f a ↔
      galeD G.l G.m b' c' * (galeD G.l G.m b' c' + galeD G.l G.m b' a) < 0 :=
  facet_lt_iff_of_dep (G.hl.galeD G.hm b').perm₂₃.perm₁₂.swap₁
    (F.perm₂₃.perm₁₂.swap₁).a'b'c (by simp) (by simp) (F.perm₂₃.perm₁₂.swap₁).nodup
    (galeD_self _ _ b') hne

/-- **Lemma 9.6 (one facet), the tie.**  With the notation of `facet_lt_iff_of_dep`,
the facet values at `x` and `y` agree iff `L x + L y = 0`. -/
theorem facet_eq_iff_of_dep {x x' y y' p p' : ℝ³} {L : ℝ³ → ℝ} (hL : IsDep x x' y y' p p' L)
    {V : Finset ℝ³} (G : FacetFn V x' y' p) (hyV : y ∈ V)
    (hnd : [x, x', y, y', p, p'].Nodup) (h0 : L p' = 0) (hLx : L x ≠ 0) :
    G.f x = G.f y ↔ L x + L y = 0 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨-, ⟨hx'y, -, -, -⟩, ⟨hyy', hyp, -⟩, -, -, -⟩ := hnd
  have r := hL.apply G.hN
  rw [G.hP, G.hQ, G.hR, h0] at r
  have ny := G.neg y hyV (Ne.symm hx'y) hyy' hyp
  have e : L x * L x * (G.f x - G.f y) = -(L x * (L x + L y)) * G.f y := by
    linear_combination L x * r
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at e
    have e' : L x * (L x + L y) * G.f y = 0 := by linarith
    rcases mul_eq_zero.mp e' with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hLx
    · exact absurd h1 ny.ne
  · intro h
    rw [h, mul_zero, neg_zero, zero_mul] at e
    have := (mul_eq_zero.mp e).resolve_left (mul_self_ne_zero.mpr hLx)
    linarith

/-- The Gale signs at `b'` in the labelling of Lemma 6 (no assumption on `κ_a`). -/
theorem type08_b'_signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) :
    0 < galeD G.l G.m b' a ∧ 0 < galeD G.l G.m b' a' ∧ galeD G.l G.m b' c < 0 ∧
      galeD G.l G.m b' c' < 0 := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨-, c2, -⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂ (self c) hκc
  have gcb : 0 < galeD G.l G.m c b := by rw [anti]; linarith
  have gcb' : 0 < galeD G.l G.m c b' := pos_of_mul_pos_pos c2 gcb
  have gb'c : galeD G.l G.m b' c < 0 := by rw [anti]; linarith
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁ (self b')
    (by rw [anti]; exact neg_ne_zero.mpr hκb)
  have gb'a : 0 < galeD G.l G.m b' a := pos_of_mul_neg_neg d3 gb'c
  exact ⟨gb'a, pos_of_mul_pos_pos d1 gb'a, gb'c, neg_of_mul_pos_neg d2 gb'c⟩

/-- **The far-end identity (T3) at the ties, Gale form.**  The ties `T` (the far ends of
`Q_bc` along `d b` tie) and `T'` (those of `Q_ab` tie) are `[b' a'] + [b' c] = 0` and
`[b' c'] + [b' a] = 0`; the two sums add up to `κ_b`. -/
theorem type08_tie_sums {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (ha' : galeD G.l G.m b' a' ≠ 0)
    (hc' : galeD G.l G.m b' c' ≠ 0) :
    (F.abc'.f a' = F.abc'.f c ↔ galeD G.l G.m b' a' + galeD G.l G.m b' c = 0) ∧
    (F.a'bc.f c' = F.a'bc.f a ↔ galeD G.l G.m b' c' + galeD G.l G.m b' a = 0) ∧
    galeD G.l G.m b' a' + galeD G.l G.m b' c + (galeD G.l G.m b' c' + galeD G.l G.m b' a) =
      galeD G.l G.m b b' := by
  refine ⟨facet_eq_iff_of_dep (G.hl.galeD G.hm b').swap₁.perm₂₃ (F.swap₁.perm₂₃).a'b'c
      (by simp) (F.swap₁.perm₂₃).nodup (galeD_self _ _ b') ha',
    facet_eq_iff_of_dep (G.hl.galeD G.hm b').perm₂₃.perm₁₂.swap₁ (F.perm₂₃.perm₁₂.swap₁).a'b'c
      (by simp) (F.perm₂₃.perm₁₂.swap₁).nodup (galeD_self _ _ b') hc', ?_⟩
  have hsum := galeD_sum G.hl G.hm b'
  rw [galeD_self, galeD_anti G.l G.m b b'] at hsum
  linarith

/-- At the tie `T`, the far end of `Q_ab` along `d b` is `c'` (`κ_b > 0`). -/
theorem type08_T_far {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hT : F.abc'.f a' = F.abc'.f c) : F.a'bc.f c' < F.a'bc.f a := by
  obtain ⟨-, ga', -, gc'⟩ := type08_b'_signs F G hκb.ne' hκc hU
  obtain ⟨e1, -, e3⟩ := type08_tie_sums F G ga'.ne' gc'.ne
  have h1 := e1.mp hT
  exact (far_end_Qab_iff' F G gc'.ne).mpr (mul_neg_of_neg_of_pos gc' (by linarith))

/-- At the tie `T'`, the far end of `Q_bc` along `d b` is `c` (`κ_b > 0`, not also `T`). -/
theorem type08_T'_far {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hT' : F.a'bc.f c' = F.a'bc.f a)
    (hT : F.abc'.f a' ≠ F.abc'.f c) : F.abc'.f c < F.abc'.f a' := by
  obtain ⟨-, ga', -, gc'⟩ := type08_b'_signs F G hκb.ne' hκc hU
  obtain ⟨-, e2, e3⟩ := type08_tie_sums F G ga'.ne' gc'.ne
  have h2 := e2.mp hT'
  refine lt_of_le_of_ne (not_lt.mp fun h => ?_) (Ne.symm hT)
  have := (far_end_Qbc_iff' F G ga'.ne').mp h
  nlinarith

/-- The tie `T` in the frame: `c − a' ∥ b − d`. -/
theorem IsCap.tieT_geom {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (hT : F.abc'.f a' = F.abc'.f c) : ∃ r : ℝ, c - a' = r • (b - d) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFc := F.abc'.neg c (by simp) (Ne.symm hnd.1.2.2.2.1) (Ne.symm hnd.2.2.1.2.1) hnd.2.2.2.2.1
  obtain ⟨-, -, -, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have : F.abc'.f a' / F.abc'.f c = 1 := by rw [hT, div_self hFc.ne]
  rw [this, one_smul] at ha'
  generalize F.ab'c.f a' / F.ab'c.f b = k at ha'
  exact ⟨-k, by rw [ha']; module⟩

/-- The tie `T'` in the frame: `c' − a ∥ b − d`. -/
theorem IsCap.tieT'_geom {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (hT' : F.a'bc.f c' = F.a'bc.f a) : ∃ r : ℝ, c' - a = r • (b - d) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFa := F.a'bc.neg a (by simp) hnd.1.1 hnd.1.2.1 hnd.1.2.2.2.1
  obtain ⟨-, -, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  have : F.a'bc.f c' / F.a'bc.f a = 1 := by rw [hT', div_self hFa.ne]
  rw [this, one_smul] at hc'
  generalize F.ab'c.f c' / F.ab'c.f b = k at hc'
  exact ⟨k, by rw [hc']; module⟩

/-- The signs of `β − 1` and `α − 1` as determinants (which of `a'`, `a` is hidden at the
ties). -/
theorem tie_beta_dets {a b b' c d : ℝ³} {α β : ℝ} (hb' : b' = d + α • (a - d) + β • (c - d)) :
    det3 (a - d) (b' - c) (b - d) = (β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c - d) (b - d) = (α - 1) * det3 (a - d) (c - d) (b - d) := by
  subst hb'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> ring

theorem sub_one_pos_of_det {E X γ : ℝ} (hX : X = (γ - 1) * E) (h : 0 < X * E) : 1 < γ := by
  rw [hX, mul_assoc] at h
  have hE : 0 < E * E := by
    rcases eq_or_ne E 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero] at h; exact absurd h (lt_irrefl _)
    · exact mul_self_pos.mpr h0
  linarith [(mul_pos_iff_of_pos_right hE).mp h]

theorem sub_one_neg_of_det {E X γ : ℝ} (hX : X = (γ - 1) * E) (h : X * E < 0) : γ < 1 := by
  rw [hX, mul_assoc] at h
  have hE : 0 < E * E := by
    rcases eq_or_ne E 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero] at h; exact absurd h (lt_irrefl _)
    · exact mul_self_pos.mpr h0
  have : γ - 1 < 0 := by
    by_contra hc; push Not at hc; nlinarith
  linarith

/-- **The genericity of Theorem 10.1′ (Lean form) in one labelling.**  What the proof
uses at the views along `d b` and `a' c` when `(a, b, c)` is the labelling of Lemma 6
(depths `z = ⟪·, b − d⟫`, `E = det3 (a − d) (c − d) (b − d)`):
* `tieTT'`: not both far-end ties `T` (`a' c ∥ d b`) and `T'` (`a c' ∥ d b`)
  (codimension 2);
* `routeT`, `routeT'` (Lemma X): at `T` one of the routes R1 (`K_b` has no weak saddle,
  slide along `Q_bc`), R2′ (`K_d` has none and `a'` is hidden, `β > 1`, slide along
  `Q_ab`), R2″ (the rim `d a c' b' a'` along `Q_bc`), R2′ with `a'` poking out (`β < 1`,
  the rim `d c' b' a' c` along `Q_ab`) applies; at `T'` one of R3 (`K_d`, `Q_ab`), R4′
  (`K_b` and `a` hidden, `α > 1`, `Q_bc`), R4″ (`b a b' c a'`, `Q_ab`), R4′ with `a` poking
  out (`α < 1`, `b c' a b' c`, `Q_bc`).  The addendum shows that one applies off
  codimension 2; here the case analysis is the hypothesis;
* `touchN2`, `touchT4`, `levelQ`: no triple tie of the far ends with `y'` at the views
  along `a' c` (case N2) and `d b` (case T4), and `b − d` not normal to `Q_ac` (case Q),
  all codimension 2;
* the slides of Lemma C (`NoBadNormal` along a face circle): for `K_c` (N2) along `Q_bc`,
  for `K_{a'}` (N2) along `Q_bc` or `a'b'c`, for `K_d` (Q) along `Q_ab` or `Q_bc`, for `K_b`
  (T4) along `Q_bc`, for `K_d` (T4) along `Q_ab`; for the three closings with one circle,
  alternatively Lemma H's five-corner rim along the other face (strictly unimodal and
  `NoBadNormal`), and for `K_c` (N2) and `K_b` (T4) also the two-peaked five-corner rim
  of `R_d` (`RdCond`: the far edge parallel to the realizing face, a horizontal double
  normal perpendicular to it crossing transversally, distinct depths, not unimodal;
  Lemma R0 and Theorem R, `Type08R0.lean`).  The two-circle alternatives fail in
  codimension 2; the one-circle ones on the class H1 of the addendum where also the
  five-corner rim is neither strictly unimodal nor in `R_d` (type (c) of Lemma H with a
  two-peaked rim, the depth-separated case not formalized; `R_d` for `K_d` (T4) is empty on
  paper), and in codimension 2;
* `flatN2`, `flatT4` (Lemma K): if the equator `b c b' c'` of `A` is planar, no
  quadruple tie `z b = z b'`, `z c = z c'` at the views along `a' c` and `d b`. -/
structure Type08Gen (a a' b b' c c' d : ℝ³) : Prop where
  tieTT' : ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∧ ∃ r : ℝ, c' - a = r • (b - d))
  routeT : (∃ r : ℝ, c - a' = r • (b - d)) →
    (NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
      NoBadNormal (quad b c' b' c) (b - d) (c - d)) ∨
    (NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
      0 < det3 (a - d) (b' - c) (b - d) * det3 (a - d) (c - d) (b - d) ∧
      NoBadNormal (quad d c' b' c) (b - d) (a - d)) ∨
    (StrictUnimodal (fun i => ⟪quint d a c' b' a' i, b - d⟫) ∧
      NoBadNormal (quint d a c' b' a') (b - d) (c - d)) ∨
    (StrictUnimodal (fun i => ⟪quint d c' b' a' c i, b - d⟫) ∧
      det3 (a - d) (b' - c) (b - d) * det3 (a - d) (c - d) (b - d) < 0 ∧
      NoBadNormal (quint d c' b' a' c) (b - d) (a - d))
  routeT' : (∃ r : ℝ, c' - a = r • (b - d)) →
    (NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
      NoBadNormal (quad d c' b' c) (b - d) (a - d)) ∨
    (NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
      0 < det3 (b' - a) (c - d) (b - d) * det3 (a - d) (c - d) (b - d) ∧
      NoBadNormal (quad b c' b' c) (b - d) (c - d)) ∨
    (StrictUnimodal (fun i => ⟪quint b a b' c a' i, b - d⟫) ∧
      NoBadNormal (quint b a b' c a') (b - d) (a - d)) ∨
    (StrictUnimodal (fun i => ⟪quint b c' a b' c i, b - d⟫) ∧
      det3 (b' - a) (c - d) (b - d) * det3 (a - d) (c - d) (b - d) < 0 ∧
      NoBadNormal (quint b c' a b' c) (b - d) (c - d))
  touchN2 : ¬ (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
  touchT4 : ¬ (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
  levelQ : ⟪a - d, b - d⟫ ≠ 0 ∨ ⟪c - d, b - d⟫ ≠ 0
  slideN2c : NoBadNormal (quad c b c' b') (c - a') (b - c) ∨
    (StrictUnimodal (fun i => ⟪quint c d b c' b' i, c - a'⟫) ∧
      NoBadNormal (quint c d b c' b') (c - a') (b' - c)) ∨
    RdCond c d b c' b' a'
  slideN2a' : NoBadNormal (quad a' b c' b') (c - a') (b - a') ∨
    NoBadNormal (quad a' b c' b') (c - a') (b' - a')
  slideQ : NoBadNormal (quad d a b' c) (b - d) (a - d) ∨
    NoBadNormal (quad d a b' c) (b - d) (c - d)
  slideT4b : NoBadNormal (quad b c' b' c) (b - d) (c - d) ∨
    (StrictUnimodal (fun i => ⟪quint b c' b' c a' i, b - d⟫) ∧
      NoBadNormal (quint b c' b' c a') (b - d) (a - d)) ∨
    RdCond b a' c b' c' d
  slideT4d : NoBadNormal (quad d c' b' c) (b - d) (a - d) ∨
    (StrictUnimodal (fun i => ⟪quint d a c' b' c i, b - d⟫) ∧
      NoBadNormal (quint d a c' b' c) (b - d) (c - d))
  flatN2 : det3 (c - b) (b' - b) (c' - b) = 0 →
    ¬ (⟪b, c - a'⟫ = ⟪b', c - a'⟫ ∧ ⟪c, c - a'⟫ = ⟪c', c - a'⟫)
  flatT4 : det3 (c - b) (b' - b) (c' - b) = 0 →
    ¬ (⟪b, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ = ⟪c', b - d⟫)

/-- `Type08Gen` in all six labellings (the `S3` symmetry of type 08 permutes the pairs). -/
def Type08GenAll (a a' b b' c c' d : ℝ³) : Prop :=
  Type08Gen a a' b b' c c' d ∧ Type08Gen b b' a a' c c' d ∧ Type08Gen a a' c c' b b' d ∧
    Type08Gen c c' a a' b b' d ∧ Type08Gen b b' c c' a a' d ∧ Type08Gen c c' b b' a a' d

/-- **Theorem 10.1 by slides, the case analysis.**  Given the two inputs that Theorem
10.1 takes from the Gale diagram (in the labelling of Lemma 6): in case N2 (the far end
of `Q_bc` along `d b` is `a'`) the edge `a' → c` of `O` is a quad edge (`a` hidden) that
is not bad (Lemma 7), and in case T4 (far ends `c'`, `c`) the edge `d → b` is not bad
(Lemmas 9.7, 4, 3), and the sides of (H4) in Lemma R0 (weakly: `b'`, `a'` on one side of
the plane `c b c'`; `a'`, `c'` on opposite sides of the plane `b c b'`), a type-08 point set
satisfying `Type08Gen` is Rupert. -/
theorem isRupert_type08_slide_core {a a' b b' c c' d : ℝ³}
    (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hN2 : F.abc'.f a' < F.abc'.f c → F.ab'c'.f a' < F.ab'c'.f c ∧
      ¬ max ⟪c, c - a'⟫ ⟪c', c - a'⟫ ≤ min ⟪b, c - a'⟫ ⟪b', c - a'⟫)
    (hT4 : F.abc'.f c < F.abc'.f a' → F.a'bc.f c' < F.a'bc.f a →
      ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hT_far : F.abc'.f a' = F.abc'.f c → F.a'bc.f c' < F.a'bc.f a)
    (hT'_far : F.a'bc.f c' = F.a'bc.f a → F.abc'.f a' ≠ F.abc'.f c → F.abc'.f c < F.abc'.f a')
    (hsideN2 : 0 ≤ det3 (b - c) (c' - c) (b' - c) * det3 (b - c) (c' - c) (a' - c))
    (hsideT4 : det3 (c - b) (b' - b) (a' - b) * det3 (c - b) (b' - b) (c' - b) ≤ 0)
    (hgen : Type08Gen a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hnd7 : [d, a, a', b, b', c, c'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
      ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', not_false⟩
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  -- the coordinates in the frame `d; a, c, b`
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hE := hd.det_Qac_ne
  obtain ⟨B1, B2⟩ := tie_beta_dets (a := a) (b := b) (d := d) hb'
  by_cases htie₁ : F.abc'.f a' = F.abc'.f c
  · -- the tie `T` (Lemma X): `β₂ = 1`, and the far end of `Q_ab` is `c'`
    have hfc' := hT_far htie₁
    have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
    have hβ₂eq : F.abc'.f a' / F.abc'.f c = 1 := by rw [htie₁, div_self hFc.ne]
    have ha'1 := ha'
    rw [hβ₂eq, one_smul] at ha'1
    have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂eq.le
    rcases hgen.routeT (hd.tieT_geom htie₁) with ⟨hN, hs⟩ | ⟨hN', hβ1, hs⟩ | ⟨hu5, hs5⟩ |
      ⟨hu5, hβ1, hs5⟩
    · exact isRupert_kb_four hb' hc' ha' hnd7 hE hα hβ hαβ hα₁1.le
        (fun h => absurd h hα₁1.ne') hβ₁ hα₂ hβ₂ hβ₂eq.le hαβ₂ hκ hN hs
    · exact isRupert_kd_four hb' hc' ha' hnd7 hE hα hβ hα₁1.le hβ₁ hα₂ hβ₂ hβ₂eq.le
        (fun _ => sub_one_pos_of_det B1 hβ1) hκ hN' hs
    · exact isRupert_r2pp hb' hc' ha'1 hnd7 hE hα hβ hαβ hα₁1 hβ₁ hα₂ hκ hu5 hs5
    · exact isRupert_r2p hb' hc' ha'1 hnd7 hE hα hβ (sub_one_neg_of_det B1 hβ1) hα₁1.le hβ₁ hα₂
        hκ hu5 hs5
  by_cases htie₂ : F.a'bc.f c' = F.a'bc.f a
  · -- the tie `T'` (Lemma X): `α₁ = 1`, and the far end of `Q_bc` is `c`
    have hfc := hT'_far htie₂ htie₁
    have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    have hα₁eq : F.a'bc.f c' / F.a'bc.f a = 1 := by rw [htie₂, div_self hFa.ne]
    have hc'1 := hc'
    rw [hα₁eq, one_smul] at hc'1
    have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
    rcases hgen.routeT' (hd.tieT'_geom htie₂) with ⟨hN', hs⟩ | ⟨hN, hα1, hs⟩ | ⟨hu5, hs5⟩ |
      ⟨hu5, hα1, hs5⟩
    · exact isRupert_kd_four hb' hc' ha' hnd7 hE hα hβ hα₁eq.symm.le hβ₁ hα₂ hβ₂ hβ₂1.le
        (fun h => absurd h hβ₂1.ne) hκ hN' hs
    · exact isRupert_kb_four hb' hc' ha' hnd7 hE hα hβ hαβ hα₁eq.symm.le
        (fun _ => sub_one_pos_of_det B2 hα1) hβ₁ hα₂ hβ₂ hβ₂1.le hαβ₂ hκ hN hs
    · exact isRupert_r4pp hb' hc'1 ha' hnd7 hE hα hβ hαβ hβ₁ hβ₂ hβ₂1 hαβ₂ hu5 hs5
    · exact isRupert_r4p hb' hc'1 ha' hnd7 hE hα (sub_one_neg_of_det B2 hα1) hβ hαβ hβ₁ hα₂ hβ₂
        hβ₂1 hαβ₂ hu5 hs5
  rcases lt_or_gt_of_ne htie₁ with hfar | hfc
  · -- case N2: the quad edge `a' → c` of `O`, with the cap `d` a middle of `Q_bc`
    obtain ⟨hq₂, hgood⟩ := hN2 hfar
    obtain ⟨s, δ, hs0, hs1, hδ, hdmid⟩ := hd.middle_Qbc hfar
    have e : (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} :=
      (type08_set_perm a a' b b' c c' d).1
    rw [← e]
    rcases hgen.slideN2c with hs | hs | hR
    · exact isRupert_quad_edge_middle_slide (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ hgen.touchN2 (Or.inl hs)
        hgen.slideN2a'
    · exact isRupert_quad_edge_middle_slide (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ hgen.touchN2 (Or.inr hs)
        hgen.slideN2a'
    · -- `R_d` (A.10): if `K_{a'}` has no weak saddle, slide it; otherwise Lemma R0 and the
      -- two-peaked five-corner rim along `a'b'c`
      by_cases hNx : NWS4 (quad ⟪a', c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫)
      · exact isRupert_quad_edge_middle_sel (m := d) F.swap₁.perm₂₃ hfar hq₂
          ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩
          (Or.inr ⟨hNx, hgen.slideN2a'⟩)
      have hNy : NWS4 (quad ⟪c, c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫) := by
        by_contra hN
        exact hNx (nws4_closing_oct F.swap₁.perm₂₃ hfar hq₂ hN hgood hgen.touchN2)
      exact isRupert_quad_edge_middle_rdCond F.swap₁.perm₂₃ hfar hq₂ ⟨s, δ, hs0, hs1, hδ, hdmid⟩
        ⟨F.abc'.f, F.abc'.N, F.abc'.hN, hd.abc', F.abc'.hQ, F.abc'.hR,
          F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc',
          F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'⟩
        hsideN2 hNy hNx hR
  · have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    by_cases hfa : F.a'bc.f a < F.a'bc.f c'
    · -- case Q: the far ends are `a` and `c`
      have hα₁1 : F.a'bc.f c' / F.a'bc.f a < 1 := (div_lt_one_of_neg hFa).mpr hfa
      exact isRupert_q_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁ hα₁1 hβ₁ hα₂ hβ₂
        hβ₂1 hgen.levelQ hgen.slideQ
    · -- case T4: the far ends are `c'` and `c`
      have hfc' : F.a'bc.f c' < F.a'bc.f a := lt_of_le_of_ne (not_lt.mp hfa) htie₂
      have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
      have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
      have hgood := hT4 hfc hfc'
      rcases hgen.slideT4b with hs | hs | hR
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood hgen.touchT4 (Or.inl hs) hgen.slideT4d
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood hgen.touchT4 (Or.inr hs) hgen.slideT4d
      · -- `R_d` (A.10): if `K_d` has no weak saddle, slide it; otherwise Lemma R0 and the
        -- two-peaked five-corner rim along `Q_ab`
        by_cases hNd : NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
        · rcases hgen.slideT4d with hs | ⟨hu5, hs5⟩
          · exact isRupert_t4_sel hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hαβ₂ hκ (Or.inr ⟨hNd, hs⟩)
          · exact isRupert_t4d_five hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hκ hu5 hs5
        have hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
          by_contra hN
          exact hNd (t4_closing hb' hc' ha' hdb hd.det_Qac_ne hα hβ hα₁1 hβ₁ hκ hgood
            hgen.touchT4 hN)
        exact isRupert_t4b_rdCond hb' hc' ha' hdb hd.det_Qac_ne hα hβ hα₁1 hβ₁ hβ₂ hβ₂1 hαβ₂ hκ
          ⟨F.a'b'c.f, F.a'b'c.N, F.a'b'c.hN, F.a'b'c.hP, F.a'b'c.hR, F.a'b'c.hQ,
            F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc,
            F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')⟩
          hsideT4 hNb hNd hR

/-- The planes `d b b'` separate `c` from `c'` (`b'` is a corner of the T4 view). -/
theorem IsCap.t4_opp {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    det3 (b - d) (b' - d) (c - d) * det3 (b - d) (b' - d) (c' - d) < 0 := by
  obtain ⟨hα, hβ, -, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, -, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, D23, D24⟩ :=
    t4_dets hb' hc'
  rw [D23, D24]
  have := mul_self_pos.mpr hd.det_Qac_ne
  have := mul_pos (mul_pos hα hα₁) hβ
  nlinarith

/-- **Theorem 10.1 by slides, normalized.**  In the labelling of Lemma 6 (`κ_a, κ_b > 0`,
`[b c] < 0`), a type-08 point set satisfying `Type08Gen` is Rupert.  No distinct
depths, no general position and no exclusion of horizontal double normals at the edge
views are assumed. -/
theorem isRupert_type08_slide_normalized {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0)
    (hgen : Type08Gen a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨-, -, -, -, -, -, -, ha'b, ha'b', -, -, -, -, hac, hac'⟩ :=
    type08_signs F G hκa hκb hκc hU
  have hsides := type08_rd_sides h G hκa ha'b ha'b' hac hac'
  exact isRupert_type08_slide_core F hd (fun hfar => type08_lemma7 F G hκa hκb hκc hU hfar)
    (fun _ _ => type08_t4_not_bad h F hd G hκa hκb hκc hU hd.t4_opp)
    (type08_T_far F G hκb hκc hU) (type08_T'_far F G hκb hκc hU) hsides.1.le hsides.2.le hgen

/-- **Theorem 10.1′ (type 08), Gale form**: as `isRupert_type08_slide`, with `κ ≠ 0` for the
three pairs of `O` in place of the planar-equator determinants. -/
theorem isRupert_type08_slide_gale {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) (G : GaleData a a' b b' c c') (hκa : galeD G.l G.m a a' ≠ 0)
    (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hgen : Type08GenAll a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have h := F.isOctahedron
  obtain ⟨-, -, hA⟩ := pole_signs F (G.hl.galeD G.hm a) (galeD_self _ _ a) hκa
  obtain ⟨-, -, hB⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm b).perm₁₂ (galeD_self _ _ b) hκb
  obtain ⟨-, -, hC⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ c) hκc
  obtain ⟨σ, hσ, hcases⟩ := type08_lemma6 hκa hκb hκc hA hB hC
  obtain ⟨G', hG'⟩ : ∃ G' : GaleData a a' b b' c c',
      ∀ s t, galeD G'.l G'.m s t = σ * galeD G.l G.m s t := by
    rcases hσ with rfl | rfl
    · exact ⟨G, fun s t => (one_mul _).symm⟩
    · exact ⟨G.mirror, fun s t => by rw [G.galeD_mirror]; ring⟩
  have hne : ∀ s t, galeD G.l G.m s t ≠ 0 → galeD G'.l G'.m s t ≠ 0 := by
    intro s t hst; rw [hG']; rcases hσ with rfl | rfl <;> simpa using hst
  have hpos : ∀ s t, 0 < σ * galeD G.l G.m s t → 0 < galeD G'.l G'.m s t := by
    intro s t h; rwa [hG']
  have hneg : ∀ s t, σ * galeD G.l G.m s t < 0 → galeD G'.l G'.m s t < 0 := by
    intro s t h; rwa [hG']
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen
  have e := type08_set_perm a a' b b' c c' d
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact isRupert_type08_slide_normalized h F hd G' (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκc)
      (hneg _ _ h3) g1
  · rw [← e.2.1]
    exact isRupert_type08_slide_normalized h.perm₁₂ F.perm₁₂ hd.perm₁₂ G'.perm₁₂ (hpos _ _ h1)
      (hpos _ _ h2) (hne _ _ hκc) (hneg _ _ h3) g2
  · rw [← e.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₂₃ F.perm₂₃ hd.perm₂₃ G'.perm₂₃ (hpos _ _ h1)
      (hpos _ _ h2) (hne _ _ hκb) (hneg _ _ h3) g3
  · rw [← e.2.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₂₃.perm₁₂ F.perm₂₃.perm₁₂ hd.perm₂₃.perm₁₂
      G'.perm₂₃.perm₁₂ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκb) (hneg _ _ h3) g4
  · rw [← e.2.2.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₁₂.perm₂₃ F.perm₁₂.perm₂₃ hd.perm₁₂.perm₂₃
      G'.perm₁₂.perm₂₃ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκa) (hneg _ _ h3) g5
  · rw [← e.2.2.2.2.2]
    exact isRupert_type08_slide_normalized h.perm₁₂.perm₂₃.perm₁₂ F.perm₁₂.perm₂₃.perm₁₂
      hd.perm₁₂.perm₂₃.perm₁₂ G'.perm₁₂.perm₂₃.perm₁₂ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκa)
      (hneg _ _ h3) g6

/-- **Theorem 10.1′ (type 08), Lean form: no general position, no exclusion of
horizontal double normals at the edge views.**  An octahedron `O` with opposite pairs
`(a, a')`, `(b, b')`, `(c, c')` and a cap `d` (`IsCap`; type 08) is Rupert, provided `O`
has no planar equator and `Type08Gen` holds in each of the six labellings
(`Type08GenAll`): no far-end tie `T`, `T'`, no touching (codimension 2), and the slides
of Lemma C along the face circles at the named crossings meet depth ties and
horizontal double normals only at isolated views (`NoBadNormal`). -/
theorem isRupert_type08_slide {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d)
    (heqA : det3 (c - b) (b' - b) (c' - b) ≠ 0) (heqB : det3 (c - a) (a' - a) (c' - a) ≠ 0)
    (heqC : det3 (b - a) (a' - a) (b' - a) ≠ 0)
    (hgen : Type08GenAll a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨G⟩ := F.nonempty_galeData
  exact isRupert_type08_slide_gale F hd G (fun h0 => heqA (G.planar_of_kappa h0))
    (fun h0 => heqB (G.perm₁₂.planar_of_kappa h0))
    (fun h0 => heqC (G.perm₂₃.perm₁₂.planar_of_kappa h0)) hgen


/-- **Theorem 10.1′, facet form (type 08).**  Seven points labelled as type 08
(`typeb_lib.load('08-7f')`: the quadrilaterals `0123`, `0245`, `2356` and the triangles
`014`, `136`, `146`, `456` are facets), with no planar equator of the octahedron
`x 0, …, x 6` without `x 2` and `Type08GenAll` for its pairs `(0, 6)`, `(3, 4)`, `(5, 1)`
and the cap `x 2`, are Rupert. -/
theorem isRupert_type08_slide_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    (heq₁ : det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) ≠ 0)
    (heq₂ : det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) ≠ 0)
    (heq₃ : det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) ≠ 0)
    (hgen : Type08GenAll (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2)) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact isRupert_type08_slide F hcap heq₁ heq₂ heq₃ hgen

end Minimality

end
