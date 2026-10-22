module

public import Minimality.Type21O2

@[expose] public section

/-!
# Type 21, the other Gale classes (`FEWER-FACES-PROOFS.md` §16 addendum)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`.  The normal
form of the addendum: `K − 2` has the pattern `(+, −, +)` (`CrossNorm G` with `[4 5] > 0`).
With `τ` as in `IsCap21.tau`, `r = β + τ [1 6]`, the brackets of `K − 6` that decide the classes
are `{5 4} = r [5 4] + τ [4 1] [5 6]` (`< 0`: `2` not beyond `013`) and
`{0 3} = r [0 3] + τ [1 3] [6 0]` (`< 0`: `2` not beyond `145`).

* **Lemma 16.16 for `K − 2`** — `type21_O_quad36`: if tier Q fails for `K − 2`, the admissible
  pair is `W = {4, 5}` and `3 → 6`, `1 → 0` are quad edges.
* **Theorem 16.18 (class (a), no crossing)** — `cert_type21_classA`: `Q` at `23` of
  `K − 6`; `2` stays in the box of the `01`-view (the identities
  `c ([4 6] − [3 4]) − [4 5]([1 0] − [5 1]) [3 4] = ([0 5] − [5 1]) [4 6] [4 1]` and
  `c ([5 6] − [3 5]) − [4 5] k = ([0 5] − [5 1]) [5 6] [4 1]`, `c` the speed of `{4 5}`).
* **Theorem 16.20 (class (b), `2` beyond `145`)** — `cert_type21_classB`: `Q` at `05`, `Q` at
  `34` of `K − 6`, or R at the ridge `26` (the plane `145` separates `2` from `6`,
  `type21_plane145`).
* **Lemma 16.21 (near or A1)** — `type21_near_or_A1`; `f ≠ 0` from a non-parallel segment
  (`gale_f_ne`); the pair brackets of `K − 6` (`type21_galeO2_kappa`); **Lemma 16.22**
  (`type21_O2_quad04`); F1 in facet form (`cert_type21_F1'`).  Theorem 16.23 (class (c)) is
  `cert_type21_classC` in `Type21F2Case.lean`.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- **Lemma 16.16 for `K − 2` in the pattern `(+, −, +)`**: if no K-quad edge of `K − 2` is an
E-good quad edge (tier Q fails), then by Lemma 9.8 the admissible pair is `{4, 5}`, and
`3 → 6`, `1 → 0` are quad edges. -/
theorem type21_O_quad36 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hN : CrossNorm G) (h45 : 0 < galeD G.l G.m b b')
    (hf : ¬(G.l a' + G.l b + G.l c' = 0 ∧ G.m a' + G.m b + G.m c' = 0))
    (hQ : ¬ Type21Q G.l G.m a a' b b' c c') :
    EGoodQuad G.l G.m a' a c' b b' ∧ EGoodQuad G.l G.m c c' a b b' := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have anti := galeD_anti G.l G.m
  rcases arc_step1 F.swap₁.swap₃ G.swap₁.swap₃ hN.h30 h45 hN.h61 hf with ⟨h1, -⟩ | ⟨-, h2⟩ |
    ⟨h3, -⟩
  · exfalso
    obtain ⟨-, ⟨q1, q2, -⟩⟩ := h1 s63
    exact hQ (Or.inl ⟨q2, q1, mul_pos hN.h30 hN.h35⟩)
  · exact h2 (show galeD G.l G.m b a' < 0 by rw [anti]; linarith)
  · exfalso
    obtain ⟨⟨q1, q2, q3⟩, -⟩ := h3 s34
    refine hQ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q2, q1, ?_⟩)))))))
    rw [anti c' c, anti b c]; nlinarith [hN.h61]

/-! ### Class (a): no crossing (Theorem 16.18) -/

theorem type21_id_a1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m c a' * galeD l m b b' + galeD l m b c * (galeD l m b' c' - galeD l m b b')) *
      (galeD l m b c' - galeD l m a' b) - galeD l m b b' * (galeD l m c a - galeD l m b' c) *
      galeD l m a' b = (galeD l m a b' - galeD l m b' c) * galeD l m b c' * galeD l m b c := by
  type21_ring hl hm

theorem type21_id_a2 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m c a' * galeD l m b b' + galeD l m b c * (galeD l m b' c' - galeD l m b b')) *
      (galeD l m b' c' - galeD l m a' b') - galeD l m b b' * (galeD l m a' b' * galeD l m c a +
      galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) = (galeD l m a b' - galeD l m b' c) *
      galeD l m b' c' * galeD l m b c := by
  type21_ring hl hm

theorem type21_id_s5 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m b' c' - galeD l m b b' = galeD l m a b' - galeD l m b' c + galeD l m a' b' := by
  type21_ring hl hm

/-- **Theorem 16.18 (class (a))**, in `τ`: `K − 2` in the pattern `(+, −, +)`, `3 → 6` and
`1 → 0` quad edges (Lemma 16.16), `2` beyond neither `013` (`{5 4} < 0`) nor `145`
(`{0 3} < 0`).  Then `0` is hidden along `3 → 2` in `K − 6` (`2` stays in the box of the
`01`-view: H1 and H2 hold, interpolating between `τ = 0` and the crossing time `[4 5]/c` of
`013`), `3 → 2` is E-good (`{0 3} [0 6] > 0`), and `K` has a rim certificate (`CertV`) (`Q` at `23`). -/
theorem cert_type21_classA {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (h45 : 0 < galeD G.l G.m b b') {α β τ : ℝ} (hτ : 0 < τ)
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hq36 : EGoodQuad G.l G.m a' a c' b b') (hq10 : EGoodQuad G.l G.m c c' a b b')
    (hn013 : (β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
      τ * galeD G.l G.m b c * galeD G.l G.m b' c' < 0)
    (hn145 : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have anti := galeD_anti G.l G.m
  have a1 := type21_id_a1 G.hl G.hm
  have a2 := type21_id_a2 G.hl G.hm
  have i5 := type21_id_s5 G.hl G.hm
  have s1 := type21_id_s1 G.hl G.hm
  obtain ⟨q1, q2, -⟩ := hq36
  obtain ⟨q3, q4, -⟩ := hq10
  rw [anti a' b] at q1
  rw [anti a' b'] at q2
  rw [anti a b] at q3
  rw [anti a b'] at q4
  have e61 : galeD G.l G.m c c' = -galeD G.l G.m c' c := anti c' c
  have e54 : galeD G.l G.m b' b = -galeD G.l G.m b b' := anti b b'
  set x45 := galeD G.l G.m b b'; set x34 := galeD G.l G.m a' b; set x35 := galeD G.l G.m a' b'
  set x46 := galeD G.l G.m b c'; set x56 := galeD G.l G.m b' c'; set x41 := galeD G.l G.m b c
  set x04 := galeD G.l G.m a b; set x51 := galeD G.l G.m b' c; set x05 := galeD G.l G.m a b'
  set x13 := galeD G.l G.m c a'; set x10 := galeD G.l G.m c a; set x63 := galeD G.l G.m c' a'
  -- the Gale facts of `3 → 6`, `1 → 0`
  have g1 : x34 < x46 := by
    have h : 0 < -x34 + x46 := by nlinarith
    linarith
  have g2 : x35 < x56 := by
    have h : 0 < -x35 + x56 := by nlinarith
    linarith
  have g4 : x51 < x05 := by
    have h : x51 + -x05 < 0 := by nlinarith
    linarith
  -- the crossing time of `013`
  have hβ : β = 1 + τ * (x10 - x51) := by linarith
  have hr : β + τ * galeD G.l G.m c c' = 1 + τ * (x41 - x13) := by
    rw [e61]; linear_combination ht - hα + τ * s1
  set cc := x13 * x45 + x41 * (x56 - x45) with hcc
  have hc0 : 0 < cc := by
    have : 0 < x56 - x45 := by rw [i5]; linarith [hN.h35]
    have := mul_pos s13 h45
    have := mul_pos s41 ‹0 < x56 - x45›
    linarith
  have hτc : τ * cc < x45 := by
    rw [hr, e54] at hn013
    have e : (1 + τ * (x41 - x13)) * -x45 + τ * x41 * x56 = τ * cc - x45 := by
      rw [hcc]; ring
    linarith
  have hgap : 0 < x45 - τ * cc := by linarith
  -- H1 and H2
  have hH1 : β * x34 < x46 := by
    have key : x45 * (x46 - β * x34) = (x45 - τ * cc) * (x46 - x34) +
        τ * ((x05 - x51) * x46 * x41) := by
      rw [hβ, ← a1, hcc]; ring
    have : 0 < x45 * (x46 - β * x34) := by
      rw [key]
      exact add_pos (mul_pos hgap (by linarith)) (mul_pos hτ (mul_pos (mul_pos (by linarith) s46)
        s41))
    have := pos_of_mul_pos_right this h45.le
    linarith
  have hH2 : α * x63 + β * x35 < x56 := by
    have key : x45 * (x56 - (α * x63 + β * x35)) = (x45 - τ * cc) * (x56 - x35) +
        τ * ((x05 - x51) * x56 * x41) := by
      rw [hβ, hα, ← a2, hcc]; ring
    have : 0 < x45 * (x56 - (α * x63 + β * x35)) := by
      rw [key]
      exact add_pos (mul_pos hgap (by linarith)) (mul_pos hτ (mul_pos (mul_pos (by linarith) s56)
        s41))
    have := pos_of_mul_pos_right this h45.le
    linarith
  exact cert_type21_step5 F hd G hN hco hα ht hH1 hH2 hn145 hgen

/-! ### Class (b): both crossed (Theorem 16.20) -/

theorem type21_id_P6 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c' c * galeD l m a' b = galeD l m b c' * galeD l m c a' - galeD l m c' a' *
      galeD l m b c := by
  type21_ring hl hm

theorem IsDep.neg {a a' b b' c c' : ℝ³} {L : ℝ³ → ℝ} (h : IsDep a a' b b' c c' L) :
    IsDep a a' b b' c c' (fun t => -L t) :=
  ⟨by linarith [h.sum], by rw [← neg_eq_zero, ← h.vsum]; module⟩

/-- The second form of the cap (§16.0): `2 = τ [1 3] 3 + τ [1 4] 4 + r 6`. -/
theorem IsCap21.rep2 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (_hd : IsCap21 F d)
    (G : GaleData a a' b b' c c') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) :
    d = (τ * galeD G.l G.m c a') • a' + (τ * galeD G.l G.m c b) • b +
      (β + τ * galeD G.l G.m c c') • c' := by
  have hs := galeD_sum G.hl G.hm c
  have hv := (G.hl.galeD G.hm c).vsum
  rw [galeD_self] at hs hv
  have hX : α + τ * galeD G.l G.m c b' = 0 := by
    rw [hα, galeD_anti G.l G.m c b']; ring
  rw [hco]
  linear_combination (norm := module) (-τ) • hv - ht • a + hX • b'

/-- `det(5 − 6, 4 − 6, 2 − 6) ≠ 0`: `4` is off the plane of `0256`. -/
theorem type21_ridge_T54 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) : det3 (b' - c') (b - c') (d - c') ≠ 0 := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  intro h0
  have hc : cross (b' - c') (d - c') ≠ 0 :=
    cross_ne_zero_of_affine (g := fun x => -F.a'b'c'.f x) (N := -F.a'b'c'.N)
      (fun y z => by rw [inner_neg_left, ← F.a'b'c'.hN]; ring) (Ne.symm hb'c')
      (by simp [F.a'b'c'.hR]) (by simp [F.a'b'c'.hQ]) (by simp; exact hd.a'b'c')
  have := affine_zero_of_coplanar F.ab'c'.hN F.ab'c'.hR F.ab'c'.hQ hd.ab'c' hc (w := b) (by
    have e : det3 (b' - c') (d - c') (b - c') = -det3 (b' - c') (b - c') (d - c') := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, h0, neg_zero])
  linarith [F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc']

/-- **Theorem 16.20 (class (b))**, in `τ`: `K − 2` in the pattern `(+, −, +)`, `2` beyond `145`
(`{0 3} > 0`).  If `|[1 5]| > |[1 0]|` (the far end of `0256` on the ridge is `0`): `Q` at
`05` (`|[6 5]| > |[6 0]|` by (b1)).  Else if `|[1 4]| > |[1 3]|` (far end `3` of `2346`): `Q` at
`34` of `K − 6` (`|[6 4]| > |[6 3]|` by (b2), E-good since `{0 3}, {0 4} > 0`).  Else R at the
ridge `26` (far ends `(5, 4)`; `1` hidden, or Lemma E with the plane `145`, which separates
`2` from `6`). -/
theorem cert_type21_classB {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    {α β τ : ℝ} (hτ : 0 < τ)
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hc145 : (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a <
      τ * galeD G.l G.m c a' * galeD G.l G.m c' a)
    (t10 : galeD G.l G.m c a ≠ galeD G.l G.m b' c)
    (t13 : galeD G.l G.m b c ≠ galeD G.l G.m c a')
    (hRid : det3 (b - b') (c - b') (d - c') ≠ 0)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have anti := galeD_anti G.l G.m
  have P1 := type21_id_P1 G.hl G.hm
  have P6 := type21_id_P6 G.hl G.hm
  have s1 := type21_id_s1 G.hl G.hm
  have h61 := hN.h61
  have hr : β + τ * galeD G.l G.m c c' = 1 + τ * (galeD G.l G.m b c - galeD G.l G.m c a') := by
    rw [anti c' c]; linear_combination ht - hα + τ * s1
  obtain ⟨hrpos, hfd, -⟩ := type21_r_pos hd hN hco hα ht
  rcases lt_or_gt_of_ne t10 with h10 | h10
  · -- `f0 = 0`: `Q` at `05`
    have h56 : galeD G.l G.m c' a < galeD G.l G.m b' c' := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc s10.le
      have := mul_lt_mul_of_pos_left h10 s60
      linarith [mul_pos h61 s05, P1]
    refine cert_type21_Q F hd G hgen (Or.inl ⟨?_, ?_, mul_pos hN.h30 hN.h35⟩)
    · rw [anti b' c]; exact mul_neg_of_pos_of_neg s10 (by linarith)
    · rw [anti b' c']; exact mul_neg_of_pos_of_neg s60 (by linarith)
  -- `f0 = 5`
  -- the dependency `{0 ·}` of `K − 6` and the sign of `{0 4}`
  obtain ⟨L, hL, La, La', Lb', Lb, Lc, Ld⟩ := type21_depO2_a hd G hco hα ht
  have hLb' : 0 < L b' := by rw [Lb']; positivity
  have hLb : 0 < L b := by
    obtain ⟨p1, -, -⟩ := pole_signs' hd.O2.perm₁₂.swap₁ hL La hLb'.ne'
    exact pos_of_mul_pos_right p1 hLb'.le
  have hLa' : 0 < L a' := by rw [La', anti a' a]; linarith
  rcases lt_or_gt_of_ne t13 with h13 | h13
  · -- `f3 = 4`: the tier R
    have hβ1 : 1 < β := by
      have := mul_pos hτ (sub_pos.mpr h10); linarith
    have hr1 : β + τ * galeD G.l G.m c c' < 1 := by
      rw [hr]; have := mul_neg_of_pos_of_neg hτ (sub_neg.mpr h13); linarith
    obtain ⟨-, e2⟩ := type21_f015 F G hco
    have f6 := F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
    have f6' := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc')
    have eβ : F.ab'c.f d / F.ab'c.f c' = β := by rw [e2]; exact mul_div_cancel_right₀ _ f6.ne
    have eβ' : F.a'bc.f d / F.a'bc.f c' = β + τ * galeD G.l G.m c c' := by
      rw [hfd]; exact mul_div_cancel_right₀ _ f6'.ne
    refine cert_type21_R F hd hgen ?_
    unfold Type21R Type21RQ
    rw [eβ, eβ']
    refine Or.inr (Or.inl ⟨hβ1, hr1, ?_⟩)
    -- the plane `145` separates `2` from `6`
    set ψ : ℝ³ → ℝ := fun x => det3 (b - b') (c - b') (x - b') with hψ
    have hψN : ∀ y z, ψ y - ψ z = ⟪cross (b - b') (c - b'), y - z⟫ := by
      intro y z; simp only [ψ, det3, ← inner_sub_right]; congr 1; abel
    have ψb' : ψ b' = 0 := by simp only [ψ, sub_self, det3_expand, PiLp.zero_apply]; ring
    have ψb : ψ b = 0 := by simp only [ψ, det3_expand, PiLp.sub_apply]; ring
    have ψc : ψ c = 0 := by simp only [ψ, det3_expand, PiLp.sub_apply]; ring
    have rA := (G.hl.galeD G.hm a).apply hψN
    rw [ψb', ψb, ψc, galeD_self] at rA
    have hrep := hd.rep2 G hco hα ht
    have hw : τ * galeD G.l G.m c a' + τ * galeD G.l G.m c b + (β + τ * galeD G.l G.m c c') = 1
        := by rw [hr, anti b c]; ring
    have e : d - c' = (τ * galeD G.l G.m c a') • (a' - c') + (τ * galeD G.l G.m c b) • (b - c') := by
      rw [hrep]; linear_combination (norm := module) hw • c'
    have hψd : ψ d = ψ c' + τ * galeD G.l G.m c a' * (ψ a' - ψ c') +
        τ * galeD G.l G.m c b * (ψ b - ψ c') := by
      have k := hψN d c'
      rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right, ← hψN, ← hψN] at k
      linarith
    have hQ : det3 (b - b') (c' - b') (d - c') ≠ 0 := by
      have e : det3 (b - b') (c' - b') (d - c') = det3 (b' - c') (b - c') (d - c') := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact type21_ridge_T54 hd
    rcases lt_or_gt_of_ne (mul_ne_zero hRid hQ) with hneg | hpos
    · refine Or.inr ⟨hneg, ?_⟩
      change ψ c' * ψ d ≤ 0
      have key : galeD G.l G.m a a' * (ψ c' * ψ d) = ψ c' * ψ c' * L a' := by
        rw [La', hψd, ψb]
        rw [anti c' a] at rA
        linear_combination (ψ c' * τ * galeD G.l G.m c a') * rA - ψ c' * ψ c' *
          galeD G.l G.m a a' * hw
      by_contra hc
      push Not at hc
      have h1 : galeD G.l G.m a a' * (ψ c' * ψ d) < 0 :=
        mul_neg_of_neg_of_pos (by rw [anti a' a]; linarith [hN.h30]) hc
      rw [key] at h1
      exact absurd h1 (not_lt.mpr (mul_nonneg (mul_self_nonneg _) hLa'.le))
    · exact Or.inl hpos
  · -- `f3 = 3`: `Q` at `34` of `K − 6`
    have h63 : galeD G.l G.m c' a' < galeD G.l G.m b c' := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc s13.le
      have := mul_lt_mul_of_pos_left h13 s63
      linarith [mul_pos h61 s34, P6]
    have hq₁ : F.ab'c.f a' < F.ab'c.f b := by
      have r1 := (G.hl.galeD G.hm c').apply F.ab'c.hN
      rw [F.ab'c.hP, F.ab'c.hQ, F.ab'c.hR, galeD_self, anti b c'] at r1
      have f4 := F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc
      have : 0 < galeD G.l G.m c' a' * (F.ab'c.f b - F.ab'c.f a') := by
        have k : galeD G.l G.m c' a' * (F.ab'c.f b - F.ab'c.f a') =
            (galeD G.l G.m c' a' - galeD G.l G.m b c') * F.ab'c.f b := by linear_combination -r1
        rw [k]; exact mul_pos_of_neg_of_neg (by linarith) f4
      linarith [pos_of_mul_pos_right this s63.le]
    have hq₂ : F.ab'c'.f a' < F.ab'c'.f b := by
      have r1 := (G.hl.galeD G.hm c).apply F.ab'c'.hN
      rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, galeD_self, anti b c] at r1
      have f4 := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
      have : 0 < galeD G.l G.m c a' * (F.ab'c'.f b - F.ab'c'.f a') := by
        have k : galeD G.l G.m c a' * (F.ab'c'.f b - F.ab'c'.f a') =
            (galeD G.l G.m c a' - galeD G.l G.m b c) * F.ab'c'.f b := by linear_combination -r1
        rw [k]; exact mul_pos_of_neg_of_neg (by linarith) f4
      linarith [pos_of_mul_pos_right this s13.le]
    have hgood : ¬ max ⟪b, b - a'⟫ ⟪b', b - a'⟫ ≤ min ⟪c, b - a'⟫ ⟪d, b - a'⟫ := by
      refine not_bad_of_dep hL.swap₁.swap₂.neg ha'b (by simp only [La, neg_zero])
        (by linarith) (by linarith) (by linarith) ?_ ?_
      · rw [Lc, anti c a]; have := mul_pos hrpos s10; linarith
      · rw [Ld, anti c' a]; linarith
    rw [← type21_set_O2] at hgen ⊢
    exact (cert_type21_43 hd.O2 hd.sigma2 hq₁ hq₂ hgood hgen).monoE fun _ _ h => h.sigma2

/-! ### Class (c): one crossing (Theorem 16.23) -/

/-- **An affine function vanishing on the plane `145`**: `[3 0] g(0) + [3 6] g(6) = 0` (the
dependency `[3 ·]`) and `[0 3] g(2) = {0 3} g(6)` (the dependency `[0 ·]` and the second form of
the cap), with `{0 3} = r [0 3] + τ [1 3] [6 0]`. -/
theorem type21_plane145 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) {g : ℝ³ → ℝ} {N : ℝ³}
    (hg : ∀ y z, g y - g z = ⟪N, y - z⟫) (gb' : g b' = 0) (gb : g b = 0) (gc : g c = 0) :
    galeD G.l G.m a' a * g a + galeD G.l G.m a' c' * g c' = 0 ∧
    galeD G.l G.m a a' * g d = ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
      τ * galeD G.l G.m c a' * galeD G.l G.m c' a) * g c' := by
  have anti := galeD_anti G.l G.m
  have s1 := type21_id_s1 G.hl G.hm
  have r3 := (G.hl.galeD G.hm a').apply hg
  rw [gb', gb, gc, galeD_self] at r3
  have rA := (G.hl.galeD G.hm a).apply hg
  rw [gb', gb, gc, galeD_self] at rA
  refine ⟨by linear_combination r3, ?_⟩
  have hr : β + τ * galeD G.l G.m c c' = 1 + τ * (galeD G.l G.m b c - galeD G.l G.m c a') := by
    rw [anti c' c]; linear_combination ht - hα + τ * s1
  have hw : τ * galeD G.l G.m c a' + τ * galeD G.l G.m c b + (β + τ * galeD G.l G.m c c') = 1 := by
    rw [hr, anti b c]; ring
  have hrep := hd.rep2 G hco hα ht
  have e : d - c' = (τ * galeD G.l G.m c a') • (a' - c') + (τ * galeD G.l G.m c b) • (b - c') := by
    rw [hrep]; linear_combination (norm := module) hw • c'
  have hgd : g d = g c' + τ * galeD G.l G.m c a' * (g a' - g c') +
      τ * galeD G.l G.m c b * (g b - g c') := by
    have k := hg d c'
    rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right, ← hg, ← hg] at k
    linarith
  rw [hgd, gb]
  rw [anti c' a] at rA
  linear_combination (τ * galeD G.l G.m c a') * rA - galeD G.l G.m a a' * g c' * hw

/-- **Lemma 16.21 (near or A1)**: in the pattern `(+, −, +)` (`[3 0] > 0`), if `2` is not
beyond `145` (`{0 3} < 0`), then `δ_014(2) < δ_014(5)` or `δ_134(2) > δ_134(5)`.  The affine
function `G = f₁₃₄ · f₀₁₄(5) − f₀₁₄ · f₁₃₄(5)` vanishes on `145`, is positive at `0`, hence at `6`
and, as `145` is not crossed, at `2`; failure of both would make `G(2) ≤ 0`. -/
theorem type21_near_or_A1 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G) {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hn145 : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a) :
    F.abc.f b' < F.abc.f d ∨ F.a'bc.f d < F.a'bc.f b' := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have anti := galeD_anti G.l G.m
  set g : ℝ³ → ℝ := fun x => F.a'bc.f x * F.abc.f b' - F.abc.f x * F.a'bc.f b' with hg_def
  have hgN : ∀ y z, g y - g z = ⟪F.abc.f b' • F.a'bc.N - F.a'bc.f b' • F.abc.N, y - z⟫ := by
    intro y z
    simp only [g, inner_sub_left, real_inner_smul_left, ← F.a'bc.hN, ← F.abc.hN]; ring
  have gb' : g b' = 0 := by simp only [g]; ring
  have gb : g b = 0 := by simp only [g, F.a'bc.hQ, F.abc.hQ]; ring
  have gc : g c = 0 := by simp only [g, F.a'bc.hR, F.abc.hR]; ring
  obtain ⟨k1, k2⟩ := type21_plane145 hd G hco hα ht hgN gb' gb gc
  have f5 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have f5' := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c
  have fa := F.a'bc.neg a (by simp) haa' hab hac
  have ga : 0 < g a := by
    simp only [g, F.abc.hP, zero_mul, sub_zero]; exact mul_pos_of_neg_of_neg fa f5
  have gc' : 0 < g c' := by
    rw [anti c' a'] at k1
    have : galeD G.l G.m c' a' * g c' = galeD G.l G.m a' a * g a := by linarith
    have := mul_pos hN.h30 ga
    exact pos_of_mul_pos_right (by linarith) s63.le
  have gd : 0 < g d := by
    rw [anti a' a] at k2
    have hc : (β + τ * galeD G.l G.m c c') * -galeD G.l G.m a' a +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a < 0 := by linarith [hn145]
    have : -galeD G.l G.m a' a * g d < 0 := by
      rw [k2]; exact mul_neg_of_neg_of_pos hc gc'
    exact pos_of_mul_neg_right this (by linarith [hN.h30])
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have : g d ≤ 0 := by
    simp only [g]
    nlinarith [mul_le_mul_of_nonpos_right h2 f5.le, mul_le_mul_of_nonpos_right h1 f5'.le]
  linarith

/-- **`f ≠ 0` from `NoPlaneParallel`** (the special position of Lemma 16.16): if
`g_a + g_b + g_c = 0`, the face function of `a'b'c'` takes one value at `a, b, c`, so the segment
`a b` is parallel to the plane `a'b'c'`. -/
theorem gale_f_ne {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hpp : det3 (b' - a') (c' - a') (b - a) ≠ 0) :
    ¬(G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  rintro ⟨h1, h2⟩
  have r1 := G.hl.apply F.a'b'c'.hN
  have r2 := G.hm.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR] at r1 r2
  have hab0 := galeD_ne_zero F G
  have hX : galeD G.l G.m a b * (F.a'b'c'.f a - F.a'b'c'.f c) = 0 := by
    simp only [galeD]
    have e1 : G.l c = -(G.l a + G.l b) := by linarith
    have e2 : G.m c = -(G.m a + G.m b) := by linarith
    rw [e1] at r1; rw [e2] at r2
    linear_combination G.m b * r1 - G.l b * r2
  have hY : galeD G.l G.m a b * (F.a'b'c'.f b - F.a'b'c'.f c) = 0 := by
    simp only [galeD]
    have e1 : G.l c = -(G.l a + G.l b) := by linarith
    have e2 : G.m c = -(G.m a + G.m b) := by linarith
    rw [e1] at r1; rw [e2] at r2
    linear_combination G.l a * r2 - G.m a * r1
  have hX' := sub_eq_zero.mp ((mul_eq_zero.mp hX).resolve_left hab0)
  have hY' := sub_eq_zero.mp ((mul_eq_zero.mp hY).resolve_left hab0)
  exact hpp (facet_tie_det F.a'b'c' (F.a'b'c'.neg a (by simp) haa' hab' hac').ne
    (by rw [hX', hY']))

/-- The three pair brackets of `K − 6` (Lemma 16.2): `[5 4]₂ = r [1 0] {5 4}`,
`[3 0]₂ = −r [1 0] {0 3}`, `[2 1]₂ = r [6 1] [1 0]`, and `[2 5]₂ < 0`. -/
theorem type21_galeO2_kappa {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (G : GaleData a a' b b' c c') (hN : CrossNorm G) {α β τ : ℝ}
    (hα : α = τ * galeD G.l G.m b' c) (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hr : 0 < β + τ * galeD G.l G.m c c') (G2 : GaleData b' b a' a c d)
    (l5 : G2.l b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c b')
    (l4 : G2.l b = β * galeD G.l G.m c b) (l3 : G2.l a' = β * galeD G.l G.m c a')
    (l0 : G2.l a = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a) (l1 : G2.l c = 0)
    (l2 : G2.l d = galeD G.l G.m c c')
    (m5 : G2.m b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b')
    (m4 : G2.m b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b +
        τ * galeD G.l G.m c b * galeD G.l G.m c' a)
    (m3 : G2.m a' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a)
    (m0 : G2.m a = 0) (m1 : G2.m c = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a c)
    (m2 : G2.m d = galeD G.l G.m a c') :
    galeD G2.l G2.m b' b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a *
      ((β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
        τ * galeD G.l G.m b c * galeD G.l G.m b' c') ∧
    galeD G2.l G2.m a' a = -((β + τ * galeD G.l G.m c c') * galeD G.l G.m c a *
      ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a)) ∧
    0 < galeD G2.l G2.m d c ∧ galeD G2.l G2.m d b' < 0 := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have anti := galeD_anti G.l G.m
  have hβ : β = 1 + τ * galeD G.l G.m c a - τ * galeD G.l G.m b' c := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · show G2.l b' * G2.m b - G2.m b' * G2.l b = _
    rw [l5, m4, m5, l4, hβ]
    simp only [galeD, IsDep.l_last G.hl, IsDep.l_last G.hm]; ring
  · show G2.l a' * G2.m a - G2.m a' * G2.l a = _
    rw [l3, m0, m3, l0]; ring
  · show 0 < G2.l d * G2.m c - G2.m d * G2.l c
    rw [l2, m1, m2, l1]
    set r := β + τ * galeD G.l G.m c c'
    rw [anti c' c, anti c a]
    have := mul_pos (mul_pos hr hN.h61) s10
    linarith
  · show G2.l d * G2.m b' - G2.m d * G2.l b' < 0
    rw [l2, m5, m2, l5]
    set r := β + τ * galeD G.l G.m c c'
    rw [anti c' c, anti c' a, anti b' c]
    have := mul_pos hr (mul_pos hN.h61 s05)
    have := mul_pos hr (mul_pos s60 s51)
    linarith

/-- **Lemma 16.22** (`K − 6` of pattern `(+, +, −)`): in class (c) (`{5 4} > 0`, `{0 3} < 0`),
if no K-quad edge of `K − 6` is an E-good quad edge, then by Lemma 9.8 the admissible pair of
`K − 6` is `{1, 2}` and `0 → 4` is an E-good quad edge of `K − 6`. -/
theorem type21_O2_quad04 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G) {α β τ : ℝ}
    (hα : α = τ * galeD G.l G.m b' c) (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hr : 0 < β + τ * galeD G.l G.m c c') (G2 : GaleData b' b a' a c d)
    (l5 : G2.l b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c b')
    (l4 : G2.l b = β * galeD G.l G.m c b) (l3 : G2.l a' = β * galeD G.l G.m c a')
    (l0 : G2.l a = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a) (l1 : G2.l c = 0)
    (l2 : G2.l d = galeD G.l G.m c c')
    (m5 : G2.m b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b')
    (m4 : G2.m b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b +
        τ * galeD G.l G.m c b * galeD G.l G.m c' a)
    (m3 : G2.m a' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a)
    (m0 : G2.m a = 0) (m1 : G2.m c = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a c)
    (m2 : G2.m d = galeD G.l G.m a c')
    (hc013 : 0 < (β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
      τ * galeD G.l G.m b c * galeD G.l G.m b' c')
    (hn145 : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (hpp : det3 (a - b) (c - b) (a' - b') ≠ 0)
    (hQ2 : ¬ Type21Q G2.l G2.m b' b a' a c d) : EGoodQuad G2.l G2.m a a' b d c := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  obtain ⟨k1, k2, k3, k4⟩ := type21_galeO2_kappa (F := F) G hN hα ht hr G2 l5 l4 l3 l0 l1 l2 m5 m4
    m3 m0 m1 m2
  have anti := galeD_anti G.l G.m
  have κ1 : 0 < galeD G2.l G2.m b' b := by rw [k1]; exact mul_pos (mul_pos hr s10) hc013
  have κ2 : 0 < galeD G2.l G2.m a' a := by
    rw [k2, anti a' a]
    have : (β + τ * galeD G.l G.m c c') * -galeD G.l G.m a' a +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a < 0 := by linarith
    have := mul_neg_of_pos_of_neg (mul_pos hr s10) this
    linarith
  have hf : ¬(G2.l b' + G2.l a' + G2.l d = 0 ∧ G2.m b' + G2.m a' + G2.m d = 0) :=
    gale_f_ne hd.O2.swap₃ G2.swap₃ hpp
  rcases arc_step1 hd.O2.swap₃ G2.swap₃ κ1 κ2 k3 hf with ⟨-, h1⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
  · exact (h1 k4).2
  · exfalso
    have hne : galeD G2.l G2.m a' b' ≠ 0 := galeD_ne_zero hd.O2.perm₁₂ G2.perm₁₂
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact hQ2 (Or.inr (Or.inr (Or.inl (h2' hn).1)))
    · exact hQ2 (Or.inr (Or.inr (Or.inr (Or.inl (h2 hp).1))))
  · exfalso
    have hne : galeD G2.l G2.m b' a' ≠ 0 := galeD_ne_zero hd.O2 G2
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact hQ2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h3' hn).1)))))))
    · exact hQ2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h3 hp).1)))))))

/-- **F1 in facet form** (Lemma 16.7 with (ii) in the form `δ_014(2) < δ_014(5)`): `[3 5] > 0`,
`[6 1] > 0`, (iii), (iv) hO2 and the special positions of `T1` at the line `014 ∩ 0256`. -/
theorem cert_type21_F1' {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (hS : F.abc.f b' < F.abc.f d)
    (hiii : F.a'b'c.f a < F.a'b'c.f b ∧ hd.f235.f a < hd.f235.f b)
    (hO2 : galeD G.l G.m a' b < galeD G.l G.m c a')
    (hT1 : ∀ u : ℝ³, u ≠ 0 → ⟪F.abc.N, u⟫ = 0 → ⟪F.ab'c'.N, u⟫ = 0 →
      T1Gen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' u)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have s35 := hN.h35
  have anti := galeD_anti G.l G.m
  obtain ⟨α, β, τ, hα0, hβ, hαβ, hτ, hco, hα, ht⟩ := hd.tau hN
  obtain ⟨e1, e2, e3⟩ := type21_f014 F G hco
  have f5 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have hS' : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m c' a' := by
    have k : galeD G.l G.m c' a' * (F.abc.f d - F.abc.f b') = F.abc.f b' *
        (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
      rw [e3]; linear_combination -β * e2
    have : 0 < F.abc.f b' *
        (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
      rw [← k]; exact mul_pos s63 (by linarith)
    by_contra hc
    push Not at hc
    linarith [mul_nonpos_of_nonpos_of_nonneg f5.le (sub_nonneg.mpr hc)]
  set u₁ := axisView G.l G.m a' a b' c' with hu₁
  have hN014 : ⟪F.abc.N, u₁⟫ = 0 := by
    simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.abc.hN, F.abc.hP,
      sub_zero, anti c' a']
    linear_combination e2
  have hN056 : ⟪F.ab'c'.N, u₁⟫ = 0 := by
    simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.ab'c'.hN,
      F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR]
    ring
  have hu0 : u₁ ≠ 0 := by
    intro h0
    have k : ⟪F.abc'.N, u₁⟫ = galeD G.l G.m a' b' * F.abc'.f b' := by
      simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.abc'.hN,
        F.abc'.hP, F.abc'.hR]
      ring
    rw [h0, inner_zero_right] at k
    have := mul_neg_of_pos_of_neg s35 (F.abc'.neg b' (by simp) (Ne.symm hab')
      (Ne.symm hbb') hb'c')
    linarith
  obtain ⟨hP, hz, -⟩ := hT1 u₁ hu0 hN014 hN056
  exact cert_type21_F1 F hd G hN.h35 hN.h61 hα0 hβ hαβ hco hS' hiii hO2 hP hz
    (fun σ hσ => (hT1 (σ • u₁) (smul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hu0)
      (by rw [real_inner_smul_right, hN014, mul_zero])
      (by rw [real_inner_smul_right, hN056, mul_zero])).2.2) hgen

end Minimality

end
