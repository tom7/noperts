module

public import Minimality.Type21Cover
public import Minimality.UniformTilt

@[expose] public section

/-!
# Type 21: the switch surface (`FEWER-FACES-PROOFS.md` §16, parts L–M)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`;
`[s t] = galeD G.l G.m s t` for Gale data `G` of `O = K − 2`.  The switch surface is
`δ_014(2) = δ_014(5)` (`F.abc.f d = F.abc.f b'`): the view `u₀ = 5 − 2` along the edge `25` is
parallel to the plane `014`.  Three faces are seen edge-on: `0256` and `235` at `25`, and the far
face `014`, whose vertex `1` lies over the open far side `0 – 4`.

* **Lemma 16.28 (the view along 25)** — `type21_switch_view`: the four triple tests of the
  quadrilateral `(2, 0, 4, 3)` at `u₀` have one sign (the faces `0256`, `014`, `235` are parallel
  to `u₀`; each test is a facet value times a constant, `det3_facet_prop`), so the shadow is the
  strictly convex quadrilateral `(p, P0, P4, P3)`, counterclockwise or clockwise;
  `type21_switch_mid1`: `1 = 0 + s (4 − 0) + δ u₀` with `0 < s < 1` (from
  `δ_0256(4) < δ_0256(1)`, i.e. `|[3 1]| > |[3 4]|`) and `δ ≠ 0`;
  `type21_switch_mid6`: `6` lies over the open side from `p` to `P0`, at a nonzero offset from
  both chords `2 – 0` and `5 – 0`.
* **Lemma 16.29 (Lemma E at 25)** — `type21_switch_sep`: if `s_C(O) = +` (`CrossNorm`), `2` and
  `5` lie strictly on opposite sides of the plane `034` (the dependency `{1 ·}` of `K − 6`,
  `type21_depO2_c`, applied to that plane).
* **Theorem 16.30 (the switch surface)** — `cert_type21_switch`: on the switch surface,
  with `CrossNorm` and `|[3 1]| > |[3 4]|`, off `NoPlaneParallel`, `GenPosTie` and `NoHDNEdges`,
  `K` has a rim certificate (`CertV`): Lemma E with ties picks a robustly unimodal rim `(v, 0, 4, 3)` (`v = 2` or
  `5`), and the uniform tilt (Lemma 16.27, `isRupert_edgePair_uniform_robust`) handles the
  middles `6` (over the side at `p`) and `1` (over the far side `0 – 4`) together with the axle.
  This closes the halves `H⁻` (cap-face class, `Type21Cap.lean`) and `H⁻_c` (class (c),
  `Type21Pattern.lean`) of the switch surface; what remains at `25` is three far corners at
  one depth (in `GenPosTie`) and the horizontal double normals (`NoHDNEdges`).

Not formalized: the boundary cases of 16.30 (`s_C(O) = 0`, `|[3 1]| = |[3 4]|`: the latter is a
tie of `NoPlaneParallel`) and Lemma 16.31.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- **A face parallel to the view.**  An affine `f` vanishing at `P`, `Q` with `⟪N, u⟫ = 0`:
the triple tests `det3 (Q − P) (y − P) u` are proportional to the facet values `f y`. -/
theorem det3_facet_prop {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {P Q u : ℝ³} (hP : f P = 0) (hQ : f Q = 0) (hu : ⟪N, u⟫ = 0) (y y' : ℝ³) :
    det3 (Q - P) (y - P) u * f y' = det3 (Q - P) (y' - P) u * f y := by
  have h1 : ⟪N, Q - P⟫ = 0 := by rw [← hf, hP, hQ, sub_self]
  have key := det3_mul_inner_eq (e := Q - P) (u := u) (w := y - P) (w' := y' - P) h1 hu
  rwa [← hf, ← hf, hP, sub_zero, sub_zero] at key

theorem nodup_four {z₀ z₁ z₂ z₃ : ℝ} (h01 : z₀ ≠ z₁) (h02 : z₀ ≠ z₂) (h03 : z₀ ≠ z₃)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) : [z₀, z₁, z₂, z₃].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  exact ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, not_false⟩

section Switch

variable {a a' b b' c c' d : ℝ³}

/-- **Lemma 16.28, the shadow.**  On the switch surface (`δ_014(2) = δ_014(5)`) the triple tests
`T₁ = [2 0 4]`, `T₂ = [2 0 3]`, `T₄ = [2 4 3]` at `u₀ = 5 − 2` have the sign of `T₃ = [0 4 3]`
(through the faces `0256`, `014`, `235`, all parallel to `u₀`). -/
theorem type21_switch_view (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hsw : F.abc.f d = F.abc.f b') (hT3 : det3 (b - a) (a' - a) (b' - d) ≠ 0) :
    0 < det3 (b - a) (a' - a) (b' - d) * det3 (a - d) (b - d) (b' - d) ∧
    0 < det3 (b - a) (a' - a) (b' - d) * det3 (a - d) (a' - d) (b' - d) ∧
    0 < det3 (b - a) (a' - a) (b' - d) * det3 (b - d) (a' - d) (b' - d) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  -- `014`: `T₃ f(2) = T₁ f(3)`
  have hf : det3 (b - a) (a' - a) (b' - d) * F.abc.f d =
      det3 (a - d) (b - d) (b' - d) * F.abc.f a' := by
    have hu0 : ⟪F.abc.N, b' - d⟫ = 0 := by rw [← F.abc.hN, hsw, sub_self]
    have := det3_facet_prop F.abc.hN F.abc.hP F.abc.hQ hu0 a' d
    rw [this]
    congr 1
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- `0256`: `T₁ g(3) = T₂ g(4)`
  have hg : det3 (a - d) (b - d) (b' - d) * F.ab'c'.f a' =
      det3 (a - d) (a' - d) (b' - d) * F.ab'c'.f b := by
    have hu0 : ⟪F.ab'c'.N, b' - d⟫ = 0 := by rw [← F.ab'c'.hN, F.ab'c'.hQ, hd.ab'c', sub_self]
    exact det3_facet_prop F.ab'c'.hN hd.ab'c' F.ab'c'.hP hu0 b a'
  -- `235`: `T₂ h(4) = T₄ h(0)`
  have hh : det3 (a - d) (a' - d) (b' - d) * hd.f235.f b =
      det3 (b - d) (a' - d) (b' - d) * hd.f235.f a := by
    have hu0 : ⟪hd.f235.N, b' - d⟫ = 0 := by
      rw [← hd.f235.hN, hd.f235.hP, hd.f235.hR, sub_self]
    have := det3_facet_prop hd.f235.hN hd.f235.hR hd.f235.hQ hu0 a b
    have e1 : det3 (a' - d) (a - d) (b' - d) = -det3 (a - d) (a' - d) (b' - d) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (a' - d) (b - d) (b' - d) = -det3 (b - d) (a' - d) (b' - d) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e1, e2] at this; linarith
  have fd := hd.abc
  have fa' := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  have ga' := F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c'
  have gb := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have ha := hd.f235.neg a (by simp) hab' haa' (Ne.symm hda)
  have hb := hd.f235.neg b (by simp) hbb' (Ne.symm ha'b) (Ne.symm hdb)
  generalize det3 (b - a) (a' - a) (b' - d) = T3 at hT3 hf ⊢
  generalize det3 (a - d) (b - d) (b' - d) = T1 at hf hg ⊢
  generalize det3 (a - d) (a' - d) (b' - d) = T2 at hg hh ⊢
  generalize det3 (b - d) (a' - d) (b' - d) = T4 at hh ⊢
  have p1 : 0 < T3 * T1 := by
    have : (T3 * T1) * F.abc.f a' = (T3 * T3) * F.abc.f d := by linear_combination T3 * hf.symm
    nlinarith [mul_self_pos.mpr hT3]
  have p2 : 0 < T3 * T2 := by
    have : (T3 * T2) * F.ab'c'.f b = (T3 * T1) * F.ab'c'.f a' := by linear_combination -T3 * hg
    nlinarith
  have p4 : 0 < T3 * T4 := by
    have : (T3 * T4) * hd.f235.f a = (T3 * T2) * hd.f235.f b := by linear_combination -T3 * hh
    nlinarith
  exact ⟨p1, p2, p4⟩

/-- **Lemma 16.28, the vertex `1`.**  On the switch surface, with `δ_0256(4) < δ_0256(1)`
(`|[3 1]| > |[3 4]|`), `1` lies over the open far side `0 – 4` at the view `u₀ = 5 − 2`:
`1 = 0 + s (4 − 0) + δ u₀`, `0 < s < 1`, `δ ≠ 0`. -/
theorem type21_switch_mid1 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hsw : F.abc.f d = F.abc.f b') (hF1 : F.ab'c'.f b < F.ab'c'.f c)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hT1 : det3 (a - d) (b - d) (b' - d) ≠ 0) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ c = a + s • (b - a) + δ • (b' - d) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  -- `1` lies on the plane through `0`, `4` parallel to `u₀` (the face `014`)
  have hu0 : ⟪F.abc.N, b' - d⟫ = 0 := by rw [← F.abc.hN, hsw, sub_self]
  have h0 : det3 (b - a) (b' - d) (c - a) = 0 := by
    have := det3_facet_prop F.abc.hN F.abc.hP F.abc.hQ hu0 c d
    rw [F.abc.hR, mul_zero] at this
    have h' : det3 (b - a) (c - a) (b' - d) = 0 := (mul_eq_zero.mp this).resolve_right hd.abc.ne
    rw [det3_swap23, h', neg_zero]
  have hD : det3 (b - a) (b' - d) (d - a) ≠ 0 := by
    have : det3 (b - a) (b' - d) (d - a) = -det3 (a - d) (b - d) (b' - d) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]; exact neg_ne_zero.mpr hT1
  have hcr := cramer (b - a) (b' - d) (d - a) (c - a)
  rw [h0, zero_smul, add_zero] at hcr
  generalize det3 (b - a) (b' - d) (d - a) = D at hcr hD
  generalize det3 (c - a) (b' - d) (d - a) = A at hcr
  generalize det3 (b - a) (c - a) (d - a) = B at hcr
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = A / D := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = B / D := ⟨_, rfl⟩
  have hX : c - a = s • (b - a) + δ • (b' - d) := by
    calc c - a = D⁻¹ • (D • (c - a)) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      _ = s • (b - a) + δ • (b' - d) := by rw [hcr, hs, hδdef]; module
  have hc : c = a + s • (b - a) + δ • (b' - d) := by
    rw [add_assoc, ← hX]; abel
  -- `0 < s < 1` from the face `0256`
  have hg : F.ab'c'.f c = s * F.ab'c'.f b := by
    have k := F.ab'c'.hN c a
    have k2 := F.ab'c'.hN b a
    have k3 : ⟪F.ab'c'.N, b' - d⟫ = 0 := by rw [← F.ab'c'.hN, F.ab'c'.hQ, hd.ab'c', sub_self]
    rw [F.ab'c'.hP, sub_zero] at k k2
    rw [k, hX, inner_add_right, real_inner_smul_right, real_inner_smul_right, k3, mul_zero,
      add_zero, ← k2]
  have gc := F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
  have gb := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  have hs0 : 0 < s := by
    by_contra h; push Not at h; nlinarith
  have hs1 : s < 1 := by
    by_contra h; push Not at h; nlinarith
  have hδ : δ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hX
    exact hgen.ne_smul (s := a) (t := c) (x := a) (y := b) (by simp) (by simp) (by simp)
      (by simp) hac hab ⟨Ne.symm hac, Ne.symm hbc⟩ s hX
  exact ⟨s, δ, hs0, hs1, hδ, hc⟩

/-- **Lemma 16.28, the vertex `6`.**  On the switch surface (`2 = 0 + α (5 − 0) + β (6 − 0)` with
`α < 1`), `6` lies over the open side from `p = P2 = P5` to `P0`: over the chord from `2` to `0`
and over the chord from `5` to `0`, at a nonzero depth offset from each. -/
theorem type21_switch_mid6 {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα1 : α < 1)
    (hco : d = a + α • (b' - a) + β • (c' - a)) :
    ∃ s δ δ' : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧
      c' = d + s • (a - d) + δ • (b' - d) ∧ c' = b' + s • (a - b') + δ' • (b' - d) := by
  set ib := β⁻¹ with hibdef
  have hib : β * ib = 1 := mul_inv_cancel₀ hβ.ne'
  have hib0 : 0 < ib := inv_pos.mpr hβ
  refine ⟨(α + β - 1) * ib, -(α * ib), -ib, mul_pos (by linarith) hib0, ?_,
    neg_ne_zero.mpr (mul_pos hα hib0).ne', neg_ne_zero.mpr hib0.ne', ?_, ?_⟩
  · have : (α + β - 1) * ib < β * ib := mul_lt_mul_of_pos_right (by linarith) hib0
    linarith
  · rw [hco]
    linear_combination (norm := module) hib • (-((1 - β) • c' - α • b' - (1 - α - β) • a))
  · rw [hco]
    linear_combination (norm := module) hib • (b' - c')

/-- **Lemma 16.29 (Lemma E at 25).**  If `s_C(O) = +` (`CrossNorm`), the dependency `{1 ·}` of
`K − 6` (Lemma 16.2) vanishes at `1` and lives on `0, 2, 3, 4, 5`; applied to the plane `034` it
gives `{1 2} ψ(2) + {1 5} ψ(5) = 0` with `{1 2} {1 5} > 0`.  So `2` and `5` lie weakly on opposite
sides of the plane `034`, strictly unless both lie on it. -/
theorem type21_switch_sep (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (G : GaleData a a' b b' c c') (hN : CrossNorm G) :
    det3 (a' - a) (b - a) (d - a) * det3 (a' - a) (b - a) (b' - a) ≤ 0 := by
  obtain ⟨α, β, τ, -, -, -, -, hco, hα, ht⟩ := hd.tau hN
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  obtain ⟨L, hL, Ld, Lc, Lb', -, -, -⟩ := type21_depO2_c hd G hco hα ht
  obtain ⟨-, -, -, -, s51, -, -, -, -, -, -⟩ := hN.signs F
  set ψ : ℝ³ → ℝ := fun y => det3 (a' - a) (b - a) (y - a) with hψ
  have hψN : ∀ y z, ψ y - ψ z = ⟪cross (a' - a) (b - a), y - z⟫ := by
    intro y z; simp only [ψ, det3, ← inner_sub_right]; congr 1; abel
  have key := hL.apply hψN
  have e0 : ψ a = 0 := by simp only [ψ, sub_self, det3, inner_zero_right]
  have e3 : ψ a' = 0 := by simp only [ψ, det3_expand, PiLp.sub_apply]; ring
  have e4 : ψ b = 0 := by simp only [ψ, det3_expand, PiLp.sub_apply]; ring
  rw [e0, e3, e4, Lc, Ld, Lb'] at key
  have k16 : galeD G.l G.m c c' < 0 := by rw [galeD_anti]; linarith [hN.h61]
  have k15 : galeD G.l G.m c b' < 0 := by rw [galeD_anti]; linarith
  set A := galeD G.l G.m c c'
  set B := (β + τ * galeD G.l G.m c c') * galeD G.l G.m c b'
  have hB : B < 0 := mul_neg_of_pos_of_neg hr k15
  have k : A * ψ d + B * ψ b' = 0 := by linarith
  show ψ d * ψ b' ≤ 0
  have : A * (ψ d * ψ b') = -B * (ψ b' * ψ b') := by linear_combination ψ b' * k
  nlinarith [mul_self_nonneg (ψ b')]

/-- **Theorem 16.30 (the switch surface).**  Let `K = O ∪ {2}` be of type 21 (`IsCap21`) with
Gale data of `O = K − 2` in the normalization `CrossNorm` (`s_C(O) = +`; the cap-face class and
the pattern `(+, −, +)` of the other classes), on the switch surface `δ_014(2) = δ_014(5)`, with
`δ_0256(4) < δ_0256(1)` (`|[3 1]| > |[3 4]|`).  Off `NoPlaneParallel`, `GenPosTie` and horizontal
double normals at the edge views (`NoHDNEdges`), `K` has a rim certificate (`CertV`): at the view along `25` the
shadow is the quadrilateral `(p, P0, P4, P3)` (16.28), `2` and `5` lie on opposite sides of the
plane `034` (16.29), so one rim `(v, 0, 4, 3)` is unimodal (Lemma E), and the uniform tilt
(16.27) takes care of the middles `6` (over the side `p – P0`) and `1` (over the far side
`P0 – P4`) and of the axle. -/
theorem cert_type21_switch (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (hsw : F.abc.f d = F.abc.f b') (hF1 : F.ab'c'.f b < F.ab'c'.f c)
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L (Edge21 a a' b b' c c' d) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKc' : c' ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  -- the triple tests (Lemma 16.28)
  have hT3 : det3 (b - a) (a' - a) (b' - d) ≠ 0 := by
    refine hpp a hKa b hKb a' hKa' d hKd b' hKb' ?_
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hab, haa', Ne.symm hda, hab'⟩, ⟨Ne.symm ha'b, Ne.symm hdb, hbb'⟩,
      ⟨Ne.symm hda', ha'b'⟩, hdb', not_false⟩
  obtain ⟨p1, p2, p4⟩ := type21_switch_view F hd hsw hT3
  have hT1 : det3 (a - d) (b - d) (b' - d) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at p1; exact lt_irrefl _ p1
  -- the middles (Lemma 16.28)
  obtain ⟨s₁, δ₁, hs₁0, hs₁1, hδ₁, hc⟩ := type21_switch_mid1 F hd hsw hF1 hgen hT1
  obtain ⟨α, β, τ, hα, hβ, hαβ, -, hco, -, -⟩ := hd.tau hN
  have hα1 : α < 1 := by
    obtain ⟨-, -, e3⟩ := type21_f014 F G hco
    have f5 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
    have f6 := F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')
    rw [hsw] at e3
    nlinarith [mul_pos hβ (neg_pos.mpr f6)]
  obtain ⟨s, δ, δ', hs0, hs1, hδ, hδ', hc'd, hc'b'⟩ := type21_switch_mid6 hα hβ hαβ hα1 hco
  -- Lemma 16.29
  have hE := type21_switch_sep F hd G hN
  -- distinct depths along `25`, no horizontal double normals there
  have hnt : ¬ (⟪a', b' - d⟫ = ⟪b, b' - d⟫ ∧ ⟪b, b' - d⟫ = ⟪a, b' - d⟫) :=
    hgen.noTriple hKd hKb' hKa' hKb hKa hdb' ha'b (Ne.symm hab) (Ne.symm haa')
  have hMK : ∀ z, z ∈ ({c', c} : Finset ℝ³) ↔ z = c' ∨ z = c := by
    intro z; simp only [mem_insert, mem_singleton]
  have nM : ∀ z, z ≠ c' → z ≠ c → z ∉ ({c', c} : Finset ℝ³) := by
    intro z h1 h2 h; rcases (hMK z).mp h with h | h
    · exact h1 h
    · exact h2 h
  have hV : ∀ (A C B : ℝ³), (A = a ∧ C = b ∧ B = a' ∨ A = a' ∧ C = b ∧ B = a) →
      ∀ z ∈ K, z ∉ ({c', c} : Finset ℝ³) → z = d ∨ z = b' ∨ z = A ∨ z = B ∨ z = C ∨
        EdgeHidden (b' - d) d A C B z := by
    intro A C B hACB z hz hzM
    have hz' : z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
      simpa [hK] using hz
    rcases hACB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hz' with h | h | h | h | h | h | h
    all_goals first
      | (left; exact h)
      | (right; left; exact h)
      | (right; right; left; exact h)
      | (right; right; right; left; exact h)
      | (right; right; right; right; left; exact h)
      | (exact absurd ((hMK z).mpr (Or.inr h)) hzM)
      | (exact absurd ((hMK z).mpr (Or.inl h)) hzM)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  rcases lt_or_gt_of_ne hT3 with hneg | hpos
  · -- clockwise: the rim `(v, 3, 4, 0)`
    refine CertV.seg hKd hKb' hdb' (by simp [Edge21, SPair])
      (rimCert_edgePair_uniform_robust (v := d) (w := b') (a := a')
      (c := b) (b := a) K
      {c', c} hKd hKb' hKa' hKa hKb (nM d hdc' hdc) (nM b' hb'c' hb'c)
      (nM a' ha'c' ha'c) (nM a hac' hac) (nM b hbc' hbc) ?_ ?_ ?_ ?_ ?_ hnt
      (hV a' b a (Or.inr ⟨rfl, rfl, rfl⟩)) ?_ ?_)
    · have : det3 (a' - d) (b - d) (b' - d) = -det3 (b - d) (a' - d) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; nlinarith
    · have : det3 (b - a') (a - a') (b' - d) = -det3 (b - a) (a' - a) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    · have : det3 (a - b) (d - b) (b' - d) = -det3 (a - d) (b - d) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; nlinarith
    · have : det3 (d - a) (a' - a) (b' - d) = -det3 (a - d) (a' - d) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; nlinarith
    · have e1 : ∀ y, det3 (a - a') (b - a') (y - a') = -det3 (a' - a) (b - a) (y - a) := by
        intro y; simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e1, neg_mul_neg]; exact hE
    · intro m hm
      rcases (hMK m).mp hm with rfl | rfl
      · refine ⟨3, 1 - s, δ, by linarith, by linarith, hδ, ?_⟩
        simp only [a3, quad_0, quad_3]
        rw [hc'd]; module
      · refine ⟨2, 1 - s₁, δ₁, by linarith, by linarith, hδ₁, ?_⟩
        simp only [a2, quad_2, quad_3]
        rw [hc]; module
    · intro m hm
      rcases (hMK m).mp hm with rfl | rfl
      · refine ⟨3, 1 - s, δ', by linarith, by linarith, hδ', ?_⟩
        simp only [a3, quad_0, quad_3]
        rw [hc'b']; module
      · refine ⟨2, 1 - s₁, δ₁, by linarith, by linarith, hδ₁, ?_⟩
        simp only [a2, quad_2, quad_3]
        rw [hc]; module
  · -- counterclockwise: the rim `(v, 0, 4, 3)`
    refine CertV.seg hKd hKb' hdb' (by simp [Edge21, SPair])
      (rimCert_edgePair_uniform_robust (v := d) (w := b') (a := a)
      (c := b) (b := a') K
      {c', c} hKd hKb' hKa hKa' hKb (nM d hdc' hdc) (nM b' hb'c' hb'c)
      (nM a hac' hac) (nM a' ha'c' ha'c) (nM b hbc' hbc) ?_ hpos ?_ ?_ hE
      (fun h => hnt ⟨h.2.symm, h.1.symm⟩)
      (hV a b a' (Or.inl ⟨rfl, rfl, rfl⟩)) ?_ ?_)
    · exact pos_of_mul_pos_right p1 hpos.le
    · have : det3 (a' - b) (d - b) (b' - d) = det3 (b - d) (a' - d) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact pos_of_mul_pos_right p4 hpos.le
    · have : det3 (d - a') (a - a') (b' - d) = det3 (a - d) (a' - d) (b' - d) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact pos_of_mul_pos_right p2 hpos.le
    · intro m hm
      rcases (hMK m).mp hm with rfl | rfl
      · exact ⟨0, s, δ, hs0, hs1, hδ, by simp only [a0, quad_0, quad_1]; exact hc'd⟩
      · exact ⟨1, s₁, δ₁, hs₁0, hs₁1, hδ₁, by simp only [a1, quad_1, quad_2]; exact hc⟩
    · intro m hm
      rcases (hMK m).mp hm with rfl | rfl
      · exact ⟨0, s, δ', hs0, hs1, hδ', by simp only [a0, quad_0, quad_1]; exact hc'b'⟩
      · exact ⟨1, s₁, δ₁, hs₁0, hs₁1, hδ₁, by simp only [a1, quad_1, quad_2]; exact hc⟩

end Switch

end Minimality

end
