module

public import Minimality.Type21Cover
public import Minimality.RobustAxis

@[expose] public section

/-!
# Type 21: the tier F1 (`FEWER-FACES-PROOFS.md` Lemma 16.7)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`, the
normalized cap-face class (`CapNorm`), `2 = 0 + α (5 − 0) + β (6 − 0)` and `τ` as in
`IsCap21.tau`.

* **T1** is the vertex crossing at `0` of the faces `014`, `0256`, at the view
  `u₁ = [3 5] (5 − 0) + [3 6] (6 − 0)` (`axisView` in S's dictionary `(3, 0, 5, 4, 6, 1)`); by
  (ii) `δ_014(2) < δ_014(5)` the cap `2` is a middle over the side `0 → 5` (Lemma 16.6), so
  `isRupert_axisTest` applies to `K`: either `K` is Rupert, or the rim `(0, 5, 3, 4)` has
  depth-separated diagonals `[0, 3]`, `[5, 4]` whose projections meet, `e − d = λ u₁`.
  Applying `det(5 − 0, 4 − 0, ·)` and the dependency `[1 ·]` gives `λ [6 3] [1 3] = s [6 1] ≥ 0`
  (Lemma 16.7 (a), (e)), so the failure is "`{5, 4}` above `{0, 3}`" and `⟪4 − 0, u₁⟫ > 0`.
* **Y** is the edge crossing along `04` with the kept apex `0` (`u = 0 − 4`).  By (iii)
  (`0 → 4` a quad edge of `K − 6`: the faces `135`, `235` face up along `4 − 0`) the rim of
  `K − 4` is the pentagon `(0, 6, 2, 5, 1)` with `3` hidden: twenty determinant tests, from the
  vertical faces `046`, `014`, the face pairs `2346/0256`, `235/0256`, `135/015`, and the plane
  coordinates of `0256` (Lemma 16.7 (c)).  Its depths are unimodal unless the peaks are
  `{0, 5}` (Lemma 16.7 (d): `{0, 2}` and `{6, 5}` contradict `α < 1 < α + β`, a peak at `1`
  contradicts the convexity of the pentagon, since `1` lies beneath `0256`), and with the peaks
  `{0, 5}`, `(1 − α) ⟪u₁, 0 − 4⟫ = [3 5] (z₅ − z₂) + ((1 − α) [6 3] − β [3 5]) (z₀ − z₆) > 0`
  (Lemma 16.7 (b)).
* **Lemma 16.7 (F1)** — `isRupert_type21_F1`: the two failures contradict each other.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The depth analysis of the pentagon `(0, 6, 2, 5, 1)` (Lemma 16.7 (d)) -/

/-- Peaks `{0, 2}` (or, mirrored, `{6, 5}`) of the coplanar four contradict `α + β > 1`. -/
theorem type21_peaks_02 {Z5 Z6 α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα1 : α < 1)
    (hαβ : 1 < α + β) (h6 : Z6 < 0) (h1 : 0 < α * Z5 + (β - 1) * Z6)
    (h2 : 0 < (α - 1) * Z5 + β * Z6) : False := by
  have hZ5 : Z5 < 0 := by nlinarith
  have k1 : α * (-Z5) < (1 - β) * (-Z6) := by linarith
  have k2 : β * (-Z6) < (1 - α) * (-Z5) := by linarith
  have := mul_lt_mul'' k1 k2 (by nlinarith) (by nlinarith)
  nlinarith [mul_pos (neg_pos.mpr hZ5) (neg_pos.mpr h6)]

theorem type21_peaks_65 {Z5 Z6 α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα1 : α < 1)
    (hαβ : 1 < α + β) (h6 : 0 < Z6) (h1 : α * Z5 + (β - 1) * Z6 < 0)
    (h2 : (α - 1) * Z5 + β * Z6 < 0) : False :=
  type21_peaks_02 (Z5 := -Z5) (Z6 := -Z6) hα hβ hα1 hαβ (by linarith) (by linarith)
    (by linarith)

/-- Peaks `{6, 1}`: `1` is beneath the plane of `0256` (`z₁ < A(P₁)`, the affine extension of
the depth), so `1` would be a peak of `A` beyond the side `5 0`, which the convexity of the
pentagon at `5` forbids. -/
theorem type21_peaks_61 {Z5 Z6 Z1 α β p q : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα1 : α < 1)
    (hαβ : 1 < α + β) (hp : 0 < p) (hq : q < 0) (hconv : (p - 1) * β + q * (1 - α) < 0)
    (hZ1 : Z1 < p * Z5 + q * Z6) (h6 : 0 < Z6) (h62 : α * Z5 + (β - 1) * Z6 < 0)
    (h15 : Z5 < Z1) (h10 : 0 < Z1) : False := by
  have k0 : 0 < (p - 1) * Z5 + q * Z6 := by linarith
  have k1 : 0 < (p - 1) * Z5 := by nlinarith
  rcases lt_trichotomy Z5 0 with h5 | h5 | h5
  · have : p < 1 := by nlinarith
    nlinarith
  · rw [h5, mul_zero] at k1; exact lt_irrefl _ k1
  · have hp1 : 1 < p := by nlinarith
    -- `α |q| < (1 − β)(p − 1)` and `β (p − 1) < (1 − α) |q|`
    have k2 : α * (-q) * Z6 < (1 - β) * (p - 1) * Z6 := by nlinarith
    have k3 : α * (-q) < (1 - β) * (p - 1) := lt_of_mul_lt_mul_right k2 h6.le
    have k4 : β * (p - 1) < (1 - α) * (-q) := by linarith
    have := mul_lt_mul'' k3 k4 (by nlinarith) (by nlinarith)
    nlinarith [mul_pos (neg_pos.mpr hq) (sub_pos.mpr hp1)]

/-- Peaks `{2, 1}`: as for `{6, 1}`. -/
theorem type21_peaks_21 {Z5 Z6 Z1 α β p q : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα1 : α < 1)
    (hαβ : 1 < α + β) (hp : 0 < p) (hq : q < 0) (hconv : (p - 1) * β + q * (1 - α) < 0)
    (hZ1 : Z1 < p * Z5 + q * Z6) (h26 : 0 < α * Z5 + (β - 1) * Z6)
    (h25 : 0 < (α - 1) * Z5 + β * Z6) (h15 : Z5 < Z1) (h10 : 0 < Z1) : False := by
  rcases lt_or_ge 0 Z6 with h6 | h6
  · have k0 : 0 < (p - 1) * Z5 + q * Z6 := by linarith
    have k1 : 0 < (p - 1) * Z5 := by nlinarith
    rcases lt_trichotomy Z5 0 with h5 | h5 | h5
    · have : p < 1 := by nlinarith
      nlinarith
    · rw [h5, mul_zero] at k1; exact lt_irrefl _ k1
    · have hp1 : 1 < p := by nlinarith
      -- `(p − 1) Z5 > |q| Z6 > |q| (1 − α) Z5 / β`
      have k2 : (-q) * ((1 - α) * Z5) < (-q) * (β * Z6) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have k3 : β * ((-q) * Z6) < β * ((p - 1) * Z5) := mul_lt_mul_of_pos_left (by linarith) hβ
      have k4 : (-q) * (1 - α) * Z5 < β * (p - 1) * Z5 := by nlinarith
      have k5 : (-q) * (1 - α) < β * (p - 1) := lt_of_mul_lt_mul_right k4 h5.le
      linarith
  · rcases lt_or_ge β 1 with hb | hb
    · have h5 : Z5 < 0 := by nlinarith
      rcases eq_or_lt_of_le h6 with h6 | h6
      · rw [h6] at h26; nlinarith
      · have k1 : α * (-Z5) < (1 - β) * (-Z6) := by linarith
        have k2 : β * (-Z6) < (1 - α) * (-Z5) := by linarith
        have := mul_lt_mul'' k1 k2 (by nlinarith) (by nlinarith)
        nlinarith [mul_pos (neg_pos.mpr h5) (neg_pos.mpr h6)]
    · have : 0 < Z5 := by nlinarith
      nlinarith

/-- **The pentagon `(0, 6, 2, 5, 1)` of `Y` is unimodal** unless the peaks are `{0, 5}`, which
is excluded by `hT1` (`(1 − α) ⟪u₁, 0 − 4⟫ = B (z₅ − z₂) + A (z₀ − z₆) < 0`, `A, B > 0`).
Here `z₂ = z₀ + α Z₅ + β Z₆` (`2` on the plane of `0256`) and `z₁ < z₀ + p Z₅ + q Z₆` (`1`
strictly beneath it), with `p > 0 > q` and the convexity of the pentagon at `5`. -/
theorem type21_Y_unimodal {z0 z6 z2 z5 z1 α β p q A B : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hα1 : α < 1) (hαβ : 1 < α + β) (hp : 0 < p) (hq : q < 0)
    (hconv : (p - 1) * β + q * (1 - α) < 0)
    (h2 : z2 = z0 + α * (z5 - z0) + β * (z6 - z0)) (h1 : z1 < z0 + p * (z5 - z0) + q * (z6 - z0))
    (hA : 0 < A) (hB : 0 < B) (hT1 : B * (z5 - z2) + A * (z0 - z6) < 0)
    (hinj : Function.Injective (quint z0 z6 z2 z5 z1)) :
    IsCyclicUnimodal (quint z0 z6 z2 z5 z1) := by
  refine unimodal5_tac hinj fun i j hi hj => ?_
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have P02 := fun h6 h1 h2 => type21_peaks_02 (Z5 := z5 - z0) (Z6 := z6 - z0) hα hβ hα1 hαβ h6 h1 h2
  have P65 := fun h6 h1 h2 => type21_peaks_65 (Z5 := z5 - z0) (Z6 := z6 - z0) hα hβ hα1 hαβ h6 h1 h2
  have P61 := fun h6 h62 h15 h10 => type21_peaks_61 (Z5 := z5 - z0) (Z6 := z6 - z0)
    (Z1 := z1 - z0) hα hβ hα1 hαβ hp hq hconv (by linarith) h6 h62 h15 h10
  have P21 := fun h26 h25 h15 h10 => type21_peaks_21 (Z5 := z5 - z0) (Z6 := z6 - z0)
    (Z1 := z1 - z0) hα hβ hα1 hαβ hp hq hconv (by linarith) h26 h25 h15 h10
  have P05 : z6 < z0 → z2 < z5 → False := fun h h' => by
    nlinarith [mul_pos hB (sub_pos.mpr h'), mul_pos hA (sub_pos.mpr h)]
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
    quint_4] at hi hj <;>
  first
  | rfl
  | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso; exact P02 (by linarith [hi.2]) (by linarith [h2, hj.1]) (by linarith [h2, hj.2]))
  | (exfalso; exact P65 (by linarith [hi.1]) (by linarith [h2, hi.2]) (by linarith [h2, hj.1]))
  | (exfalso; exact P61 (by linarith [hi.1]) (by linarith [h2, hi.2]) (by linarith [hj.1])
      (by linarith [hj.2]))
  | (exfalso; exact P21 (by linarith [h2, hi.1]) (by linarith [h2, hi.2]) (by linarith [hj.1])
      (by linarith [hj.2]))
  | (exfalso; exact P05 (by linarith [hi.2]) (by linarith [hj.1]))

/-! ### A five-corner edge view -/

/-- **Theorem 8.9 with Theorem 7.3 for a five-corner rim, in either orientation**: the rim
`x₀ … x₄` passes the fifteen determinant tests at `u` with the sign `σ`, every other point
except `w = x₀ − h u` is strictly inside, the depths are unimodal and there is no horizontal
double normal: `V` is Rupert (`isRupert_of_edgeView`, at `u` or `−u`). -/
theorem isRupert_quint_rim (V : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {x₀ x₁ x₂ x₃ x₄ w : ℝ³} {h : ℝ} (hh : h ≠ 0) (hw : w = x₀ - h • u) (hwV : w ∈ V)
    (hxV : ∀ i, quint x₀ x₁ x₂ x₃ x₄ i ∈ V)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < σ * det3
      (quint x₀ x₁ x₂ x₃ x₄ (i + 1) - quint x₀ x₁ x₂ x₃ x₄ i)
      (quint x₀ x₁ x₂ x₃ x₄ j - quint x₀ x₁ x₂ x₃ x₄ i) u)
    (hrest : ∀ y ∈ V, y ≠ w → (∀ j, y ≠ quint x₀ x₁ x₂ x₃ x₄ j) → ∀ i, 0 < σ * det3
      (quint x₀ x₁ x₂ x₃ x₄ (i + 1) - quint x₀ x₁ x₂ x₃ x₄ i) (y - quint x₀ x₁ x₂ x₃ x₄ i) u)
    (hz : IsCyclicUnimodal fun i => ⟪quint x₀ x₁ x₂ x₃ x₄ i, u⟫) (hnd : NoHDNAt (V.erase w) u) :
    IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hcyc hrest
    exact isRupert_of_edgeView V ∅ u hu (k := 5) (by norm_num) (quint x₀ x₁ x₂ x₃ x₄) 0 w h hwV
      hw hh hxV (fun _ => notMem_empty _) hcyc (fun y hy _ hyw hyx => hrest y hy hyw hyx) hz hnd
      (fun m hm => absurd hm (notMem_empty m))
  · refine isRupert_of_edgeView V ∅ (-u) (neg_ne_zero.mpr hu) (k := 5) (by norm_num)
      (quint x₀ x₁ x₂ x₃ x₄) 0 w (-h) hwV (by rw [hw, neg_smul_neg]; rfl) (neg_ne_zero.mpr hh)
      hxV (fun _ => notMem_empty _) (fun i j hi hj => ?_) (fun y hy _ hyw hyx i => ?_) ?_
      hnd.neg (fun m hm => absurd hm (notMem_empty m))
    · have := hcyc i j hi hj; rw [det3_neg_right]; linarith
    · have := hrest y hy hyw hyx i; rw [det3_neg_right]; linarith
    · simp only [inner_neg_right]
      refine isCyclicUnimodal_of_localMin_unique (by norm_num) _ (fun a b e => hz.1 (neg_injective e)) ?_
      intro a b h1 h2 h3 h4
      have hc := Finset.card_le_one.mp hz.2.le
      exact hc a (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)
        b (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)

/-! ### `Y`: the edge crossing along `04` (Lemma 16.7 (c), (d)) -/

/-- **`Y` (Lemma 16.7 (c), (d))**, in the normalized class.  Let (ii) `{3 5} < [6 3]`
(`δ_014(2) < δ_014(5)`) and (iii) `0 → 4` a quad edge of `K − 6` (`f₁₃₅(0) < f₁₃₅(4)`,
`f₂₃₅(0) < f₂₃₅(4)`).  At the view `u = 0 − 4` the rim of `K − 4` is the pentagon
`(0, 6, 2, 5, 1)` with `3` hidden; if `⟪0 − 4, u₁⟫ < 0` (`T1` failed), its depths are unimodal
and `K` is Rupert, off `GenPos` and horizontal double normals at the edge views. -/
theorem isRupert_type21_Y {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (h35 : 0 < galeD G.l G.m a' b') {α β : ℝ}
    (hα0 : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hco : d = a + α • (b' - a) + β • (c' - a))
    (hS : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m c' a')
    (hiii : F.a'b'c.f a < F.a'b'c.f b ∧ hd.f235.f a < hd.f235.f b)
    (hT1 : ⟪a - b, axisView G.l G.m a' a b' c'⟫ < 0)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := type21_cross_signs F h35
  have s35 := h35
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  set u := a - b with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr hab
  have hα1 : α < 1 := by
    have : α * galeD G.l G.m c' a' < 1 * galeD G.l G.m c' a' := by
      have := mul_pos hβ s35; linarith
    exact lt_of_mul_lt_mul_right this s63.le
  -- facet values used below
  have f046b := F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'
  have f046c := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have f046a' := F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c'
  have f014c' := F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')
  have f014b' := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have f014a' := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  have f056b := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  have f056c := F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
  have f056a' := F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c'
  have f346a := F.a'bc'.neg a (by simp) haa' hab hac'
  have f346b' := F.a'bc'.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c'
  have f346c := F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
  have f135a := F.a'b'c.neg a (by simp) haa' hab' hac
  have f135c' := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  have f015b := F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc
  have f015c' := F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
  have f015a' := F.ab'c.neg a' (by simp) (Ne.symm haa') ha'b' ha'c
  have f235a := hd.f235.neg a (by simp) hab' haa' (Ne.symm hda)
  have f235c := hd.f235.neg c (by simp) (Ne.symm hb'c) (Ne.symm ha'c) (Ne.symm hdc)
  -- the orientation `σ` of `(0, 6, 5)`
  set T := det3 (c' - a) (b' - a) u with hT_def
  have hT : T ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine F.ab'c.hN hab' F.ab'c.hP F.ab'c.hQ f015c'
    have := affine_zero_of_coplanar F.ab'c'.hN F.ab'c'.hP F.ab'c'.hQ F.ab'c'.hR hc (w := b) (by
      have e : det3 (b' - a) (c' - a) (b - a) = T := by
        simp only [hT_def, hu_def, det3_expand, PiLp.sub_apply]; ring
      rw [e, h0])
    linarith
  obtain ⟨σ, hσ, hσT⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * T := by
    rcases lt_or_gt_of_ne hT with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hNu : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) →
      ⟪N, u⟫ = f a - f b := fun hf => by rw [hf]
  -- in-plane tests (the quadrilateral `0256`)
  have p_a_c'_d : det3 (c' - a) (d - a) u = α * T := by
    rw [hco]; simp only [hT_def, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have p_c'_d_a : det3 (d - c') (a - c') u = α * T := by
    rw [hco]; simp only [hT_def, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have p_d_b'_a : det3 (b' - d) (a - d) u = β * T := by
    rw [hco]; simp only [hT_def, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have p_d_b'_c' : det3 (b' - d) (c' - d) u = (α + β - 1) * T := by
    rw [hco]; simp only [hT_def, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  -- edge `0 → 6`: the vertical face `046`
  have t01 : ∀ w, F.abc'.f w < 0 → 0 < σ * det3 (c' - a) (w - a) u := fun w hw =>
    det3_pos_of_combo_σ F.abc'.hN F.abc'.hN F.abc'.hP F.abc'.hR F.abc'.hP F.abc'.hR
      (α := 1) (β := 0) (by rw [hNu F.abc'.hN, F.abc'.hP, F.abc'.hQ]; ring) (r := b')
      hσT (by linarith) (by linarith)
  have t01c := t01 c f046c
  -- edge `1 → 0`: the vertical face `014`
  have t40 : ∀ w, F.abc.f w < 0 → 0 < σ * det3 (a - c) (w - c) u := fun w hw =>
    det3_pos_of_combo_σ F.abc.hN F.abc.hN F.abc.hR F.abc.hP F.abc.hR F.abc.hP
      (α := 1) (β := 0) (by rw [hNu F.abc.hN, F.abc.hP, F.abc.hQ]; ring) (r := c')
      (by rw [← det3_cyc]; exact t01c) (by linarith) (by linarith)
  have t40b' := t40 b' f014b'
  -- edge `5 → 1`: the faces `135` (up) and `015` (down)
  have t34 : ∀ w, (-F.ab'c.f b) * F.a'b'c.f w + (F.a'b'c.f b - F.a'b'c.f a) * F.ab'c.f w < 0 →
      0 < σ * det3 (c - b') (w - b') u := fun w hw =>
    det3_pos_of_combo_σ F.a'b'c.hN F.ab'c.hN F.a'b'c.hQ F.a'b'c.hR F.ab'c.hQ F.ab'c.hR
      (by rw [hNu F.a'b'c.hN, hNu F.ab'c.hN, F.ab'c.hP]; ring) (r := a)
      (by rw [← det3_cyc]; exact t40b')
      (by rw [F.ab'c.hP, mul_zero, add_zero]; exact mul_neg_of_pos_of_neg (by linarith) f135a) hw
  -- edge `6 → 2`: the faces `2346` (up) and `0256` (down)
  have t12 : ∀ w, (-F.ab'c'.f b) * F.a'bc'.f w + (-F.a'bc'.f a) * F.ab'c'.f w < 0 →
      0 < σ * det3 (d - c') (w - c') u := fun w hw =>
    det3_pos_of_combo_σ F.a'bc'.hN F.ab'c'.hN F.a'bc'.hR hd.a'bc' F.ab'c'.hR hd.ab'c'
      (by rw [hNu F.a'bc'.hN, hNu F.ab'c'.hN, F.a'bc'.hQ, F.ab'c'.hP]; ring) (r := a)
      (by rw [p_c'_d_a, show σ * (α * T) = α * (σ * T) by ring]; exact mul_pos hα0 hσT)
      (by rw [F.ab'c'.hP, mul_zero, add_zero]; exact mul_neg_of_pos_of_neg (by linarith) f346a) hw
  -- edge `2 → 5`: the faces `235` (up) and `0256` (down)
  have t23 : ∀ w, (-F.ab'c'.f b) * hd.f235.f w + (hd.f235.f b - hd.f235.f a) * F.ab'c'.f w < 0 →
      0 < σ * det3 (b' - d) (w - d) u := fun w hw =>
    det3_pos_of_combo_σ hd.f235.hN F.ab'c'.hN hd.f235.hR hd.f235.hP hd.ab'c' F.ab'c'.hQ
      (by rw [hNu hd.f235.hN, hNu F.ab'c'.hN, F.ab'c'.hP]; ring) (r := a)
      (by rw [p_d_b'_a, show σ * (β * T) = β * (σ * T) by ring]; exact mul_pos hβ hσT)
      (by rw [F.ab'c'.hP, mul_zero, add_zero]; exact mul_neg_of_pos_of_neg (by linarith) f235a) hw
  -- the twenty tests
  have hB135 : 0 < F.a'b'c.f b - F.a'b'c.f a := by linarith [hiii.1]
  have hB235 : 0 < hd.f235.f b - hd.f235.f a := by linarith [hiii.2]
  have T01d := t01 d hd.abc'
  have T01a' := t01 a' f046a'
  have T12b' := t12 b' (by
      rw [F.ab'c'.hQ, mul_zero, add_zero]
      exact mul_neg_of_pos_of_neg (by linarith) f346b')
  have T12c := by
    have k1 := mul_neg_of_pos_of_neg (neg_pos.mpr f056b) f346c
    have k2 := mul_neg_of_pos_of_neg (neg_pos.mpr f346a) f056c
    exact t12 c (by linarith)
  have T12a : 0 < σ * det3 (d - c') (a - c') u := by
    rw [p_c'_d_a, show σ * (α * T) = α * (σ * T) by ring]; exact mul_pos hα0 hσT
  have T12a' := t12 a' (by
      rw [F.a'bc'.hP, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg (by linarith) f056a')
  have T23c := by
    have k1 := mul_neg_of_pos_of_neg (neg_pos.mpr f056b) f235c
    have k2 := mul_neg_of_pos_of_neg hB235 f056c
    exact t23 c (by linarith)
  have T23a : 0 < σ * det3 (b' - d) (a - d) u := by
    rw [p_d_b'_a, show σ * (β * T) = β * (σ * T) by ring]; exact mul_pos hβ hσT
  have T23c' : 0 < σ * det3 (b' - d) (c' - d) u := by
    rw [p_d_b'_c', show σ * ((α + β - 1) * T) = (α + β - 1) * (σ * T) by ring]
    exact mul_pos (by linarith) hσT
  have T23a' := t23 a' (by
      rw [hd.f235.hQ, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg hB235 f056a')
  have T34a : 0 < σ * det3 (c - b') (a - b') u := by rw [← det3_cyc]; exact t40b'
  have T34c' := by
    have k1 := mul_neg_of_pos_of_neg (neg_pos.mpr f015b) f135c'
    have k2 := mul_neg_of_pos_of_neg hB135 f015c'
    exact t34 c' (by linarith)
  have T34d := by
    have k1 := mul_neg_of_pos_of_neg (neg_pos.mpr f015b) hd.a'b'c
    have k2 := mul_neg_of_pos_of_neg hB135 hd.ab'c
    exact t34 d (by linarith)
  have T34a' := t34 a' (by
      rw [F.a'b'c.hP, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg hB135 f015a')
  have T40c' := t40 c' f014c'
  have T40d := t40 d hd.abc
  have T40a' := t40 a' f014a'
  -- the coordinates of `1` over the plane of `0256` (Cramer)
  set D := det3 (b' - a) (c' - a) u with hD_def
  have hDT : D = -T := by simp only [hD_def, hT_def, det3_expand]; ring
  have hD : D ≠ 0 := by rw [hDT]; exact neg_ne_zero.mpr hT
  set p := det3 (c - a) (c' - a) u / D
  set q := det3 (b' - a) (c - a) u / D
  set ν := det3 (b' - a) (c' - a) (c - a) / D
  have hcm : c - a = p • (b' - a) + q • (c' - a) + ν • u := by
    have e := cramer (b' - a) (c' - a) u (c - a)
    have e1 : det3 (c - a) (c' - a) u = p * D := (div_mul_cancel₀ _ hD).symm
    have e2 : det3 (b' - a) (c - a) u = q * D := (div_mul_cancel₀ _ hD).symm
    have e3 : det3 (b' - a) (c' - a) (c - a) = ν * D := (div_mul_cancel₀ _ hD).symm
    rw [e1, e2, e3] at e
    refine smul_right_injective ℝ³ hD ?_
    simp only
    rw [e]; module
  have hc_rep : c = a + p • (b' - a) + q • (c' - a) + ν • u := by
    calc c = a + (c - a) := by abel
      _ = _ := by rw [hcm]; abel
  have hp : 0 < p := by
    have e : det3 (c' - a) (c - a) u = p * T := by
      rw [hcm, hT_def]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul]; ring
    have := t01c; rw [e, show σ * (p * T) = p * (σ * T) by ring] at this
    exact pos_of_mul_pos_left this hσT.le
  have hq : q < 0 := by
    have e : det3 (a - c) (b' - c) u = -(q * T) := by
      rw [← det3_cyc, hcm, hT_def]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul]; ring
    have := t40b'; rw [e, show σ * -(q * T) = -q * (σ * T) by ring] at this
    have := pos_of_mul_pos_left this hσT.le
    linarith
  have hconv : (p - 1) * β + q * (1 - α) < 0 := by
    have e : det3 (c - b') (d - b') u = -(((p - 1) * β + q * (1 - α)) * T) := by
      rw [hc_rep, hco, hT_def]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul]; ring
    have := T34d
    rw [e, show σ * -(((p - 1) * β + q * (1 - α)) * T) =
      -((p - 1) * β + q * (1 - α)) * (σ * T) by ring] at this
    have := pos_of_mul_pos_left this hσT.le
    linarith
  have hν : ν < 0 := by
    have k := F.ab'c'.hN c a
    rw [hcm, F.ab'c'.hP] at k
    simp only [inner_add_right, real_inner_smul_right] at k
    rw [← F.ab'c'.hN, ← F.ab'c'.hN, hNu F.ab'c'.hN, F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR] at k
    have k' : F.ab'c'.f c = ν * -F.ab'c'.f b := by linarith
    by_contra hc
    push Not at hc
    have : 0 ≤ ν * -F.ab'c'.f b := mul_nonneg hc (by linarith)
    linarith
  -- the depths
  have hz2 : ⟪d, u⟫ = ⟪a, u⟫ + α * (⟪b', u⟫ - ⟪a, u⟫) + β * (⟪c', u⟫ - ⟪a, u⟫) := by
    rw [hco]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have hz1 : ⟪c, u⟫ < ⟪a, u⟫ + p * (⟪b', u⟫ - ⟪a, u⟫) + q * (⟪c', u⟫ - ⟪a, u⟫) := by
    have e : ⟪c, u⟫ = ⟪a, u⟫ + p * (⟪b', u⟫ - ⟪a, u⟫) + q * (⟪c', u⟫ - ⟪a, u⟫) + ν * ⟪u, u⟫ := by
      rw [hc_rep]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
    have := mul_neg_of_neg_of_pos hν huu
    linarith
  have hA : 0 < (1 - α) * galeD G.l G.m c' a' - β * galeD G.l G.m a' b' := by linarith
  have hT1' : galeD G.l G.m a' b' * (⟪b', u⟫ - ⟪d, u⟫) +
      ((1 - α) * galeD G.l G.m c' a' - β * galeD G.l G.m a' b') * (⟪a, u⟫ - ⟪c', u⟫) < 0 := by
    have e : galeD G.l G.m a' b' * (⟪b', u⟫ - ⟪d, u⟫) +
        ((1 - α) * galeD G.l G.m c' a' - β * galeD G.l G.m a' b') * (⟪a, u⟫ - ⟪c', u⟫) =
        (1 - α) * ⟪u, axisView G.l G.m a' a b' c'⟫ := by
      rw [hz2]
      simp only [axisView, inner_add_right, real_inner_smul_right, inner_sub_right,
        galeD_anti G.l G.m c' a', real_inner_comm u]
      ring
    rw [e]
    exact mul_neg_of_pos_of_neg (by linarith) hT1
  -- distinct depths (`GenPos`)
  have hKa : a ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hdep : ∀ s t, s ∈ K → t ∈ K → s ≠ t → t ≠ b → t ≠ a → ⟪s, u⟫ ≠ ⟪t, u⟫ :=
    fun s t hs ht hst htb hta => hgen.inner_ne_of_ne hs ht hKb hKa hst (Ne.symm hab)
      (Or.inl ⟨htb, hta⟩)
  have hKc' : c' ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hinj := quint_injective (hdep a c' hKa hKc' hac' (Ne.symm hbc') (Ne.symm hac'))
    (hdep a d hKa hKd (Ne.symm hda) hdb hda) (hdep a b' hKa hKb' hab' (Ne.symm hbb') (Ne.symm hab'))
    (hdep a c hKa hKc hac (Ne.symm hbc) (Ne.symm hac))
    (hdep c' d hKc' hKd (Ne.symm hdc') hdb hda) (hdep c' b' hKc' hKb' (Ne.symm hb'c')
      (Ne.symm hbb') (Ne.symm hab')) (hdep c' c hKc' hKc (Ne.symm hcc') (Ne.symm hbc) (Ne.symm hac))
    (hdep d b' hKd hKb' hdb' (Ne.symm hbb') (Ne.symm hab')) (hdep d c hKd hKc hdc (Ne.symm hbc)
      (Ne.symm hac)) (hdep b' c hKb' hKc hb'c (Ne.symm hbc) (Ne.symm hac))
  have hz : IsCyclicUnimodal fun i => ⟪quint a c' d b' c i, u⟫ := by
    have e : (fun i => ⟪quint a c' d b' c i, u⟫) =
        quint ⟪a, u⟫ ⟪c', u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ := by
      funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact type21_Y_unimodal hα0 hβ hα1 hαβ hp hq hconv hz2 hz1 hA s35 hT1' hinj
  -- the edge view
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isRupert_quint_rim K u hu hσ (h := 1) one_ne_zero (by rw [hu_def]; module) hKb
    (fun i => by rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> assumption)
    (fun i j hi hj => ?_) (fun y hy hyb hyx i => ?_) hz (noHDN_pair hnd hKb hKa (Ne.symm hab)).1
  · rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [T01d, hσT, t01c, T12b', T12c, T12a, T23c, T23a, T23c', T34a, T34c', T34d, T40c', T40d,
      t40b']
  · have hya' : y = a' := by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl (hyx 2)
      · exact absurd rfl (hyx 0)
      · rfl
      · exact absurd rfl hyb
      · exact absurd rfl (hyx 3)
      · exact absurd rfl (hyx 4)
      · exact absurd rfl (hyx 1)
    subst hya'
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [T01a', T12a', T23a', T34a', T40a']

/-! ### `T1` and Lemma 16.7 -/

/-- **Lemma 16.7 (F1)**, in the normalized class (so (i) `s_C = +1` holds).  Let (ii)
`{3 5} < [6 3]` (`δ_014(2) < δ_014(5)`), (iii) `0 → 4` a quad edge of `K − 6` (the faces
`135`, `235` face up along `4 − 0`), and (iv) hO2 `[3 4] < [1 3]` (the far end of `014` along
`u₁` is `4`).  Outside the special positions of `T1` (`P(3)` on the line `P(5) P(4)` along
`u₁`, ties among the depths of `0, 5, 3, 4` other than those of `QuadTie`, a horizontal double
normal at `u₁`) and those of the edge
views (`GenPos`, `NoHDNEdges`), `K` is Rupert: `T1` (the vertex crossing at `0` of `014`,
`0256`, with the middle `2`) or `Y` (the edge crossing along `04`) is unimodal. -/
theorem isRupert_type21_F1 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (h35 : 0 < galeD G.l G.m a' b')
    (h61 : 0 < galeD G.l G.m c' c) {α β : ℝ}
    (hα0 : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hco : d = a + α • (b' - a) + β • (c' - a))
    (hS : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m c' a')
    (hiii : F.a'b'c.f a < F.a'b'c.f b ∧ hd.f235.f a < hd.f235.f b)
    (hO2 : galeD G.l G.m a' b < galeD G.l G.m c a')
    (hP : det3 (b - b') (a' - b') (axisView G.l G.m a' a b' c') ≠ 0)
    (hz : QuadTie ⟪a, axisView G.l G.m a' a b' c'⟫ ⟪b', axisView G.l G.m a' a b' c'⟫
      ⟪a', axisView G.l G.m a' a b' c'⟫ ⟪b, axisView G.l G.m a' a b' c'⟫)
    (hnd₁ : NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) (axisView G.l G.m a' a b' c'))
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := type21_cross_signs F h35
  have s35 := h35
  have s61 := h61
  have anti := galeD_anti G.l G.m
  set u := axisView G.l G.m a' a b' c' with hu_def
  have hu : u = galeD G.l G.m a' b' • (b' - a) + galeD G.l G.m a' c' • (c' - a) := rfl
  have h36 : galeD G.l G.m a' c' = -galeD G.l G.m c' a' := anti c' a'
  have h63 : galeD G.l G.m a' b' < galeD G.l G.m c' a' := by
    have : (1 - α) * galeD G.l G.m a' b' < β * galeD G.l G.m a' b' :=
      mul_lt_mul_of_pos_right (by linarith) s35
    nlinarith
  -- `T1`: the vertex crossing at `0`, with `2` a middle over the side `0 → 5`
  have hmid : AxisExtra a' a b' b u d := by
    refine Or.inr (Or.inl ⟨α + β * galeD G.l G.m a' b' / galeD G.l G.m c' a',
      -(β / galeD G.l G.m c' a'), ?_, ?_, ?_, ?_⟩)
    · positivity
    · have : α + β * galeD G.l G.m a' b' / galeD G.l G.m c' a' =
          (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b') / galeD G.l G.m c' a' := by
        field_simp
      rw [this, div_lt_one s63]; exact hS
    · exact neg_ne_zero.mpr (div_ne_zero hβ.ne' s63.ne')
    · rw [hco, hu, h36]
      have : galeD G.l G.m c' a' ≠ 0 := s63.ne'
      match_scalars <;> field_simp <;> ring
  have hfar₁ : |galeD G.l G.m a' b'| < |galeD G.l G.m a' c'| := by
    rw [abs_of_pos s35, h36, abs_neg, abs_of_pos s63]; exact h63
  have hfar₂ : |galeD G.l G.m a' b| < |galeD G.l G.m a' c| := by
    rw [abs_of_pos s34, anti c a', abs_neg, abs_of_pos s13]; exact hO2
  have hT := isRupert_axisTest_robust F.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃ hfar₁ hfar₂ hP hz
    (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto)
    (fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | h
      · exact Or.inr hmid
      · left; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hnd₁
  rcases hT with hR | ⟨⟨s, t, μ, hs0, hs1, ht0, ht1, hm⟩, -, hsep⟩
  · exact hR
  replace hm : b' + t • (b - b') - (a + s • (a' - a)) = μ • u := hm
  replace hsep : DepthSep a a' b' b u := hsep
  -- `T1` failed: `μ ≥ 0` (Lemma 16.7 (a), (e)), so `{5, 4}` lies above `{0, 3}`
  set X := det3 (b' - a) (b - a) (a' - a)
  set Y := det3 (b' - a) (b - a) (c' - a)
  have hY : Y ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine F.ab'c.hN hab' F.ab'c.hP F.ab'c.hQ
      (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
    have := affine_zero_of_coplanar F.ab'c'.hN F.ab'c'.hP F.ab'c'.hQ F.ab'c'.hR hc (w := b) (by
      have e : det3 (b' - a) (c' - a) (b - a) = -Y := by
        simp only [Y, det3_expand, PiLp.sub_apply]; ring
      rw [e, h0, neg_zero])
    linarith [F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc']
  have k1 : -(s * X) = μ * (galeD G.l G.m a' c' * Y) := by
    have e := congrArg (fun x => det3 (b' - a) (b - a) x) hm
    simp only [hu, X, Y, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e
  have k2 : galeD G.l G.m c a' * X + galeD G.l G.m c c' * Y = 0 := by
    have hs := galeD_sum G.hl G.hm c
    have hv := (G.hl.galeD G.hm c).vsum
    rw [galeD_self] at hs hv
    have hv' : galeD G.l G.m c a' • (a' - a) + galeD G.l G.m c b • (b - a) +
        galeD G.l G.m c b' • (b' - a) + galeD G.l G.m c c' • (c' - a) = 0 := by
      linear_combination (norm := module) hv - hs • a
    have e := congrArg (fun x => det3 (b' - a) (b - a) x) hv'
    simp only [X, Y, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, PiLp.zero_apply] at e ⊢
    linear_combination e
  have hμ : 0 ≤ μ := by
    have e : (s * galeD G.l G.m c' c - μ * (galeD G.l G.m c' a' * galeD G.l G.m c a')) * Y = 0 := by
      rw [anti c c', h36] at *
      linear_combination -(galeD G.l G.m c a' * k1) - s * k2
    have e' := (mul_eq_zero.mp e).resolve_right hY
    by_contra hc
    push Not at hc
    nlinarith [mul_pos s63 s13]
  -- the depth separation is `{5, 4}` above `{0, 3}`
  have huu := real_inner_self_nonneg (x := u)
  have i1 := congrArg (fun w => ⟪w, u⟫) hm
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at i1
  have hba : ⟪a, u⟫ < ⟪b, u⟫ := by
    rcases hsep with h | h
    · exact lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le h (min_le_right _ _))
    · exfalso
      obtain ⟨e1, -⟩ := seg_bounds (x := ⟪a, u⟫) (y := ⟪a', u⟫) hs0 hs1
      obtain ⟨-, e2⟩ := seg_bounds (x := ⟪b', u⟫) (y := ⟪b, u⟫) ht0 ht1
      have := mul_nonneg hμ huu
      linarith
  exact isRupert_type21_Y F hd G h35 hα0 hβ hαβ hco hS hiii
    (by rw [inner_sub_left]; linarith) hgen hnd

end Minimality

end
