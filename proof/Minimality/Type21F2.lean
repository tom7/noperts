module

public import Minimality.Type21F1

@[expose] public section

/-!
# Type 21: the tier F2 (`FEWER-FACES-PROOFS.md` Lemmas 16.8 (a), 16.9)

* **Lemma 16.8 (a) (vertex separation, every octahedron)** — `vertex_sep`: at a vertex `b'`
  with antipode `b`, the views of the two vertex crossings `V = (b'a'c', b'ac)` and
  `V' = (b'a'c, b'ac')`, `u_V = [b a'] (a' − b') + [b c'] (c' − b')` and
  `u_V' = [b a'] (a' − b') + [b c] (c − b')`, are separated by `a a'` seen along the axis:
  `det(u_V, b − b', a' − a) det(u_V', b − b', a' − a) < 0`.  In the frame `b'; a', c', a` the
  dependencies `[b ·]`, `[c ·]` give the coordinates of `c`, `b`; the two determinants are
  `V₀ / [c b]` times `[b c] [a' c'] − [b c'] [c a] < 0` and `[b c'] [c a'] + [b c] [c' a] > 0`
  (Plücker and Lemma 13.4).
* **Lemma 16.9 (F2)** — `isRupert_F2`: two vertex tests at `b'` sharing the diagonal
  `[b', b]`; if both rims are quadrilaterals whose diagonals are depth-separated, the angle
  lemma in the shared-diagonal form (`not_both_depthSep`) and 16.8 (a) give a contradiction,
  given the sign of the other factor (the hypothesis of 16.9).  For type 21 (`b' = 4`, `b = 5`,
  `a = 3`, `a' = 0`, `c = 6`, `c' = 1`, `V = 014/2346`, `V' = 046/134`):
  `isRupert_type21_F2`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Lemma 16.8 (a)** (every octahedron): seen along the axis `b b'`, the views of the two
vertex crossings at `b'` are separated by `a a'`. -/
theorem vertex_sep {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') :
    det3 (axisView G.l G.m b b' a' c') (b - b') (a' - a) *
      det3 (axisView G.l G.m b b' a' c) (b - b') (a' - a) < 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have anti := galeD_anti G.l G.m
  -- the frame `b'; a', c', a`
  set V₀ := det3 (a' - b') (c' - b') (a - b') with hV₀
  have hV : V₀ ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine F.a'b'c.hN ha'b' F.a'b'c.hP F.a'b'c.hQ
      (F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'))
    have := affine_zero_of_coplanar F.a'b'c'.hN F.a'b'c'.hP F.a'b'c'.hQ F.a'b'c'.hR hc (w := a) (by
      have e : det3 (b' - a') (c' - a') (a - a') = -V₀ := by
        simp only [hV₀, det3_expand, PiLp.sub_apply]; ring
      rw [e, h0, neg_zero])
    linarith [F.a'b'c'.neg a (by simp) haa' hab' hac']
  -- the coordinates of `c` and `b` (the dependencies `[b ·]`, `[c ·]`)
  have hsb := galeD_sum G.hl G.hm b
  have hvb := (G.hl.galeD G.hm b).vsum
  have hsc := galeD_sum G.hl G.hm c
  have hvc := (G.hl.galeD G.hm c).vsum
  rw [galeD_self] at hsb hvb hsc hvc
  have kc : galeD G.l G.m b c • (c - b') = -(galeD G.l G.m b a • (a - b') +
      galeD G.l G.m b a' • (a' - b') + galeD G.l G.m b c' • (c' - b')) := by
    linear_combination (norm := module) hvb - hsb • b'
  have kb : galeD G.l G.m c b • (b - b') = -(galeD G.l G.m c a • (a - b') +
      galeD G.l G.m c a' • (a' - b') + galeD G.l G.m c c' • (c' - b')) := by
    linear_combination (norm := module) hvc - hsc • b'
  have hu' : axisView G.l G.m b b' a' c = -(galeD G.l G.m b a • (a - b') +
      galeD G.l G.m b c' • (c' - b')) := by
    simp only [axisView]; rw [kc]; module
  set D₁ := det3 (axisView G.l G.m b b' a' c') (b - b') (a' - a)
  set D₂ := det3 (axisView G.l G.m b b' a' c) (b - b') (a' - a)
  have e₁ : galeD G.l G.m c b * D₁ = V₀ * (galeD G.l G.m b a' * galeD G.l G.m c c' -
      galeD G.l G.m b c' * galeD G.l G.m c a' - galeD G.l G.m b c' * galeD G.l G.m c a) := by
    have : galeD G.l G.m c b * D₁ = det3 (axisView G.l G.m b b' a' c')
        (galeD G.l G.m c b • (b - b')) ((a' - b') - (a - b')) := by
      simp only [D₁, det3_expand, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [this, kb]
    simp only [hV₀, axisView, det3_expand, PiLp.add_apply, PiLp.neg_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]; ring
  have e₂ : galeD G.l G.m c b * D₂ = V₀ * (galeD G.l G.m b c' * galeD G.l G.m c a' +
      galeD G.l G.m b c' * galeD G.l G.m c a - galeD G.l G.m b a * galeD G.l G.m c c') := by
    have : galeD G.l G.m c b * D₂ = det3 (axisView G.l G.m b b' a' c)
        (galeD G.l G.m c b • (b - b')) ((a' - b') - (a - b')) := by
      simp only [D₂, det3_expand, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [this, kb, hu']
    simp only [hV₀, det3_expand, PiLp.add_apply, PiLp.neg_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]; ring
  -- the signs (Plücker and Lemma 13.4)
  have p1 := galeD_plucker G.l G.m b a' c c'
  have p2 := galeD_plucker G.l G.m b a c c'
  obtain ⟨⟨A1, A2, A3⟩, ⟨A1', A2', A3'⟩, AB, -⟩ := cluster_signs F G
  obtain ⟨⟨B1, B2, B3⟩, -, -, -⟩ := cluster_signs F.perm₁₂ G.perm₁₂
  dsimp only [GaleData.perm₁₂] at B1 B2 B3
  have hcb : galeD G.l G.m c b ≠ 0 := by
    rw [anti]; exact neg_ne_zero.mpr (galeD_ne_zero F.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃)
  set M₁ := galeD G.l G.m b a' * galeD G.l G.m c c' -
      galeD G.l G.m b c' * galeD G.l G.m c a' - galeD G.l G.m b c' * galeD G.l G.m c a
  set M₂ := galeD G.l G.m b c' * galeD G.l G.m c a' +
      galeD G.l G.m b c' * galeD G.l G.m c a - galeD G.l G.m b a * galeD G.l G.m c c'
  have hM₁ : M₁ = galeD G.l G.m b c * galeD G.l G.m a' c' -
      galeD G.l G.m b c' * galeD G.l G.m c a := by
    simp only [M₁]; linear_combination p1 - galeD G.l G.m b c' * anti c a'
  have hM₂ : M₂ = galeD G.l G.m b c' * galeD G.l G.m c a' +
      galeD G.l G.m b c * galeD G.l G.m c' a := by
    simp only [M₂]
    linear_combination -p2 - galeD G.l G.m b c * anti c' a + galeD G.l G.m b c' * anti c a
  -- `σA = sign [a b]` fixes every sign
  have hM₁n : M₁ * M₂ < 0 := by
    rw [hM₁, hM₂]
    have hab0 : galeD G.l G.m a b ≠ 0 := galeD_ne_zero F G
    have eba := anti a b
    have eca := anti a c
    have eca' := anti a' c
    have ec'a := anti a c'
    rcases lt_or_gt_of_ne hab0 with h | h
    · have hac : 0 < galeD G.l G.m a c := pos_of_mul_neg_right A3 h.le
      have hac' : 0 < galeD G.l G.m a c' := pos_of_mul_pos_right A2 hac.le
      have ha'b : galeD G.l G.m a' b < 0 := neg_of_mul_pos_right AB h.le
      have ha'c : 0 < galeD G.l G.m a' c := pos_of_mul_neg_right A3' ha'b.le
      have ha'c' : 0 < galeD G.l G.m a' c' := pos_of_mul_pos_right A2' ha'c.le
      have hba : 0 < galeD G.l G.m b a := by rw [eba]; linarith
      have hbc : galeD G.l G.m b c < 0 := neg_of_mul_neg_right B3 hba.le
      have hbc' : galeD G.l G.m b c' < 0 := neg_of_mul_pos_right B2 hbc.le
      have m1 : galeD G.l G.m b c * galeD G.l G.m a' c' - galeD G.l G.m b c' * galeD G.l G.m c a
          < 0 := by
        rw [eca]; linarith only [mul_neg_of_neg_of_pos hbc ha'c', mul_neg_of_neg_of_pos hbc' hac]
      have m2 : 0 < galeD G.l G.m b c' * galeD G.l G.m c a' + galeD G.l G.m b c * galeD G.l G.m c' a
          := by
        rw [eca', ec'a]
        linarith only [mul_neg_of_neg_of_pos hbc' ha'c, mul_neg_of_neg_of_pos hbc hac']
      exact mul_neg_of_neg_of_pos m1 m2
    · have hac : galeD G.l G.m a c < 0 := neg_of_mul_neg_right A3 h.le
      have hac' : galeD G.l G.m a c' < 0 := neg_of_mul_pos_right A2 hac.le
      have ha'b : 0 < galeD G.l G.m a' b := pos_of_mul_pos_right AB h.le
      have ha'c : galeD G.l G.m a' c < 0 := neg_of_mul_neg_right A3' ha'b.le
      have ha'c' : galeD G.l G.m a' c' < 0 := neg_of_mul_pos_right A2' ha'c.le
      have hba : galeD G.l G.m b a < 0 := by rw [eba]; linarith
      have hbc : 0 < galeD G.l G.m b c := pos_of_mul_neg_right B3 hba.le
      have hbc' : 0 < galeD G.l G.m b c' := pos_of_mul_pos_right B2 hbc.le
      have m1 : galeD G.l G.m b c * galeD G.l G.m a' c' - galeD G.l G.m b c' * galeD G.l G.m c a
          < 0 := by
        rw [eca]; linarith only [mul_neg_of_pos_of_neg hbc ha'c', mul_neg_of_pos_of_neg hbc' hac]
      have m2 : 0 < galeD G.l G.m b c' * galeD G.l G.m c a' + galeD G.l G.m b c * galeD G.l G.m c' a
          := by
        rw [eca', ec'a]
        linarith only [mul_neg_of_pos_of_neg hbc' ha'c, mul_neg_of_pos_of_neg hbc hac']
      exact mul_neg_of_neg_of_pos m1 m2
  have key : (galeD G.l G.m c b * D₁) * (galeD G.l G.m c b * D₂) = V₀ * V₀ * (M₁ * M₂) := by
    rw [e₁, e₂]; ring
  have hsq : 0 < galeD G.l G.m c b * galeD G.l G.m c b := mul_self_pos.mpr hcb
  have hV2 : 0 < V₀ * V₀ := mul_self_pos.mpr hV
  have : (galeD G.l G.m c b * galeD G.l G.m c b) * (D₁ * D₂) < 0 := by
    have e : (galeD G.l G.m c b * galeD G.l G.m c b) * (D₁ * D₂) = V₀ * V₀ * (M₁ * M₂) := by
      rw [← key]; ring
    rw [e]; exact mul_neg_of_pos_of_neg hV2 hM₁n
  exact neg_of_mul_neg_right this hsq.le

/-- **Lemma 16.9 (F2)**, type-21 labels (`a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`).  The
vertex crossings at `4`: `V = 014/2346` at `u_V = [5 0] (0 − 4) + [5 1] (1 − 4)` with the rim
`(4, 2, 5, 1)` (or the triangle `(4, 2, 1)`), `3` a middle over `4 → 2`, `0` over `4 → 1`, `6` a
middle or hidden; `V' = 046/134` at `u_V' = [5 0] (0 − 4) + [5 6] (6 − 4)` with the rim
`(4, 3, 5, 0)` (or the triangle), `1` a middle over `4 → 3`, `6` over `4 → 0`, `2` hidden or a
middle.  If the projections of `[2, 1]` and `[4, 5]` meet along `u_V'` and
`det(u_V, 5 − 4, 1 − 2) det(u_V', 5 − 4, 1 − 2) > 0`, then with distinct depths on both rims and
no horizontal double normals at `u_V`, `u_V'`, `K` is Rupert: the two tests share the diagonal
`[4, 5]`, and by Lemma 16.8 (a) the four-determinant product of Corollary 13.3 is negative. -/
theorem isRupert_type21_F2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {σ₁ σ₂ s₁ δ₁ s₁' δ₁' s₂ δ₂ s₂' δ₂' : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hT₁ : 0 < σ₁ * det3 (d - b) (c - b) (axisView G.l G.m b' b a c))
    (hΓ₁ : 0 < σ₁ * det3 (d - b) (b' - b) (axisView G.l G.m b' b a c))
    (hB₁ : 0 < σ₁ * det3 (b' - b) (c - b) (axisView G.l G.m b' b a c))
    (hP₁ : det3 (c - d) (b' - d) (axisView G.l G.m b' b a c) ≠ 0)
    (hm₁ : 0 < s₁ ∧ s₁ < 1 ∧ δ₁ ≠ 0 ∧ a' = b + s₁ • (d - b) + δ₁ • axisView G.l G.m b' b a c)
    (hm₁' : 0 < s₁' ∧ s₁' < 1 ∧ δ₁' ≠ 0 ∧ a = b + s₁' • (c - b) + δ₁' • axisView G.l G.m b' b a c)
    (hX₁ : AxisExtra b' b d c (axisView G.l G.m b' b a c) c')
    (hz₁ : [⟪b, axisView G.l G.m b' b a c⟫, ⟪d, axisView G.l G.m b' b a c⟫,
      ⟪b', axisView G.l G.m b' b a c⟫, ⟪c, axisView G.l G.m b' b a c⟫].Nodup)
    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hT₂ : 0 < σ₂ * det3 (a' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hΓ₂ : 0 < σ₂ * det3 (a' - b) (b' - b) (axisView G.l G.m b' b a c'))
    (hB₂ : 0 < σ₂ * det3 (b' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hP₂ : det3 (a - a') (b' - a') (axisView G.l G.m b' b a c') ≠ 0)
    (hm₂ : 0 < s₂ ∧ s₂ < 1 ∧ δ₂ ≠ 0 ∧ c = b + s₂ • (a' - b) + δ₂ • axisView G.l G.m b' b a c')
    (hm₂' : 0 < s₂' ∧ s₂' < 1 ∧ δ₂' ≠ 0 ∧ c' = b + s₂' • (a - b) + δ₂' • axisView G.l G.m b' b a c')
    (hX₂ : AxisExtra b' b a' a (axisView G.l G.m b' b a c') d)
    (hz₂ : [⟪b, axisView G.l G.m b' b a c'⟫, ⟪a', axisView G.l G.m b' b a c'⟫,
      ⟪b', axisView G.l G.m b' b a c'⟫, ⟪a, axisView G.l G.m b' b a c'⟫].Nodup)
    (hmeet : SegMeet b b' d c (axisView G.l G.m b' b a c'))
    (hsign : 0 < det3 (axisView G.l G.m b' b a c) (b' - b) (c - d) *
      det3 (axisView G.l G.m b' b a c') (b' - b) (c - d))
    (hnd₁ : NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) (axisView G.l G.m b' b a c))
    (hnd₂ : NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
      (axisView G.l G.m b' b a c')) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  set u := axisView G.l G.m b' b a c with hu
  set v := axisView G.l G.m b' b a c' with hv
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz₁ hz₂
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz₁
  obtain ⟨⟨w1, w2, w3⟩, ⟨w4, w5⟩, w6, -⟩ := hz₂
  obtain ⟨hs₁0, hs₁1, hδ₁, hm₁⟩ := hm₁
  obtain ⟨hs₁0', hs₁1', hδ₁', hm₁'⟩ := hm₁'
  obtain ⟨hs₂0, hs₂1, hδ₂, hm₂⟩ := hm₂
  obtain ⟨hs₂0', hs₂1', hδ₂', hm₂'⟩ := hm₂'
  -- the test `V` at `u` (core labels `(b', b, d, c)`)
  obtain ⟨K1, K2⟩ := isRupert_axisTest_core hσ₁ hT₁ hΓ₁ hB₁ ⟨z1, z3, z5⟩ K (by simp [hK])
    (by simp [hK]) (by simp [hK]) (by simp [hK]) (fun x hx => by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s₁', δ₁', hs₁0', hs₁1', hδ₁', hm₁'⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s₁, δ₁, hs₁0, hs₁1, hδ₁, hm₁⟩)))))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hX₁)))) hnd₁
  -- the test `V'` at `v` (core labels `(b', b, a', a)`)
  obtain ⟨L1, L2⟩ := isRupert_axisTest_core hσ₂ hT₂ hΓ₂ hB₂ ⟨w1, w3, w5⟩ K (by simp [hK])
    (by simp [hK]) (by simp [hK]) (by simp [hK]) (fun x hx => by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr hX₂)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s₂, δ₂, hs₂0, hs₂1, hδ₂, hm₂⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s₂', δ₂', hs₂0', hs₂1', hδ₂',
          hm₂'⟩)))))) hnd₂
  have hσσ₁ : σ₁ ≠ 0 := by rcases hσ₁ with rfl | rfl <;> norm_num
  have hσσ₂ : σ₂ ≠ 0 := by rcases hσ₂ with rfl | rfl <;> norm_num
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₁ hP₁) with hα₁ | hα₁
  swap; · exact K1 hα₁
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₂ hP₂) with hα₂ | hα₂
  swap; · exact L1 hα₂
  by_cases hs1 : DepthSep b b' d c u
  swap; · exact K2 hα₁ z2 z4 z6 hs1
  by_cases hs2 : DepthSep b b' a' a v
  swap; · exact L2 hα₂ w2 w4 w6 hs2
  exfalso
  obtain ⟨m1u, m2u⟩ := axisTest_meets hσ₁ hs₁0 hs₁1 hm₁ hs₁0' hs₁1' hm₁' hT₁ hΓ₁ hB₁ hα₁
  obtain ⟨m2v, -⟩ := axisTest_meets hσ₂ hs₂0 hs₂1 hm₂ hs₂0' hs₂1' hm₂' hT₂ hΓ₂ hB₂ hα₂
  have h08 := vertex_sep F.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃
  refine not_both_depthSep hs1 hs2 m1u hmeet m2v m2u ?_
  exact mul_neg_of_pos_of_neg hsign h08

end Minimality

end
