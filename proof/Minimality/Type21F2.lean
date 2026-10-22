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
  `cert_type21_F2`.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

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

/-- **Corollary 13.3 with a weak separation** (one test): if the diagonals `[a', a]`, `[b, b']`
are weakly depth-separated at `u`, their projections meet along `u` and along `v`,
`⟪u, v⟫ ≠ 0`, and `a', a, b, b'` are not coplanar (so the diagonals do not meet in space), then
`⟪u, v⟫ det(u, ā, b̄) det(v, ā, b̄) ≥ 0`. -/
theorem weakSep_det_sign {a a' b b' u v : ℝ³}
    (hsep : max ⟪a', u⟫ ⟪a, u⟫ ≤ min ⟪b, u⟫ ⟪b', u⟫ ∨ max ⟪b, u⟫ ⟪b', u⟫ ≤ min ⟪a', u⟫ ⟪a, u⟫)
    (hu : SegMeet a' a b b' u) (hv : SegMeet a' a b b' v) (huv : ⟪u, v⟫ ≠ 0)
    (hS : det3 (b - a') (a - a') (b' - b) ≠ 0) :
    0 ≤ ⟪u, v⟫ * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b)) := by
  obtain ⟨s, t, l, hs0, hs1, ht0, ht1, h1⟩ := hu
  obtain ⟨s', t', μ, hs0', hs1', ht0', ht1', h2⟩ := hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu0
  have key : ∀ (x : ℝ³) (k s t : ℝ), b + t • (b' - b) - (a' + s • (a - a')) = k • x →
      k * det3 x (a - a') (b' - b) = det3 (b - a') (a - a') (b' - b) := by
    intro x k s t h
    have e := congrArg (fun w => det3 w (a - a') (b' - b)) h
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e ⊢
    linear_combination -e
  have k1 := key u l s t h1
  have k2 := key v μ s' t' h2
  have hl : l ≠ 0 := by rintro rfl; rw [zero_mul] at k1; exact hS k1.symm
  have hμ : μ ≠ 0 := by rintro rfl; rw [zero_mul] at k2; exact hS k2.symm
  -- the weak sign: `l μ ⟪u, v⟫ ≥ 0`
  have i1 := congrArg (fun w => ⟪w, u⟫) h1
  have i2 := congrArg (fun w => ⟪w, u⟫) h2
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1 i2
  rw [real_inner_comm u v] at i2
  obtain ⟨e1, e2⟩ := seg_bounds (x := ⟪b, u⟫) (y := ⟪b', u⟫) ht0 ht1
  obtain ⟨e1', e2'⟩ := seg_bounds (x := ⟪b, u⟫) (y := ⟪b', u⟫) ht0' ht1'
  obtain ⟨d1, d2⟩ := seg_bounds (x := ⟪a', u⟫) (y := ⟪a, u⟫) hs0 hs1
  obtain ⟨d1', d2'⟩ := seg_bounds (x := ⟪a', u⟫) (y := ⟪a, u⟫) hs0' hs1'
  have hpos : 0 ≤ l * (μ * ⟪u, v⟫) := by
    rcases hsep with h | h
    · have p1 : 0 ≤ l * ⟪u, u⟫ := by linarith
      have p2 : 0 ≤ μ * ⟪u, v⟫ := by linarith
      have hl0 : 0 ≤ l := by
        by_contra hc; push Not at hc; linarith [mul_neg_of_neg_of_pos hc huu]
      exact mul_nonneg hl0 p2
    · have p1 : l * ⟪u, u⟫ ≤ 0 := by linarith
      have p2 : μ * ⟪u, v⟫ ≤ 0 := by linarith
      have hl0 : l ≤ 0 := by
        by_contra hc; push Not at hc; linarith [mul_pos hc huu]
      exact mul_nonneg_of_nonpos_of_nonpos hl0 p2
  have hstrict : 0 < l * μ * ⟪u, v⟫ := by
    rw [mul_assoc]
    exact lt_of_le_of_ne hpos (Ne.symm (mul_ne_zero hl (mul_ne_zero hμ huv)))
  set Du := det3 u (a - a') (b' - b)
  set Dv := det3 v (a - a') (b' - b)
  set S := det3 (b - a') (a - a') (b' - b)
  have e : (l * μ * ⟪u, v⟫) * (⟪u, v⟫ * (Du * Dv)) =
      (⟪u, v⟫ * (l * Du)) * (⟪u, v⟫ * (μ * Dv)) := by ring
  rw [k1, k2] at e
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg hstrict hc
  rw [e] at this
  linarith [mul_self_nonneg (⟪u, v⟫ * S)]

/-- The end of Corollary 13.3 for two tests sharing a diagonal, from the two sign facts. -/
theorem not_both_of_signs {a a' b b' c c' u v : ℝ³}
    (A : 0 ≤ ⟪u, v⟫ * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b)))
    (B : 0 ≤ ⟪v, u⟫ * (det3 v (a - a') (c' - c) * det3 u (a - a') (c' - c)))
    (hne : ⟪u, v⟫ ≠ 0)
    (hdet : det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b) *
      (det3 u (a - a') (c' - c) * det3 v (a - a') (c' - c)) < 0) : False := by
  rw [real_inner_comm u v] at B
  have hsq : 0 < ⟪u, v⟫ * ⟪u, v⟫ := mul_self_pos.mpr hne
  have := mul_nonneg A B
  have e : ⟪u, v⟫ * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b)) *
      (⟪u, v⟫ * (det3 v (a - a') (c' - c) * det3 u (a - a') (c' - c))) =
      (⟪u, v⟫ * ⟪u, v⟫) * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b) *
        (det3 u (a - a') (c' - c) * det3 v (a - a') (c' - c))) := by ring
  rw [e] at this
  nlinarith

/-- **The ties allowed at the two vertex tests of F2** (rims `b, p, b', q` at `u` and
`b, p', b', q'` at `v`): those of `QuadTie` at both, or at most one tie at each view, no tie at
one of them, and the two diagonal pairs not coplanar. -/
def F2Tie (K : Finset ℝ³) (b b' p q p' q' u v : ℝ³) : Prop :=
  (QuadTie ⟪b, u⟫ ⟪p, u⟫ ⟪b', u⟫ ⟪q, u⟫ ∧ QuadTie ⟪b, v⟫ ⟪p', v⟫ ⟪b', v⟫ ⟪q', v⟫) ∨
    (OneTieAt K u ∧ OneTieAt K v ∧ (NoTieAt K u ∨ NoTieAt K v) ∧
      det3 (p - b) (b' - b) (q - p) ≠ 0 ∧ det3 (p' - b) (b' - b) (q' - p') ≠ 0)

/-- **Lemma 16.9 (F2)**, type-21 labels (`a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`).  The
vertex crossings at `4`: `V = 014/2346` at `u_V = [5 0] (0 − 4) + [5 1] (1 − 4)` with the rim
`(4, 2, 5, 1)` (or the triangle `(4, 2, 1)`), `3` a middle over `4 → 2`, `0` over `4 → 1`, `6` a
middle or hidden; `V' = 046/134` at `u_V' = [5 0] (0 − 4) + [5 6] (6 − 4)` with the rim
`(4, 3, 5, 0)` (or the triangle), `1` a middle over `4 → 3`, `6` over `4 → 0`, `2` hidden or a
middle.  If the projections of `[2, 1]` and `[4, 5]` meet along `u_V'` and
`det(u_V, 5 − 4, 1 − 2) det(u_V', 5 − 4, 1 − 2) > 0`, then with the ties of `F2Tie` on the two
rims (those of `QuadTie` on both, or at most one tie at each view and a tie at no more than one
of them, with the equators `4 5 2 1`, `4 5 3 0` not planar), `K` has a rim certificate (`CertV`)
at `±u_V` or `±u_V'`: the two tests share the diagonal `[4, 5]`, and by Lemma 16.8 (a) the
four-determinant product of Corollary 13.3 is negative, so the two rims are not both
depth-separated; with one tie, a rim that is not robustly unimodal is weakly separated
(`weakSep_of_not_robust`), the rim without a tie strictly, and the weak sign (`weakSep_det_sign`)
gives the contradiction. -/
theorem cert_type21_F2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {σ₁ σ₂ s₁ δ₁ s₁' δ₁' s₂ δ₂ s₂' δ₂' : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hT₁ : 0 < σ₁ * det3 (d - b) (c - b) (axisView G.l G.m b' b a c))
    (hΓ₁ : 0 < σ₁ * det3 (d - b) (b' - b) (axisView G.l G.m b' b a c))
    (hB₁ : 0 < σ₁ * det3 (b' - b) (c - b) (axisView G.l G.m b' b a c))
    (hP₁ : det3 (c - d) (b' - d) (axisView G.l G.m b' b a c) ≠ 0)
    (hm₁ : 0 < s₁ ∧ s₁ < 1 ∧ δ₁ ≠ 0 ∧ a' = b + s₁ • (d - b) + δ₁ • axisView G.l G.m b' b a c)
    (hm₁' : 0 < s₁' ∧ s₁' < 1 ∧ δ₁' ≠ 0 ∧ a = b + s₁' • (c - b) + δ₁' • axisView G.l G.m b' b a c)
    (hX₁ : AxisExtra b' b d c (axisView G.l G.m b' b a c) c')

    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hT₂ : 0 < σ₂ * det3 (a' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hΓ₂ : 0 < σ₂ * det3 (a' - b) (b' - b) (axisView G.l G.m b' b a c'))
    (hB₂ : 0 < σ₂ * det3 (b' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hP₂ : det3 (a - a') (b' - a') (axisView G.l G.m b' b a c') ≠ 0)
    (hm₂ : 0 < s₂ ∧ s₂ < 1 ∧ δ₂ ≠ 0 ∧ c = b + s₂ • (a' - b) + δ₂ • axisView G.l G.m b' b a c')
    (hm₂' : 0 < s₂' ∧ s₂' < 1 ∧ δ₂' ≠ 0 ∧ c' = b + s₂' • (a - b) + δ₂' • axisView G.l G.m b' b a c')
    (hX₂ : AxisExtra b' b a' a (axisView G.l G.m b' b a c') d)

    (hmeet : SegMeet b b' d c (axisView G.l G.m b' b a c'))
    (hsign : 0 < det3 (axisView G.l G.m b' b a c) (b' - b) (c - d) *
      det3 (axisView G.l G.m b' b a c') (b' - b) (c - d))
    (hties : F2Tie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) b b' d c a' a
      (axisView G.l G.m b' b a c) (axisView G.l G.m b' b a c'))
    (hL₁ : L (σ₁ • axisView G.l G.m b' b a c)) (hL₂ : L (σ₂ • axisView G.l G.m b' b a c')) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  set u := axisView G.l G.m b' b a c with hu
  set v := axisView G.l G.m b' b a c' with hv
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  obtain ⟨hs₁0, hs₁1, hδ₁, hm₁⟩ := hm₁
  obtain ⟨hs₁0', hs₁1', hδ₁', hm₁'⟩ := hm₁'
  obtain ⟨hs₂0, hs₂1, hδ₂, hm₂⟩ := hm₂
  obtain ⟨hs₂0', hs₂1', hδ₂', hm₂'⟩ := hm₂'
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hbd : b ≠ d := by
    intro e
    have h0 : det3 (d - b) (c - b) u = 0 := by
      rw [← e, sub_self]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [h0, mul_zero] at hT₁; exact lt_irrefl _ hT₁
  have hdb' : d ≠ b' := by
    intro e
    have h0 : det3 (d - b) (b' - b) u = 0 := by
      rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h0, mul_zero] at hΓ₁; exact lt_irrefl _ hΓ₁
  have hdc : d ≠ c := by
    intro e
    have h0 : det3 (d - b) (c - b) u = 0 := by
      rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h0, mul_zero] at hT₁; exact lt_irrefl _ hT₁
  have htri₁ : ¬ (⟪b, u⟫ = ⟪d, u⟫ ∧ ⟪d, u⟫ = ⟪c, u⟫) := by
    rcases hties with ⟨q1, -⟩ | ⟨o1, -, -⟩
    · exact q1.2.1
    · rintro ⟨e1, e2⟩
      rcases o1 b hKb d hKd d hKd c hKc hbd hdc e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hbd h1
      · exact hbc h1
  have htri₂ : ¬ (⟪b, v⟫ = ⟪a', v⟫ ∧ ⟪a', v⟫ = ⟪a, v⟫) := by
    rcases hties with ⟨-, q2⟩ | ⟨-, o2, -⟩
    · exact q2.2.1
    · rintro ⟨e1, e2⟩
      rcases o2 b hKb a' hKa' a' hKa' a hKa (Ne.symm ha'b) (Ne.symm haa') e1 e2 with
        ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ha'b h1.symm
      · exact hab h1.symm
  -- the test `V` at `u` (core labels `(b', b, d, c)`)
  obtain ⟨K1, K2⟩ := rimCert_axisTest_core_gen hσ₁ hT₁ hΓ₁ hB₁ htri₁ K (by simp [hK])
    (by simp [hK]) (by simp [hK]) (by simp [hK]) (fun x hx => by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s₁', δ₁', hs₁0', hs₁1', hδ₁', hm₁'⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s₁, δ₁, hs₁0, hs₁1, hδ₁, hm₁⟩)))))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hX₁))))
  -- the test `V'` at `v` (core labels `(b', b, a', a)`)
  obtain ⟨L1, L2⟩ := rimCert_axisTest_core_gen hσ₂ hT₂ hΓ₂ hB₂ htri₂ K (by simp [hK])
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
          hm₂'⟩))))))
  have hσσ₁ : σ₁ ≠ 0 := by rcases hσ₁ with rfl | rfl <;> norm_num
  have hσσ₂ : σ₂ ≠ 0 := by rcases hσ₂ with rfl | rfl <;> norm_num
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₁ hP₁) with hα₁ | hα₁
  swap; · exact CertV.line hL₁ (K1 hα₁)
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₂ hP₂) with hα₂ | hα₂
  swap; · exact CertV.line hL₂ (L1 hα₂)
  by_cases hR1 : IsRobustUnimodal (quad ⟪b, u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫)
  · exact CertV.line hL₁ (K2 hα₁ hR1)
  by_cases hR2 : IsRobustUnimodal (quad ⟪b, v⟫ ⟪a', v⟫ ⟪b', v⟫ ⟪a, v⟫)
  · exact CertV.line hL₂ (L2 hα₂ hR2)
  exfalso
  obtain ⟨m1u, m2u⟩ := axisTest_meets hσ₁ hs₁0 hs₁1 hm₁ hs₁0' hs₁1' hm₁' hT₁ hΓ₁ hB₁ hα₁
  obtain ⟨m2v, -⟩ := axisTest_meets hσ₂ hs₂0 hs₂1 hm₂ hs₂0' hs₂1' hm₂' hT₂ hΓ₂ hB₂ hα₂
  have h08 := vertex_sep F.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃
  have hdet := mul_neg_of_pos_of_neg hsign h08
  have nd1 : [b, d, b', c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hbd, hbb', hbc⟩, ⟨hdb', hdc⟩, hb'c, not_false⟩
  have nd2 : [b, a', b', a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm ha'b, hbb', Ne.symm hab⟩, ⟨ha'b', Ne.symm haa'⟩, Ne.symm hab', not_false⟩
  rcases hties with ⟨q1, q2⟩ | ⟨o1, o2, hno, hS1, hS2⟩
  · -- the ties of `QuadTie`: both diagonals strictly separated
    have hs1 : DepthSep b b' d c u := by
      by_contra hc
      exact hR1 (isRobustUnimodal_quad q1 (fun h => hc (Or.inr h)) (fun h => hc (Or.inl h)))
    have hs2 : DepthSep b b' a' a v := by
      by_contra hc
      exact hR2 (isRobustUnimodal_quad q2 (fun h => hc (Or.inr h)) (fun h => hc (Or.inl h)))
    exact not_both_depthSep hs1 hs2 m1u hmeet m2v m2u hdet
  · -- one tie: weak separations, one of them strict
    have W1 := weakSep_of_not_robust (o1.oneTie4 hKb hKd hKb' hKc nd1) hR1
    have W2 := weakSep_of_not_robust (o2.oneTie4 hKb hKa' hKb' hKa nd2) hR2
    rcases hno with n1 | n2
    · have hs1 : DepthSep b b' d c u := by
        rcases W1 with w | w
        · exact Or.inr (lt_of_le_of_noTie n1 hKd hKc hKb hKb' (Ne.symm hbd) hdb' (Ne.symm hbc)
            (Ne.symm hb'c) w)
        · exact Or.inl (lt_of_le_of_noTie n1 hKb hKb' hKd hKc hbd hbc (Ne.symm hdb') hb'c w)
      obtain ⟨A, hne⟩ := depthSep_det_sign hs1 m1u hmeet
      have hne' : ⟪v, u⟫ ≠ 0 := by rw [real_inner_comm]; exact hne
      exact not_both_of_signs A (weakSep_det_sign W2.symm m2v m2u hne' hS2) hne hdet
    · have hs2 : DepthSep b b' a' a v := by
        rcases W2 with w | w
        · exact Or.inr (lt_of_le_of_noTie n2 hKa' hKa hKb hKb' ha'b ha'b' hab hab' w)
        · exact Or.inl (lt_of_le_of_noTie n2 hKb hKb' hKa' hKa (Ne.symm ha'b) (Ne.symm hab)
            (Ne.symm ha'b') (Ne.symm hab') w)
      obtain ⟨B, hne'⟩ := depthSep_det_sign hs2 m2v m2u
      have hne : ⟪u, v⟫ ≠ 0 := by rw [real_inner_comm]; exact hne'
      exact not_both_of_signs (weakSep_det_sign W1.symm m1u hmeet hne hS1) B hne hdet

end Minimality

end
