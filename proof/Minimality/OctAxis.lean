module

public import Minimality.Type29

@[expose] public section

/-!
# Two-test certificates: the angle lemma and the octahedral axis lemma (§13)

`FEWER-FACES-PROOFS.md` §13, in Euclidean form: the metric is the one of `ℝ³` (the paper's
"for every metric" is not needed, since a point set's own inner product is one metric), and
the depth along a view `u` is `⟪·, u⟫`.  `[s t] = galeD G.l G.m s t` for Gale data `G`.

* **The angle lemma** (Lemma 13.2 and Corollary 13.3, for 4-corner rims): with distinct
  depths a 4-corner rim is unimodal unless its diagonals are depth-separated (`DepthSep`,
  both ends of one above both ends of the other; `overlap4_of_not_depthSep`).  If the
  projections of the diagonals meet along `u` and along `v` (`SegMeet`), separation at `u`
  forces `λ μ ⟪u, v⟫ > 0` for the two meeting parameters (`depthSep_meet_sign`), in the
  shared-diagonal form `⟪u, v⟫ det(u, ā, s̄) det(v, ā, s̄) ≥ 0` with `⟪u, v⟫ ≠ 0`
  (`depthSep_det_sign`); two tests sharing the diagonal `A` whose four determinants have a
  negative product are not both depth-separated (`not_both_depthSep`).
* **Lemma 13.4 (cluster signs, every octahedron)** — `cluster_signs`, after
  `dep_eq_zero_of_two` (a dependency vanishing at two adjacent vertices vanishes),
  `galeD_ne_zero` (`[s t] ≠ 0` for adjacent `s, t`) and `pole_signs'`.  No planar-equator
  exclusion.
* **Lemma 13.5 (views and far ends)** — the view `u₁ = [a b] (b − a') + [a c] (c − a')` of the
  vertex crossing at `a'` (`axisView`), its second form `axisView_eq_neg`, and, under the
  far-end inequalities, the middles `c`, `c'` over the sides at `a'` with the screen
  orientation (`axis_test_facts`).  The view of the crossing at `a` is
  `u₂ = axisView G.l G.m a' a c' b = [a' c'] (c' − a) + [a' b] (b − a)` (the paper's `u₂` up to
  sign, which does not matter).
* **Lemma 13.6 (sign identity)** — `axis_sign`, `axis_sign_two`: applying the dependencies
  `[a ·]`, `[b ·]` to the linear function `det(u₁, ā, ·)` and the Plücker relation; no division
  by `[a a']`, so the paper's continuity step is not needed.
* **The test** — `isRupert_of_vertexView` (Proposition 8.8 with Theorem 7.3 from determinant
  tests, through `isRupert_of_chords_unimodal`); `isRupert_axisTest_core`: the rim is the
  triangle `a' b b'` (unimodal with distinct depths) or the quadrilateral `a' b a b'`
  (unimodal unless its diagonals are depth-separated); extra points that are hidden or middles
  at the apex (`AxisExtra`: `AxisHidden`, `ApexMid`) are allowed.  `axisTest_meets` (via
  `segMeet_of_sides`) gives the crossings of the diagonals used by Corollary 13.3, and
  `isRupert_axisTest` packages one test of an octahedron.
* **Theorem 13.7 (the octahedral axis lemma)** — `isRupert_octAxis_gen` (with admissible extra
  points), `isRupert_octAxis` (the octahedron), and **the lift** `isRupert_octAxis_lift`
  (Lemma 13.8 (i), (ii) and clause AX for `K = O ∪ {m}`).

Not formalized: Observation 13.1 and the remark on general two-test certificates (statements
about all metrics), Lemma 13.8 (iii) (the edge-crossing lift at a ridge), and the coverage
dictionary for types 21 and 29 (a relabelling of `isRupert_octAxis_lift`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Gale determinants of an octahedron: Lemma 13.4 -/

/-- A dependency of the octahedron vanishing at two adjacent vertices `a`, `b` vanishes. -/
theorem dep_eq_zero_of_two {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') {D : ℝ³ → ℝ}
    (hD : IsDep a a' b b' c c' D) (ha : D a = 0) (hb : D b = 0) :
    D a = 0 ∧ D a' = 0 ∧ D b = 0 ∧ D b' = 0 ∧ D c = 0 ∧ D c' = 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have r1 := hD.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, ha, hb] at r1
  have r2 := hD.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, ha, hb] at r2
  have n1 := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  have n2 := F.a'b'c'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hb'c) hcc'
  have zc' : D c' = 0 := by
    have : D c' * F.a'b'c.f c' = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n1.ne
  have zc : D c = 0 := by
    have : D c * F.a'b'c'.f c = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n2.ne
  have hs := hD.sum
  have hv := hD.vsum
  rw [ha, hb, zc, zc'] at hs hv
  have hb'v : D b' = -D a' := by linarith
  rw [hb'v] at hv
  have : D a' • (a' - b') = 0 := by rw [← hv]; module
  have za' : D a' = 0 := (smul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr ha'b')
  exact ⟨ha, za', hb, by rw [hb'v, za', neg_zero], zc, zc'⟩

/-- **`[a b] ≠ 0`** for adjacent vertices `a`, `b` of an octahedron (Lemma 13.4: the
dependency `[a ·]` vanishes at no vertex other than `a`, `a'`). -/
theorem galeD_ne_zero {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') : galeD G.l G.m a b ≠ 0 := by
  intro h0
  -- the dependency `[a ·]` vanishes, so `g_a = 0`
  obtain ⟨-, e2, -, e4, e5, e6⟩ := dep_eq_zero_of_two F (G.hl.galeD G.hm a) (galeD_self _ _ _) h0
  obtain ⟨hma, hla⟩ := G.indep (G.m a) (-G.l a)
    (by simp only [galeD] at *; ring) (by simp only [galeD] at e2; linarith)
    (by simp only [galeD] at h0; linarith) (by simp only [galeD] at e4; linarith)
    (by simp only [galeD] at e5; linarith) (by simp only [galeD] at e6; linarith)
  have hla' : G.l a = 0 := by linarith
  -- likewise `g_b = 0`
  have hE := G.hl.comb G.hm (G.m b) (-G.l b)
  obtain ⟨-, f2, -, f4, f5, f6⟩ := dep_eq_zero_of_two F hE
    (by simp only [hma, hla']; ring) (by ring)
  obtain ⟨hmb, hlb⟩ := G.indep (G.m b) (-G.l b) (by simp only [hma, hla']; ring) f2 (by ring)
    f4 f5 f6
  have hlb' : G.l b = 0 := by linarith
  -- so `l = m = 0`
  obtain ⟨-, l2, -, l4, l5, l6⟩ := dep_eq_zero_of_two F G.hl hla' hlb'
  obtain ⟨-, m2, -, m4, m5, m6⟩ := dep_eq_zero_of_two F G.hm hma hmb
  have := G.indep 1 0 (by rw [hla']; ring) (by rw [l2]; ring) (by rw [hlb']; ring)
    (by rw [l4]; ring) (by rw [l5]; ring) (by rw [l6]; ring)
  exact one_ne_zero this.1

/-- `pole_signs` with `L e ≠ 0` in place of `L t' ≠ 0` (so planar equators are allowed). -/
theorem pole_signs' {t t' e e' g g' : ℝ³} (F : OctFacets t t' e e' g g') {L : ℝ³ → ℝ}
    (hL : IsDep t t' e e' g g' L) (h0 : L t = 0) (he : L e ≠ 0) :
    0 < L e * L e' ∧ 0 < L g * L g' ∧ L e * L g < 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, hte, hte', htg, htg'⟩, ⟨ht'e, ht'e', ht'g, ht'g'⟩, ⟨hee', heg, heg'⟩,
    ⟨he'g, he'g'⟩, hgg', -⟩ := hnd
  have r1 := hL.apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, h0] at r1
  have r2 := hL.apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, h0] at r2
  have r3 := hL.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, h0] at r3
  have r4 := hL.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, h0] at r4
  have n1e' := F.a'bc.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g
  have n1g' := F.a'bc.neg g' (by simp) (Ne.symm ht'g') (Ne.symm heg') (Ne.symm hgg')
  have n2e' := F.a'bc'.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g'
  have n2g := F.a'bc'.neg g (by simp) (Ne.symm ht'g) (Ne.symm heg) hgg'
  have n3e := F.a'b'c.neg e (by simp) (Ne.symm ht'e) hee' heg
  have n3g' := F.a'b'c.neg g' (by simp) (Ne.symm ht'g') (Ne.symm he'g') (Ne.symm hgg')
  have n4e := F.a'b'c'.neg e (by simp) (Ne.symm ht'e) hee' heg'
  have n4g := F.a'b'c'.neg g (by simp) (Ne.symm ht'g) (Ne.symm he'g) hgg'
  obtain ⟨s1, z1⟩ := pair_sign (L₁ := L e') (L₂ := L g') (by linarith) n1e' n1g'
  obtain ⟨s2, z2⟩ := pair_sign (L₁ := L e') (L₂ := L g) (by linarith) n2e' n2g
  obtain ⟨s3, z3⟩ := pair_sign (L₁ := L e) (L₂ := L g') (by linarith) n3e n3g'
  obtain ⟨s4, z4⟩ := pair_sign (L₁ := L e) (L₂ := L g) (by linarith) n4e n4g
  have hg : L g ≠ 0 := fun h' => he (z4.mpr h')
  have he' : L e' ≠ 0 := fun h' => hg (z2.mp h')
  have hg' : L g' ≠ 0 := fun h' => he' (z1.mpr h')
  have q2 : L e' * L g < 0 := lt_of_le_of_ne s2 (mul_ne_zero he' hg)
  have q3 : L e * L g' < 0 := lt_of_le_of_ne s3 (mul_ne_zero he hg')
  have q4 : L e * L g < 0 := lt_of_le_of_ne s4 (mul_ne_zero he hg)
  refine ⟨?_, ?_, q4⟩
  · have := mul_pos_of_neg_of_neg q4 q2
    have hgg : 0 < L g * L g := mul_self_pos.mpr hg
    nlinarith
  · have := mul_pos_of_neg_of_neg q4 q3
    have hee : 0 < L e * L e := mul_self_pos.mpr he
    nlinarith

/-- **Lemma 13.4 (cluster signs, every octahedron).**  `[a ·]` and `[a' ·]` have one sign
on `{b, b'}`, the opposite sign on `{c, c'}`, and the same pattern (`[a b] [a' b] > 0`);
`[b c]`, `[b c']`, `[b' c]`, `[b' c']` all have one sign.  No planar-equator exclusion. -/
theorem cluster_signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') :
    (0 < galeD G.l G.m a b * galeD G.l G.m a b' ∧ 0 < galeD G.l G.m a c * galeD G.l G.m a c' ∧
      galeD G.l G.m a b * galeD G.l G.m a c < 0) ∧
    (0 < galeD G.l G.m a' b * galeD G.l G.m a' b' ∧
      0 < galeD G.l G.m a' c * galeD G.l G.m a' c' ∧
      galeD G.l G.m a' b * galeD G.l G.m a' c < 0) ∧
    0 < galeD G.l G.m a b * galeD G.l G.m a' b ∧
    (0 < galeD G.l G.m b c * galeD G.l G.m b c' ∧ 0 < galeD G.l G.m b c * galeD G.l G.m b' c ∧
      0 < galeD G.l G.m b c * galeD G.l G.m b' c') := by
  have anti := galeD_anti G.l G.m
  have A := pole_signs' F (G.hl.galeD G.hm a) (galeD_self _ _ _) (galeD_ne_zero F G)
  have A' := pole_signs' F.swap₁ (G.swap₁.hl.galeD G.swap₁.hm a') (galeD_self _ _ _)
    (galeD_ne_zero F.swap₁ G.swap₁)
  have B := pole_signs' F.perm₁₂ (G.perm₁₂.hl.galeD G.perm₁₂.hm b) (galeD_self _ _ _)
    (galeD_ne_zero F.perm₁₂ G.perm₁₂)
  have Bc := pole_signs' F.perm₁₂.perm₂₃ (G.perm₁₂.perm₂₃.hl.galeD G.perm₁₂.perm₂₃.hm b)
    (galeD_self _ _ _) (galeD_ne_zero F.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃)
  have B'c := pole_signs' F.perm₁₂.perm₂₃.swap₁
    (G.perm₁₂.perm₂₃.swap₁.hl.galeD G.perm₁₂.perm₂₃.swap₁.hm b') (galeD_self _ _ _)
    (galeD_ne_zero F.perm₁₂.perm₂₃.swap₁ G.perm₁₂.perm₂₃.swap₁)
  have Cb := pole_signs' F.perm₂₃.perm₁₂.perm₂₃
    (G.perm₂₃.perm₁₂.perm₂₃.hl.galeD G.perm₂₃.perm₁₂.perm₂₃.hm c) (galeD_self _ _ _)
    (galeD_ne_zero F.perm₂₃.perm₁₂.perm₂₃ G.perm₂₃.perm₁₂.perm₂₃)
  have hb'c : galeD G.l G.m b' c ≠ 0 := by
    have := galeD_ne_zero F.perm₁₂.perm₂₃.swap₁ G.perm₁₂.perm₂₃.swap₁; exact this
  dsimp only [GaleData.perm₁₂, GaleData.perm₂₃, GaleData.swap₁] at A' B Bc B'c Cb
  refine ⟨A, A', ?_, Bc.1, ?_, ?_⟩
  · have := B.1; rw [anti a b, anti a' b] at this; nlinarith
  · have := Cb.1; rw [anti b c, anti b' c] at this; nlinarith
  · have h1 : 0 < galeD G.l G.m b c * galeD G.l G.m b' c := by
      have := Cb.1; rw [anti b c, anti b' c] at this; nlinarith
    have h2 := B'c.1
    have hsq : 0 < galeD G.l G.m b' c * galeD G.l G.m b' c := mul_self_pos.mpr hb'c
    have := mul_pos h1 h2
    have e : galeD G.l G.m b c * galeD G.l G.m b' c * (galeD G.l G.m b' c * galeD G.l G.m b' c') =
      (galeD G.l G.m b c * galeD G.l G.m b' c') * (galeD G.l G.m b' c * galeD G.l G.m b' c) := by
      ring
    rw [e] at this
    exact pos_of_mul_pos_left this hsq.le

/-! ### Lemmas 13.5 and 13.6: the view and the sign identity -/

/-- The view of the vertex crossing at `a'` of the faces `a'bc`, `a'b'c'` (Lemma 13.5):
`u₁ = [a b] (b − a') + [a c] (c − a')`, a vector in both face planes. -/
noncomputable def axisView (l m : ℝ³ → ℝ) (a a' b c : ℝ³) : ℝ³ :=
  galeD l m a b • (b - a') + galeD l m a c • (c - a')

/-- **Lemma 13.5, the second form of the view**: `u₁ = −[a b'] (b' − a') − [a c'] (c' − a')`
(the dependency `[a ·]` vanishes at `a`). -/
theorem axisView_eq_neg {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') :
    axisView G.l G.m a a' b c =
      -(galeD G.l G.m a b' • (b' - a') + galeD G.l G.m a c' • (c' - a')) := by
  have hD := G.hl.galeD G.hm a
  have hs := hD.sum
  have hv := hD.vsum
  rw [galeD_self] at hs hv
  simp only [axisView]
  linear_combination (norm := module) hv - hs • a'

/-- **Lemma 13.6 (sign identity)**, at the view of the vertex crossing at `a'`:
`det(u₁, ā, b̄) det(u₁, ā, c̄) > 0` with `ā = a − a'`, `b̄ = b' − b`, `c̄ = c' − c`.  For every
octahedron and labelling; the relabelling `a ↔ a'`, `b ↔ c'`, `b' ↔ c` gives the other
inequality of 13.6 (`axis_sign_two`, at the view `u₂` of the vertex crossing at `a`).
Proof: the dependencies `[a ·]`, `[b ·]` applied to the linear function `det(u₁, ā, · − a')`,
and the Plücker relation; no division by `[a a']` (the paper's continuity step is not
needed). -/
theorem axis_sign {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') :
    0 < det3 (axisView G.l G.m a a' b c) (a - a') (b' - b) *
      det3 (axisView G.l G.m a a' b c) (a - a') (c' - c) := by
  obtain ⟨⟨SA1, SA2, SA3⟩, -, -, ⟨-, -, SB3⟩⟩ := cluster_signs F G
  have hab := galeD_ne_zero F G
  have hb'c' : galeD G.l G.m b' c' ≠ 0 :=
    galeD_ne_zero F.perm₁₂.perm₂₃.swap₁.swap₂ G.perm₁₂.perm₂₃.swap₁.swap₂
  have hbc : galeD G.l G.m b c ≠ 0 := galeD_ne_zero F.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃
  have hV0 : det3 (b - a') (c - a') (a - a') ≠ 0 := frame_det_ne F.swap₁
  set u := axisView G.l G.m a a' b c with hu
  set f : ℝ³ → ℝ := fun t => det3 u (a - a') (t - a') with hf_def
  have hf : ∀ y z, f y - f z = ⟪cross u (a - a'), y - z⟫ := by
    intro y z; simp only [f, det3, ← inner_sub_right]; congr 1; abel
  have rA := (G.hl.galeD G.hm a).apply hf
  have rB := (G.hl.galeD G.hm b).apply hf
  have plk := galeD_plucker G.l G.m a b b' c'
  rw [galeD_self] at rA
  rw [galeD_self] at rB
  set V0 := det3 (b - a') (c - a') (a - a')
  have fa' : f a' = 0 := by simp only [f, det3_expand, PiLp.sub_apply]; ring
  have fa : f a = 0 := by simp only [f, det3_expand, PiLp.sub_apply]; ring
  have fb : f b = galeD G.l G.m a c * V0 := by
    simp only [f, V0, u, axisView, det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]; ring
  have fc : f c = -(galeD G.l G.m a b * V0) := by
    simp only [f, V0, u, axisView, det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]; ring
  have db : det3 u (a - a') (b' - b) = f b' - f b := by
    simp only [f, det3_expand, PiLp.sub_apply]; ring
  have dc : det3 u (a - a') (c' - c) = f c' - f c := by
    simp only [f, det3_expand, PiLp.sub_apply]; ring
  rw [db, dc]
  rw [fa, fa', fb, fc] at rA
  rw [fa, fa', fb, fc] at rB
  set gab := galeD G.l G.m a b
  set gab' := galeD G.l G.m a b'
  set gac := galeD G.l G.m a c
  set gac' := galeD G.l G.m a c'
  set gbc := galeD G.l G.m b c
  set gbc' := galeD G.l G.m b c'
  set gbb' := galeD G.l G.m b b'
  set gb'c' := galeD G.l G.m b' c'
  have E1 : gab' * f b' + gac' * f c' = 0 := by linear_combination rA
  have E2 : gbb' * f b' + gbc' * f c' = gbc * gab * V0 := by linear_combination rB
  have hX : gb'c' * f b' = -(gac' * gbc * V0) := by
    have : gab * (gb'c' * f b' + gac' * gbc * V0) = 0 := by
      linear_combination (f b') * plk + gbc' * E1 - gac' * E2
    have := (mul_eq_zero.mp this).resolve_left hab
    linarith
  have hY : gb'c' * f c' = gab' * gbc * V0 := by
    have : gab * (gb'c' * f c' - gab' * gbc * V0) = 0 := by
      linear_combination (f c') * plk - gbb' * E1 + gab' * E2
    have := (mul_eq_zero.mp this).resolve_left hab
    linarith
  set X1 := gac' * gbc + gac * gb'c'
  set Y1 := gab' * gbc + gab * gb'c'
  have hgbc2 : 0 < gbc * gbc := mul_self_pos.mpr hbc
  have hX1 : 0 < gac * gbc * X1 := by
    have e : gac * gbc * X1 = (gac * gac') * (gbc * gbc) + (gac * gac) * (gbc * gb'c') := by
      simp only [X1]; ring
    rw [e]
    have hac : gac ≠ 0 := by intro h0; rw [h0, mul_zero] at SA3; exact lt_irrefl _ SA3
    nlinarith [mul_self_pos.mpr hac, mul_pos SA2 hgbc2]
  have hY1 : 0 < gab * gbc * Y1 := by
    have e : gab * gbc * Y1 = (gab * gab') * (gbc * gbc) + (gab * gab) * (gbc * gb'c') := by
      simp only [Y1]; ring
    rw [e]
    nlinarith [mul_self_pos.mpr hab, mul_pos SA1 hgbc2]
  have hXY : X1 * Y1 < 0 := by
    have h := mul_pos hX1 hY1
    have e : gac * gbc * X1 * (gab * gbc * Y1) = (gab * gac) * (gbc * gbc) * (X1 * Y1) := by ring
    rw [e] at h
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_neg_of_pos SA3 hgbc2]
  have key : gb'c' * gb'c' * ((f b' - f b) * (f c' - f c)) = -(V0 * V0) * (X1 * Y1) := by
    have e : gb'c' * gb'c' * ((f b' - f b) * (f c' - f c)) =
        (gb'c' * f b' - gb'c' * f b) * (gb'c' * f c' - gb'c' * f c) := by ring
    rw [e, hX, hY, fb, fc]; simp only [X1, Y1]; ring
  have hpos : 0 < gb'c' * gb'c' * ((f b' - f b) * (f c' - f c)) := by
    rw [key]; nlinarith [mul_self_pos.mpr hV0]
  exact pos_of_mul_pos_right hpos (mul_self_nonneg _)

/-- **Lemma 13.6, the second inequality**: at the view `u₂ = [a' c'] (c' − a) + [a' b] (b − a)`
of the vertex crossing at `a` (faces `a b c'`, `a b' c`),
`det(u₂, ā, b̄) det(u₂, ā, c̄) < 0`.  This is `axis_sign` for the relabelled octahedron
`(a', a, c', c, b, b')`. -/
theorem axis_sign_two {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') :
    det3 (axisView G.l G.m a' a c' b) (a - a') (b' - b) *
      det3 (axisView G.l G.m a' a c' b) (a - a') (c' - c) < 0 := by
  have s2 := axis_sign F.perm₂₃.swap₁.swap₂ G.perm₂₃.swap₁.swap₂
  set u₂ := axisView G.l G.m a' a c' b
  change 0 < det3 u₂ (a' - a) (c - c') * det3 u₂ (a' - a) (b' - b) at s2
  have e1 : det3 u₂ (a' - a) (c - c') = det3 u₂ (a - a') (c' - c) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e2 : det3 u₂ (a' - a) (b' - b) = -det3 u₂ (a - a') (b' - b) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e1, e2] at s2
  linarith

/-! ### The angle lemma for 4-corner rims (Lemma 13.2, Corollary 13.3) -/

/-- The projections of the segments `[d₀, d₁]` and `[e₀, e₁]` along `u` meet: `e − d = μ u`
for points `d`, `e` of the segments (possibly ends). -/
def SegMeet (d₀ d₁ e₀ e₁ u : ℝ³) : Prop :=
  ∃ s t μ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = μ • u

/-- The diagonals `{d₀, d₁}`, `{e₀, e₁}` of a 4-corner rim are *depth-separated* at `u`: both
ends of one lie strictly above both ends of the other.  These are the two patterns with two
maxima, so with distinct depths a 4-corner rim is unimodal unless its diagonals are
depth-separated. -/
def DepthSep (d₀ d₁ e₀ e₁ u : ℝ³) : Prop :=
  max ⟪d₀, u⟫ ⟪d₁, u⟫ < min ⟪e₀, u⟫ ⟪e₁, u⟫ ∨ max ⟪e₀, u⟫ ⟪e₁, u⟫ < min ⟪d₀, u⟫ ⟪d₁, u⟫

theorem DepthSep.swap {d₀ d₁ e₀ e₁ u : ℝ³} (h : DepthSep d₀ d₁ e₀ e₁ u) :
    DepthSep d₁ d₀ e₁ e₀ u := by
  simp only [DepthSep, max_comm ⟪d₁, u⟫, min_comm ⟪e₁, u⟫, max_comm ⟪e₁, u⟫,
    min_comm ⟪d₁, u⟫] at h ⊢
  exact h

theorem SegMeet.swap {d₀ d₁ e₀ e₁ u : ℝ³} (h : SegMeet d₀ d₁ e₀ e₁ u) : SegMeet d₁ d₀ e₁ e₀ u := by
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := h
  refine ⟨1 - s, 1 - t, μ, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [← h]; module

theorem inner_seg (x y u : ℝ³) (t : ℝ) : ⟪x + t • (y - x), u⟫ = (1 - t) * ⟪x, u⟫ + t * ⟪y, u⟫ := by
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring

theorem seg_bounds {x y t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min x y ≤ (1 - t) * x + t * y ∧ (1 - t) * x + t * y ≤ max x y := by
  have h1 := min_le_left x y; have h2 := min_le_right x y
  have h3 := le_max_left x y; have h4 := le_max_right x y
  constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]

/-- **The angle lemma, 4-corner form (Lemma 13.2).**  If the diagonals are depth-separated at
`u` and their projections meet along `u` (`e − d = λ u`) and along `v` (`e' − d' = μ v`),
then `λ μ ⟪u, v⟫ > 0`: failure of the test at `u` forces the sign of `⟪u, v⟫`. -/
theorem depthSep_meet_sign {d₀ d₁ e₀ e₁ u v : ℝ³} (hsep : DepthSep d₀ d₁ e₀ e₁ u)
    {s t l s' t' μ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hs0' : 0 ≤ s') (hs1' : s' ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1)
    (h1 : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • u)
    (h2 : (e₀ + t' • (e₁ - e₀)) - (d₀ + s' • (d₁ - d₀)) = μ • v) :
    0 < l * μ * ⟪u, v⟫ := by
  have i1 := congrArg (fun w => ⟪w, u⟫) h1
  have i2 := congrArg (fun w => ⟪w, u⟫) h2
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1 i2
  obtain ⟨e1, e2⟩ := seg_bounds (x := ⟪e₀, u⟫) (y := ⟪e₁, u⟫) ht0 ht1
  obtain ⟨e1', e2'⟩ := seg_bounds (x := ⟪e₀, u⟫) (y := ⟪e₁, u⟫) ht0' ht1'
  obtain ⟨d1, d2⟩ := seg_bounds (x := ⟪d₀, u⟫) (y := ⟪d₁, u⟫) hs0 hs1
  obtain ⟨d1', d2'⟩ := seg_bounds (x := ⟪d₀, u⟫) (y := ⟪d₁, u⟫) hs0' hs1'
  have huu := real_inner_self_nonneg (x := u)
  rw [real_inner_comm u v] at i2
  rcases hsep with h | h
  · have p1 : 0 < l * ⟪u, u⟫ := by linarith
    have p2 : 0 < μ * ⟪u, v⟫ := by linarith
    have hl : 0 < l := by
      by_contra hc; push Not at hc; nlinarith
    have := mul_pos hl p2
    linarith [show l * μ * ⟪u, v⟫ = l * (μ * ⟪u, v⟫) by ring]
  · have p1 : l * ⟪u, u⟫ < 0 := by linarith
    have p2 : μ * ⟪u, v⟫ < 0 := by linarith
    have hl : l < 0 := by
      by_contra hc; push Not at hc; nlinarith
    have := mul_pos_of_neg_of_neg hl p2
    linarith [show l * μ * ⟪u, v⟫ = l * (μ * ⟪u, v⟫) by ring]

/-- **Corollary 13.3, shared-diagonal form, one test.**  If the diagonals `A = [a', a]`,
`B = [b, b']` are depth-separated at `u` and their projections meet along `u` and along `v`,
then `⟪u, v⟫ det(u, ā, b̄) det(v, ā, b̄) ≥ 0` (with `ā = a − a'`, `b̄ = b' − b`) and
`⟪u, v⟫ ≠ 0`. -/
theorem depthSep_det_sign {a a' b b' u v : ℝ³} (hsep : DepthSep a' a b b' u)
    (hu : SegMeet a' a b b' u) (hv : SegMeet a' a b b' v) :
    0 ≤ ⟪u, v⟫ * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b)) ∧ ⟪u, v⟫ ≠ 0 := by
  obtain ⟨s, t, l, hs0, hs1, ht0, ht1, h1⟩ := hu
  obtain ⟨s', t', μ, hs0', hs1', ht0', ht1', h2⟩ := hv
  have hpos := depthSep_meet_sign hsep hs0 hs1 ht0 ht1 hs0' hs1' ht0' ht1' h1 h2
  have key : ∀ (x : ℝ³) (k s t : ℝ), b + t • (b' - b) - (a' + s • (a - a')) = k • x →
      k * det3 x (a - a') (b' - b) = det3 (b - a') (a - a') (b' - b) := by
    intro x k s t h
    have e := congrArg (fun w => det3 w (a - a') (b' - b)) h
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e ⊢
    linear_combination -e
  have k1 := key u l s t h1
  have k2 := key v μ s' t' h2
  refine ⟨?_, fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos⟩
  set Du := det3 u (a - a') (b' - b)
  set Dv := det3 v (a - a') (b' - b)
  set S := det3 (b - a') (a - a') (b' - b)
  have e : (l * μ * ⟪u, v⟫) * (⟪u, v⟫ * (Du * Dv)) =
      (⟪u, v⟫ * (l * Du)) * (⟪u, v⟫ * (μ * Dv)) := by ring
  rw [k1, k2] at e
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg hpos hc
  rw [e] at this
  linarith [mul_self_nonneg (⟪u, v⟫ * S)]

/-- **Corollary 13.3 for two tests sharing the diagonal `A = [a', a]`.**  Test 1 at `u` has
diagonals `A`, `B = [b, b']`, test 2 at `v` has `A`, `C = [c, c']`; the projections of `A` and
`B` meet along `u` and `v`, those of `A` and `C` along `v` and `u`.  If
`det(u, ā, b̄) det(v, ā, b̄) det(u, ā, c̄) det(v, ā, c̄) < 0` (seen along `ā`, the views are
separated by `b̄`, `c̄`), the two tests are not both depth-separated. -/
theorem not_both_depthSep {a a' b b' c c' u v : ℝ³} (h1 : DepthSep a' a b b' u)
    (h2 : DepthSep a' a c c' v) (m1u : SegMeet a' a b b' u) (m1v : SegMeet a' a b b' v)
    (m2v : SegMeet a' a c c' v) (m2u : SegMeet a' a c c' u)
    (hdet : det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b) *
      (det3 u (a - a') (c' - c) * det3 v (a - a') (c' - c)) < 0) : False := by
  obtain ⟨A, hne⟩ := depthSep_det_sign h1 m1u m1v
  obtain ⟨B, -⟩ := depthSep_det_sign h2 m2v m2u
  rw [real_inner_comm u v] at B
  have hsq : 0 < ⟪u, v⟫ * ⟪u, v⟫ := mul_self_pos.mpr hne
  have := mul_nonneg A B
  have e : ⟪u, v⟫ * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b)) *
      (⟪u, v⟫ * (det3 v (a - a') (c' - c) * det3 u (a - a') (c' - c))) =
      (⟪u, v⟫ * ⟪u, v⟫) * (det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b) *
        (det3 u (a - a') (c' - c) * det3 v (a - a') (c' - c))) := by ring
  rw [e] at this
  nlinarith

/-! ### The vertex crossing at `a'`: Lemma 13.5 and the rim -/

theorem ratio_mem_Ioo {x y : ℝ} (hxy : x * y < 0) (habs : |x| < |y|) :
    0 < -x / y ∧ -x / y < 1 := by
  rcases lt_or_gt_of_ne (show y ≠ 0 by rintro rfl; simp at hxy) with hy | hy
  · have hx : 0 < x := by nlinarith
    rw [abs_of_pos hx, abs_of_neg hy] at habs
    exact ⟨div_pos_of_neg_of_neg (by linarith) hy, (div_lt_one_of_neg hy).mpr (by linarith)⟩
  · have hx : x < 0 := by nlinarith
    rw [abs_of_neg hx, abs_of_pos hy] at habs
    exact ⟨div_pos (by linarith) hy, (div_lt_one hy).mpr (by linarith)⟩

/-- **Lemma 13.5 at the vertex crossing at `a'`.**  Under the far-end inequalities
`|[a b]| < |[a c]|` and `|[a b']| < |[a c']|`, `c` and `c'` are middles over the sides
`a' → b`, `a' → b'` at the view `u₁` (`c = a' + s (b − a') + δ u₁`, `0 < s < 1`, `δ ≠ 0`,
likewise `c'`), and for the orientation `σ = ±1` of the corner at `a'`:
`σ det(b − a', b' − a', u₁) > 0` (the corner), `σ det(b − a', a − a', u₁) > 0` and
`σ det(a − a', b' − a', u₁) > 0` (`a` is beneath both faces). -/
theorem axis_test_facts {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|) :
    ∃ σ s δ s' δ' : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ c = a' + s • (b - a') + δ • axisView G.l G.m a a' b c ∧
      0 < s' ∧ s' < 1 ∧ δ' ≠ 0 ∧ c' = a' + s' • (b' - a') + δ' • axisView G.l G.m a a' b c ∧
      0 < σ * det3 (b - a') (b' - a') (axisView G.l G.m a a' b c) ∧
      0 < σ * det3 (b - a') (a - a') (axisView G.l G.m a a' b c) ∧
      0 < σ * det3 (a - a') (b' - a') (axisView G.l G.m a a' b c) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨⟨SA1, SA2, SA3⟩, -, -, -⟩ := cluster_signs F G
  have hu' := axisView_eq_neg G
  set u := axisView G.l G.m a a' b c with hu
  set gab := galeD G.l G.m a b
  set gab' := galeD G.l G.m a b'
  set gac := galeD G.l G.m a c
  set gac' := galeD G.l G.m a c'
  have hgac : gac ≠ 0 := by intro h0; rw [h0, mul_zero] at SA3; exact lt_irrefl _ SA3
  have hgac' : gac' ≠ 0 := by intro h0; rw [h0, mul_zero] at SA2; exact lt_irrefl _ SA2
  have SA4 : gab' * gac' < 0 := by nlinarith [mul_pos SA1 SA2]
  obtain ⟨hs0, hs1⟩ := ratio_mem_Ioo SA3 hfar₁
  obtain ⟨hs0', hs1'⟩ := ratio_mem_Ioo SA4 hfar₂
  -- the corner orientation
  have hT : det3 (b - a') (b' - a') u ≠ 0 := by
    have e : det3 (b - a') (b' - a') u = -(gac * det3 (b - a') (c - a') (b' - a')) := by
      simp only [u, axisView, det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul]; ring
    rw [e, neg_ne_zero]
    refine mul_ne_zero hgac fun h0 => ?_
    have hcr := cross_ne_zero_of_affine F.a'bc'.hN ha'b F.a'bc'.hP F.a'bc'.hQ
      (F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc')
    have := affine_zero_of_coplanar F.a'bc.hN F.a'bc.hP F.a'bc.hQ F.a'bc.hR hcr h0
    have := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c
    linarith
  have hNu : ⟪F.a'bc.N, u⟫ = 0 := by
    simp only [u, axisView, inner_add_right, real_inner_smul_right, ← F.a'bc.hN, F.a'bc.hP,
      F.a'bc.hQ, F.a'bc.hR]; ring
  have hNu' : ⟪F.a'b'c'.N, u⟫ = 0 := by
    rw [hu', inner_neg_right]
    simp only [inner_add_right, real_inner_smul_right, ← F.a'b'c'.hN, F.a'b'c'.hP,
      F.a'b'c'.hQ, F.a'b'c'.hR]; ring
  have key : ∀ σ : ℝ, 0 < σ * det3 (b - a') (b' - a') u →
      0 < σ * det3 (b - a') (a - a') u ∧ 0 < σ * det3 (a - a') (b' - a') u := by
    intro σ hσ
    constructor
    · refine det3_pos_of_combo_σ F.a'bc.hN F.a'bc.hN F.a'bc.hP F.a'bc.hQ F.a'bc.hP F.a'bc.hQ
        (α := 1) (β := 0) (by rw [hNu]; ring) hσ ?_ ?_
      · have := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c; linarith
      · have := F.a'bc.neg a (by simp) haa' hab hac; linarith
    · have e1 : det3 (a' - b') (b - b') u = det3 (b - a') (b' - a') u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e2 : det3 (a' - b') (a - b') u = det3 (a - a') (b' - a') u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [← e2]
      refine det3_pos_of_combo_σ F.a'b'c'.hN F.a'b'c'.hN F.a'b'c'.hQ F.a'b'c'.hP F.a'b'c'.hQ
        F.a'b'c'.hP (α := 1) (β := 0) (by rw [hNu']; ring) (r := b) (by rw [e1]; exact hσ) ?_ ?_
      · have := F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc'; linarith
      · have := F.a'b'c'.neg a (by simp) haa' hab' hac'; linarith
  have hc : c = a' + (-gab / gac) • (b - a') + (1 / gac) • u := by
    rw [hu]; simp only [axisView]
    match_scalars <;> field_simp <;> ring
  have hc' : c' = a' + (-gab' / gac') • (b' - a') + (-1 / gac') • u := by
    rw [hu']
    match_scalars <;> field_simp <;> ring
  rcases lt_or_gt_of_ne hT with h | h
  · obtain ⟨k1, k2⟩ := key (-1) (by linarith)
    exact ⟨-1, _, _, _, _, Or.inr rfl, hs0, hs1, one_div_ne_zero hgac, hc, hs0', hs1',
      div_ne_zero (by norm_num) hgac', hc', by linarith, k1, k2⟩
  · obtain ⟨k1, k2⟩ := key 1 (by linarith)
    exact ⟨1, _, _, _, _, Or.inl rfl, hs0, hs1, one_div_ne_zero hgac, hc, hs0', hs1',
      div_ne_zero (by norm_num) hgac', hc', by linarith, k1, k2⟩

/-! ### Proposition 8.8 with a unimodal `K′` at a vertex view, from determinant tests -/

/-- **Proposition 8.8 with Theorem 7.3, at a view given by determinant tests** (no rotation
in the statement; the vertex-crossing analogue of `isRupert_of_edgeView`).  The cycle `x`
passes all determinant tests at `u₀` (strictly convex, counterclockwise), every point of `V`
other than the corners and the middles `M` is strictly inside, the depths `⟪x i, u₀⟫` are
cyclically unimodal, there is no horizontal double normal, and each middle lies over a side:
`m = x i + s (x (i + 1) − x i) + δ u₀`, `0 < s < 1`, `δ ≠ 0`.  Then `V` is Rupert. -/
theorem isRupert_of_vertexView (V M : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt V u₀)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u₀ hu₀
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_chords_unimodal V M R hR hr hRu x hxV hxM hp ?_ ?_ ?_ hM
  · intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x hxV hp

/-! ### The test: the rim is a triangle or a quadrilateral -/

/-- A hidden point at the vertex crossing at `a'` with far ends `b`, `b'` (Lemma 13.8 (i)):
its projection along `u` is a combination of those of `a, a', b, b'` with positive weights,
so it lies in the interior of the shadow. -/
def AxisHidden (a a' b b' u m : ℝ³) : Prop :=
  ∃ w₁ w₂ w₃ w₄ μ : ℝ, 0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧ 0 < w₄ ∧ w₁ + w₂ + w₃ + w₄ = 1 ∧
    m = w₁ • a + w₂ • a' + w₃ • b + w₄ • b' + μ • u

/-- A middle over a side at the apex `a'` (Lemma 13.8 (ii)): on the screen strictly between
`a'` and the far end `b` (or `b'`), off the view line through them. -/
def ApexMid (a' b b' u m : ℝ³) : Prop :=
  (∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = a' + s • (b - a') + δ • u) ∨
  (∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = a' + s • (b' - a') + δ • u)

/-- An admissible extra point of the vertex crossing at `a'`: hidden or a middle at the apex. -/
def AxisExtra (a a' b b' u m : ℝ³) : Prop := AxisHidden a a' b b' u m ∨ ApexMid a' b b' u m

theorem det3_hidden (e p a a' b b' u : ℝ³) {w₁ w₂ w₃ w₄ μ : ℝ} (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    det3 e (w₁ • a + w₂ • a' + w₃ • b + w₄ • b' + μ • u - p) u =
      w₁ * det3 e (a - p) u + w₂ * det3 e (a' - p) u + w₃ * det3 e (b - p) u +
        w₄ * det3 e (b' - p) u := by
  have e1 : w₁ • a + w₂ • a' + w₃ • b + w₄ • b' + μ • u - p =
      w₁ • (a - p) + w₂ • (a' - p) + w₃ • (b - p) + w₄ • (b' - p) + μ • u := by
    linear_combination (norm := module) hw • p
  rw [e1]
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The two forms of an apex middle, read by the side functions at `a'`. -/
theorem apexMid_sides {a' b b' u m : ℝ³} (h : ApexMid a' b b' u m) :
    (det3 (b - a') (m - a') u = 0 ∧ ∃ s, 0 < s ∧ s < 1 ∧
      det3 (m - a') (b' - a') u = s * det3 (b - a') (b' - a') u) ∨
    (det3 (m - a') (b' - a') u = 0 ∧ ∃ s, 0 < s ∧ s < 1 ∧
      det3 (b - a') (m - a') u = s * det3 (b - a') (b' - a') u) := by
  rcases h with ⟨s, δ, hs0, hs1, -, rfl⟩ | ⟨s, δ, hs0, hs1, -, rfl⟩
  · refine Or.inl ⟨?_, s, hs0, hs1, ?_⟩ <;>
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
      ring
  · refine Or.inr ⟨?_, s, hs0, hs1, ?_⟩ <;>
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
      ring

theorem mid_view {x y u : ℝ³} {σ s δ : ℝ} (hσσ : σ * σ = 1) :
    x + s • (y - x) + δ • u = x + s • (y - x) + (σ * δ) • (σ • u) := by
  rw [smul_smul, show σ * δ * σ = δ by linear_combination δ * hσσ]

theorem mid_view' {x y u : ℝ³} {σ s δ : ℝ} (hσσ : σ * σ = 1) :
    x + s • (y - x) + δ • u = y + (1 - s) • (x - y) + (σ * δ) • (σ • u) := by
  rw [smul_smul, show σ * δ * σ = δ by linear_combination δ * hσσ]; module

theorem overlap4_of_not_depthSep {a a' b b' u : ℝ³} (h : ¬ DepthSep a' a b b' u)
    (h1 : ⟪a', u⟫ ≠ ⟪b, u⟫) (h2 : ⟪a', u⟫ ≠ ⟪a, u⟫) (h3 : ⟪a', u⟫ ≠ ⟪b', u⟫)
    (h4 : ⟪b, u⟫ ≠ ⟪a, u⟫) (h5 : ⟪b, u⟫ ≠ ⟪b', u⟫) (h6 : ⟪a, u⟫ ≠ ⟪b', u⟫) :
    Overlap4 ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫ := by
  simp only [DepthSep, not_or, not_lt] at h
  obtain ⟨k1, k2⟩ := h
  refine ⟨?_, ?_, h2, h5⟩
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have : max ⟪b, u⟫ ⟪b', u⟫ < min ⟪a', u⟫ ⟪a, u⟫ :=
      max_lt (lt_min (lt_of_le_of_ne c1 (Ne.symm h1)) (lt_of_le_of_ne c3 h4))
        (lt_min (lt_of_le_of_ne c2 (Ne.symm h3)) (lt_of_le_of_ne c4 (Ne.symm h6)))
    linarith
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have : max ⟪a', u⟫ ⟪a, u⟫ < min ⟪b, u⟫ ⟪b', u⟫ :=
      max_lt (lt_min (lt_of_le_of_ne c1 h1) (lt_of_le_of_ne c2 h3))
        (lt_min (lt_of_le_of_ne c3 (Ne.symm h4)) (lt_of_le_of_ne c4 h6))
    linarith

theorem det3_zero_mid (x u : ℝ³) : det3 x 0 u = 0 := by
  simp only [det3_expand, PiLp.zero_apply]; ring

theorem det3_zero_left' (x u : ℝ³) : det3 0 x u = 0 := by
  simp only [det3_expand, PiLp.zero_apply]; ring

/-- **The vertex crossing at `a'`, certified** (Proposition 8.8 with Theorem 7.3).  The
screen data at the view `u` (orientation `σ = ±1`): the corner `a'` between the sides towards
`b` and `b'` (`σ T > 0`, `T = det(b − a', b' − a', u)`), `a` inside that corner (`σ Γ > 0`,
`σ B > 0`); every point of `V` is `a, a', b, b'` or an admissible extra point (hidden, or a
middle at the apex, such as the middles `c`, `c'`).  Then:
* if `a` is on the inner side of `b b'` (`σ det(b' − b, a − b, u) > 0`), the rim is the
  triangle `a' b b'`, unimodal whenever its depths are distinct, and `V` is Rupert;
* if `a` is beyond `b b'` (`< 0`), the rim is the quadrilateral `a' b a b'`; with distinct
  depths it is unimodal unless its diagonals `[a', a]`, `[b, b']` are depth-separated, and
  then `V` is Rupert.
No horizontal double normal at `u` (`NoHDNAt`) is assumed. -/
theorem isRupert_axisTest_core {a a' b b' u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u)
    (hz : ⟪a', u⟫ ≠ ⟪b, u⟫ ∧ ⟪a', u⟫ ≠ ⟪b', u⟫ ∧ ⟪b, u⟫ ≠ ⟪b', u⟫)
    (V : Finset ℝ³) (ha : a ∈ V) (ha' : a' ∈ V) (hb : b ∈ V) (hb' : b' ∈ V)
    (hV : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v)
    (hnd : NoHDNAt V u) :
    (0 < σ * det3 (b' - b) (a - b) u → IsRupert V) ∧
    (σ * det3 (b' - b) (a - b) u < 0 → ⟪a', u⟫ ≠ ⟪a, u⟫ → ⟪b, u⟫ ≠ ⟪a, u⟫ →
      ⟪a, u⟫ ≠ ⟪b', u⟫ → ¬ DepthSep a' a b b' u → IsRupert V) := by
  classical
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσσ
  have hu0 : u ≠ 0 := by rintro rfl; simp [det3] at hT
  have hw0 : σ • u ≠ 0 := smul_ne_zero hσ0 hu0
  have hdw : ∀ x y, det3 x y (σ • u) = σ * det3 x y u := fun x y => by
    simp only [det3, real_inner_smul_right]
  have hiw : ∀ x, ⟪x, σ • u⟫ = σ * ⟪x, u⟫ := fun x => real_inner_smul_right _ _ _
  have hndw : NoHDNAt V (σ • u) := by
    rcases hσ with rfl | rfl
    · rwa [one_smul]
    · rw [neg_one_smul]; exact hnd.neg
  have i1 : det3 (b' - b) (a' - b) u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (a' - b') (b - b') u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i3 : det3 (a' - b') (a - b') u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (a - b) (a' - b) u = det3 (b - a') (a - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i5 : det3 (a - b) (b' - b) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b' - a) (a' - a) u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i7 : det3 (b' - a) (b - a) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not middles
  have nmid : ∀ y, ApexMid a' b b' u y → y ≠ a ∧ y ≠ a' ∧ y ≠ b ∧ y ≠ b' := by
    intro y hy
    have hsT : ∀ s : ℝ, 0 < s → s < 1 → 0 < s * (σ * det3 (b - a') (b' - a') u) ∧
        0 < (1 - s) * (σ * det3 (b - a') (b' - a') u) :=
      fun s h0 h1 => ⟨mul_pos h0 hT, mul_pos (by linarith) hT⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at hy <;>
      rcases apexMid_sides hy with ⟨h1, s, hs0, hs1, h2⟩ | ⟨h1, s, hs0, hs1, h2⟩ <;>
      (try simp only [sub_self, det3_zero_mid, det3_zero_left', det3_self_left] at h1 h2) <;>
      obtain ⟨t1, t2⟩ := hsT s hs0 hs1 <;>
      first
        | nlinarith [congrArg (σ * ·) h1, congrArg (σ * ·) h2]
        | nlinarith [congrArg (σ * ·) h2]
  set M := V.filter (ApexMid a' b b' u) with hM
  refine ⟨fun hα => ?_, fun hα h2 h4 h6 hsep => ?_⟩
  · -- the rim is the triangle `a' b b'`
    obtain ⟨b0, b1, b2⟩ := zmod3_add_one
    refine isRupert_of_vertexView V M (σ • u) hw0 (k := 3) le_rfl (tri a' b b') ?_ ?_ ?_ ?_ ?_
      hndw ?_
    · intro i; rcases zmod3_cases i with rfl | rfl | rfl
      exacts [ha', hb, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod3_cases i with rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i1, i2]
      exacts [hT, hT, hT]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2
      simp only [tri_0, tri_1, tri_2] at h0 h1 h2
      rcases hV y hy with e | e | e | e | hext
      · rw [e]
        rcases zmod3_cases i with rfl | rfl | rfl <;>
          simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i3]
        exacts [hΓ, hα, hB]
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h2
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod3_cases i with rfl | rfl | rfl <;>
            simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i1, i2, i3]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p1 hα, mul_pos p2 hT]
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [tri_inner]
      refine isCyclicUnimodal_three (tri_injective ?_ ?_ ?_) <;> simp only [hiw] <;>
        intro h <;> [exact hz.1 (mul_left_cancel₀ hσ0 h); exact hz.2.1 (mul_left_cancel₀ hσ0 h);
          exact hz.2.2 (mul_left_cancel₀ hσ0 h)]
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [b0, tri_0, tri_1]; exact mid_view hσσ⟩
      · exact ⟨2, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [b2, tri_0, tri_2]; exact mid_view' hσσ⟩
  · -- the rim is the quadrilateral `a' b a b'`
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    have hov := overlap4_of_not_depthSep hsep hz.1 h2 hz.2.1 h4 hz.2.2 h6
    have hα' : 0 < σ * -det3 (b' - b) (a - b) u := by linarith
    refine isRupert_of_vertexView V M (σ • u) hw0 (k := 4) (by norm_num) (quad a' b a b') ?_ ?_
      ?_ ?_ ?_ hndw ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [ha', hb, ha, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).1 rfl,
        (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw, i2, i3, i4, i5, i6, i7]
      exacts [hΓ, hT, hα', hΓ, hB, hα', hT, hB]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2; have h3 := hyx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hV y hy with e | e | e | e | hext
      · exact absurd e h2
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h3
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
            simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i2, i3, i4, i5, i6, i7]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p2 hΓ, mul_pos p4 hα']
          · nlinarith [mul_pos p2 hB, mul_pos p3 hα']
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [quad_inner]
      simp only [hiw]
      refine isCyclicUnimodal_four (quad_injective ?_ ?_ ?_ ?_ ?_ ?_) (hov.mul hσ0) <;>
        intro h <;> have h' := mul_left_cancel₀ hσ0 h
      exacts [hz.1 h', h2 h', hz.2.1 h', h4 h', hz.2.2 h', h6 h']
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [a0, quad_0, quad_1]; exact mid_view hσσ⟩
      · exact ⟨3, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [a3, quad_0, quad_3]; exact mid_view' hσσ⟩

/-! ### The crossings of the diagonals (the hypotheses of Corollary 13.3) -/

theorem SegMeet.swap_d {d₀ d₁ e₀ e₁ u : ℝ³} (h : SegMeet d₀ d₁ e₀ e₁ u) :
    SegMeet d₁ d₀ e₀ e₁ u := by
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := h
  exact ⟨1 - s, t, μ, by linarith, by linarith, ht0, ht1, by rw [← h]; module⟩

theorem SegMeet.swap_e {d₀ d₁ e₀ e₁ u : ℝ³} (h : SegMeet d₀ d₁ e₀ e₁ u) :
    SegMeet d₀ d₁ e₁ e₀ u := by
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := h
  exact ⟨s, 1 - t, μ, hs0, hs1, by linarith, by linarith, by rw [← h]; module⟩

/-- **Two segments whose projections cross.**  If `r`, `s` are strictly on opposite sides of
the line `p q` and `p`, `q` weakly on opposite sides of the line `r s` (on the screen along
`u`), the projections of `[p, q]` and `[r, s]` meet. -/
theorem segMeet_of_sides {p q r s u : ℝ³}
    (hD : det3 (q - p) (r - p) u * det3 (q - p) (s - p) u < 0)
    (hE : det3 (s - r) (p - r) u * det3 (s - r) (q - r) u ≤ 0) : SegMeet p q r s u := by
  set Dr := det3 (q - p) (r - p) u
  set Ds := det3 (q - p) (s - p) u
  set Ep := det3 (s - r) (p - r) u
  set Eq := det3 (s - r) (q - r) u
  set Δ := det3 (q - p) (s - r) u with hΔ
  have hΔD : Δ = Ds - Dr := by
    simp only [Δ, Ds, Dr, det3_expand, PiLp.sub_apply]; ring
  have hΔE : Δ = Ep - Eq := by
    simp only [Δ, Ep, Eq, det3_expand, PiLp.sub_apply]; ring
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔD]; intro h0
    have : Ds = Dr := by linarith
    rw [this] at hD; nlinarith [mul_self_nonneg Dr]
  set t := -Dr / Δ with ht
  set l := Ep / Δ with hl
  have htΔ : t * Δ = -Dr := by rw [ht]; field_simp
  have hlΔ : l * Δ = Ep := by rw [hl]; field_simp
  set X := (r + t • (s - r)) - (p + l • (q - p)) with hX
  have c1 : det3 (q - p) X u = 0 := by
    have e : det3 (q - p) X u = Dr + t * Δ := by
      simp only [X, Dr, Δ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e, htΔ]; ring
  have c2 : det3 X (s - r) u = 0 := by
    have e : det3 X (s - r) u = Ep - l * Δ := by
      simp only [X, Ep, Δ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e, hlΔ]; ring
  have hcr := cramer (q - p) (s - r) u X
  rw [c1, c2, zero_smul, zero_smul, zero_add, zero_add] at hcr
  have hXu : X = (det3 (q - p) (s - r) X / Δ) • u := by
    rw [div_eq_inv_mul, mul_smul, ← hcr, smul_smul, inv_mul_cancel₀ hΔ0, one_smul]
  have hbounds : ∀ {x y : ℝ}, x * y < 0 → 0 ≤ x / (x - y) ∧ x / (x - y) ≤ 1 := by
    intro x y hxy
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hxy) with hx | hx
    · have hy : 0 < y := by nlinarith
      exact ⟨div_nonneg_of_nonpos hx.le (by linarith), (div_le_one_of_neg (by linarith)).mpr
        (by linarith)⟩
    · have hy : y < 0 := by nlinarith
      exact ⟨div_nonneg hx.le (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
  have ht' : t = Dr / (Dr - Ds) := by
    rw [ht, hΔD, show Ds - Dr = -(Dr - Ds) by ring]; field_simp
  have hl' : 0 ≤ l ∧ l ≤ 1 := by
    rw [hl, hΔE]
    rcases lt_or_eq_of_le hE with hE' | hE'
    · exact hbounds hE'
    · rcases mul_eq_zero.mp hE' with h0 | h0
      · rw [h0]; simp
      · rw [h0, sub_zero, div_self]
        · simp
        · intro h1; apply hΔ0; rw [hΔE, h0, h1]; ring
  obtain ⟨t0, t1⟩ := hbounds hD
  exact ⟨l, t, _, hl'.1, hl'.2, by rw [ht']; exact t0, by rw [ht']; exact t1, hXu⟩

/-- **The crossings at a quadrilateral rim** (the proof of Theorem 13.7): if `a` is beyond
`b b'` on the screen, the diagonals `[a', a]` and `[b, b']` of the rim cross, and the chord
between the middles `c`, `c'` cuts off the corner `a'`, so `[a', a]` and `[c, c']` cross. -/
theorem axisTest_meets {a a' b b' c c' u : ℝ³} {σ s δ s' δ' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hs0 : 0 < s) (hs1 : s < 1) (hc : c = a' + s • (b - a') + δ • u)
    (hs0' : 0 < s') (hs1' : s' < 1) (hc' : c' = a' + s' • (b' - a') + δ' • u)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u) (hα : σ * det3 (b' - b) (a - b) u < 0) :
    SegMeet a' a b b' u ∧ SegMeet a' a c c' u := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set T := det3 (b - a') (b' - a') u
  set Γ := det3 (b - a') (a - a') u
  set B := det3 (a - a') (b' - a') u
  set α := det3 (b' - b) (a - b) u
  have hαe : α = T - B - Γ := by
    simp only [α, T, B, Γ, det3_expand, PiLp.sub_apply]; ring
  constructor
  · refine segMeet_of_sides ?_ ?_
    · have e1 : det3 (a - a') (b - a') u = -Γ := by
        simp only [Γ, det3_expand, PiLp.sub_apply]; ring
      rw [e1]
      have := mul_pos hΓ hB
      nlinarith
    · have e1 : det3 (b' - b) (a' - b) u = T := by
        simp only [T, det3_expand, PiLp.sub_apply]; ring
      rw [e1]
      have := mul_neg_of_pos_of_neg hT hα
      nlinarith
  · subst hc hc'
    refine segMeet_of_sides ?_ ?_
    · have e1 : det3 (a - a') (a' + s • (b - a') + δ • u - a') u = -(s * Γ) := by
        simp only [Γ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have e2 : det3 (a - a') (a' + s' • (b' - a') + δ' • u - a') u = s' * B := by
        simp only [B, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [e1, e2]
      have h1 := mul_pos (mul_pos hs0 hs0') (mul_pos hΓ hB)
      nlinarith
    · have e1 : det3 (a' + s' • (b' - a') + δ' • u - (a' + s • (b - a') + δ • u))
          (a' - (a' + s • (b - a') + δ • u)) u = s * s' * T := by
        simp only [T, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have e2 : det3 (a' + s' • (b' - a') + δ' • u - (a' + s • (b - a') + δ • u))
          (a - (a' + s • (b - a') + δ • u)) u = s * s' * T - s' * B - s * Γ := by
        simp only [T, B, Γ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [e1, e2]
      have p1 : 0 < σ * (s * s' * T) := by
        have := mul_pos (mul_pos hs0 hs0') hT
        linarith [show σ * (s * s' * T) = s * s' * (σ * T) by ring]
      have p2 : σ * (s * s' * T - s' * B - s * Γ) < 0 := by
        rw [hαe] at hα
        have q1 : s * s' * (σ * B) ≤ s' * (σ * B) := by
          have := mul_pos hs0' hB; nlinarith
        have q2 : s * s' * (σ * Γ) ≤ s * (σ * Γ) := by
          have := mul_pos hs0 hΓ; nlinarith
        have q3 : s * s' * (σ * T) < s * s' * (σ * B + σ * Γ) := by
          have := mul_pos hs0 hs0'; nlinarith
        nlinarith
      have := mul_neg_of_pos_of_neg p1 p2
      nlinarith [hσσ]

/-! ### Theorem 13.7 and the lift 13.8 -/

/-- **One test of Theorem 13.7**: the vertex crossing at `a'` of the faces `a'bc`, `a'b'c'`
of an octahedron, at the view `u₁ = axisView` (Lemma 13.5), under the far-end inequalities
`|[a b]| < |[a c]|`, `|[a b']| < |[a c']|` (the far ends are `b`, `b'`; `c`, `c'` are middles).
Outside the special positions (`P(a)` on the line `P(b) P(b')`; equal depths among
`a', b, a, b'`) and without a horizontal double normal, either `V` is Rupert, or the rim is
the quadrilateral `a' b a b'` with depth-separated diagonals, and then the projections of
`[a', a]` and `[b, b']`, and those of `[a', a]` and `[c, c']`, meet along `u₁`.  The points of
`V` other than the vertices are hidden or middles at the apex (`AxisExtra`, Lemma 13.8). -/
theorem isRupert_axisTest {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (hP : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hz : [⟪a', axisView G.l G.m a a' b c⟫, ⟪b, axisView G.l G.m a a' b c⟫,
      ⟪a, axisView G.l G.m a a' b c⟫, ⟪b', axisView G.l G.m a a' b c⟫].Nodup)
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v)
    (hnd : NoHDNAt V (axisView G.l G.m a a' b c)) :
    IsRupert V ∨ (SegMeet a' a b b' (axisView G.l G.m a a' b c) ∧
      SegMeet a' a c c' (axisView G.l G.m a a' b c) ∧
      DepthSep a' a b b' (axisView G.l G.m a a' b c)) := by
  obtain ⟨σ, s, δ, s', δ', hσ, hs0, hs1, hδ, hc, hs0', hs1', hδ', hc', hT, hΓ, hB⟩ :=
    axis_test_facts F G hfar₁ hfar₂
  set u := axisView G.l G.m a a' b c
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  have hV' : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v := by
    intro v hv
    rcases hV v hv with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, δ, hs0, hs1, hδ, h.trans hc⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨s', δ', hs0', hs1', hδ', h.trans hc'⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have mem : ∀ x ∈ ({a, a', b, b', c, c'} : Finset ℝ³), x ∈ V := fun x hx => hO hx
  obtain ⟨K1, K2⟩ := isRupert_axisTest_core hσ hT hΓ hB ⟨z1, z3, z5⟩ V (mem a (by simp))
    (mem a' (by simp)) (mem b (by simp)) (mem b' (by simp)) hV' hnd
  have hσα : σ * det3 (b' - b) (a - b) u ≠ 0 :=
    mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hP
  rcases lt_or_gt_of_ne hσα with hα | hα
  · by_cases hsep : DepthSep a' a b b' u
    · obtain ⟨m1, m2⟩ := axisTest_meets hσ hs0 hs1 hc hs0' hs1' hc' hT hΓ hB hα
      exact Or.inr ⟨m1, m2, hsep⟩
    · exact Or.inl (K2 hα z2 z4 z6 hsep)
  · exact Or.inl (K1 hα)

/-- **Theorem 13.7 (the octahedral axis lemma), Euclidean form, with admissible extra
points.**  `O` is an octahedron with opposite pairs `(a, a')`, `(b, b')`, `(c, c')` and Gale
data `G` (`[s t] = galeD G.l G.m s t`).  `T₁` is the vertex crossing at `a'` of the faces
`a'bc`, `a'b'c'` at the view `u₁ = [a b] (b − a') + [a c] (c − a')`, `T₂` the vertex crossing
at `a` of the faces `abc'`, `ab'c` at `u₂ = [a' c'] (c' − a) + [a' b] (b − a)` (Lemma 13.5).
Under the four far-end inequalities
`|[a b]| < |[a c]|`, `|[a b']| < |[a c']|`, `|[a' c']| < |[a' b]|`, `|[a' c]| < |[a' b']|`
(along `u₁` the far ends are `b`, `b'`, along `u₂` they are `c`, `c'`), outside the special
positions (`P(a)` on `P(b) P(b')` along `u₁`, `P(a')` on `P(c) P(c')` along `u₂`, equal depths
among the corners of a rim) and without horizontal double normals at `u₁`, `u₂`, the point set
`V ⊇ O` is Rupert, provided every other point of `V` is hidden or a middle at the apex for
both tests (`AxisExtra`).  Proof: each test is Rupert unless its rim is a quadrilateral with
depth-separated diagonals (`isRupert_axisTest`); both cannot happen, by Corollary 13.3 in the
shared-diagonal form (`not_both_depthSep`) and Lemma 13.6 (`axis_sign`). -/
theorem isRupert_octAxis_gen {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (h₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (h₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (h₃ : |galeD G.l G.m a' c'| < |galeD G.l G.m a' b|)
    (h₄ : |galeD G.l G.m a' c| < |galeD G.l G.m a' b'|)
    (hP₁ : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hP₂ : det3 (c - c') (a' - c') (axisView G.l G.m a' a c' b) ≠ 0)
    (hz₁ : [⟪a', axisView G.l G.m a a' b c⟫, ⟪b, axisView G.l G.m a a' b c⟫,
      ⟪a, axisView G.l G.m a a' b c⟫, ⟪b', axisView G.l G.m a a' b c⟫].Nodup)
    (hz₂ : [⟪a, axisView G.l G.m a' a c' b⟫, ⟪c', axisView G.l G.m a' a c' b⟫,
      ⟪a', axisView G.l G.m a' a c' b⟫, ⟪c, axisView G.l G.m a' a c' b⟫].Nodup)
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV₁ : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v)
    (hV₂ : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a' a c' c (axisView G.l G.m a' a c' b) v)
    (hnd₁ : NoHDNAt V (axisView G.l G.m a a' b c))
    (hnd₂ : NoHDNAt V (axisView G.l G.m a' a c' b)) : IsRupert V := by
  have e : ({a', a, c', c, b, b'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  set F₂ := F.perm₂₃.swap₁.swap₂
  set G₂ := G.perm₂₃.swap₁.swap₂
  rcases isRupert_axisTest F G h₁ h₂ hP₁ hz₁ V hO hV₁ hnd₁ with R | ⟨m1u, m2u, sep1⟩
  · exact R
  rcases isRupert_axisTest F₂ G₂ h₃ h₄ hP₂ hz₂ V (by rw [e]; exact hO)
    (by rw [e]; exact hV₂) hnd₂ with R | ⟨m2v, m1v, sep2⟩
  · exact R
  exfalso
  set u₁ := axisView G.l G.m a a' b c
  set u₂ := axisView G.l G.m a' a c' b
  have s1 := axis_sign F G
  have s2 := axis_sign_two F G
  have hdet : det3 u₁ (a - a') (b' - b) * det3 u₂ (a - a') (b' - b) *
      (det3 u₁ (a - a') (c' - c) * det3 u₂ (a - a') (c' - c)) < 0 := by
    have e3 : det3 u₁ (a - a') (b' - b) * det3 u₂ (a - a') (b' - b) *
        (det3 u₁ (a - a') (c' - c) * det3 u₂ (a - a') (c' - c)) =
        (det3 u₁ (a - a') (b' - b) * det3 u₁ (a - a') (c' - c)) *
          (det3 u₂ (a - a') (b' - b) * det3 u₂ (a - a') (c' - c)) := by ring
    rw [e3]
    exact mul_neg_of_pos_of_neg s1 s2
  exact not_both_depthSep sep1 sep2.swap m1u m1v.swap_d m2v.swap m2u hdet

/-- **Theorem 13.7 (the octahedral axis lemma)** for the octahedron itself: under the four
far-end inequalities, outside the special positions and without horizontal double normals at
the two views, one of the two vertex-crossing reduced polygons (`a' b c`/`a' b' c'` at `a'`,
`a b' c`/`a b c'` at `a`) is unimodal, and the octahedron is Rupert (Proposition 8.8 with
Theorem 7.3). -/
theorem isRupert_octAxis {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (h₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (h₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (h₃ : |galeD G.l G.m a' c'| < |galeD G.l G.m a' b|)
    (h₄ : |galeD G.l G.m a' c| < |galeD G.l G.m a' b'|)
    (hP₁ : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hP₂ : det3 (c - c') (a' - c') (axisView G.l G.m a' a c' b) ≠ 0)
    (hz₁ : [⟪a', axisView G.l G.m a a' b c⟫, ⟪b, axisView G.l G.m a a' b c⟫,
      ⟪a, axisView G.l G.m a a' b c⟫, ⟪b', axisView G.l G.m a a' b c⟫].Nodup)
    (hz₂ : [⟪a, axisView G.l G.m a' a c' b⟫, ⟪c', axisView G.l G.m a' a c' b⟫,
      ⟪a', axisView G.l G.m a' a c' b⟫, ⟪c, axisView G.l G.m a' a c' b⟫].Nodup)
    (hnd₁ : NoHDNAt {a, a', b, b', c, c'} (axisView G.l G.m a a' b c))
    (hnd₂ : NoHDNAt {a, a', b, b', c, c'} (axisView G.l G.m a' a c' b)) :
    IsRupert {a, a', b, b', c, c'} :=
  isRupert_octAxis_gen F G h₁ h₂ h₃ h₄ hP₁ hP₂ hz₁ hz₂ _ subset_rfl (fun _ hv => Or.inl hv)
    (fun _ hv => Or.inl hv) hnd₁ hnd₂

/-- **Lemma 13.8 (i), (ii) and clause AX: the lift to `K = O ∪ {m}`.**  `O = K − m` is an
octahedron satisfying the hypotheses of Theorem 13.7.  If both tests lift, i.e. at `u₁` the
point `m` is hidden (`P(m)` in the interior of the shadow of `O`, as a positive combination of
`P(a), P(a'), P(b), P(b')`; case (i)) or a middle over a side at the apex `a'` (strictly
between `P(a')` and the far end `P(b)` or `P(b')`; case (ii)), and likewise at `u₂` (hidden, or
a middle at the apex `a` towards `c'` or `c`), then `K` has the two crossing tests of `O` with
the same rims and depths, one of them is unimodal, and `K` is Rupert (unless a horizontal
double normal of `K` at `u₁` or `u₂`).  The hypotheses are Gale inequalities of `O` plus one
affine certificate per test. -/
theorem isRupert_octAxis_lift {a a' b b' c c' m : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (h₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (h₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (h₃ : |galeD G.l G.m a' c'| < |galeD G.l G.m a' b|)
    (h₄ : |galeD G.l G.m a' c| < |galeD G.l G.m a' b'|)
    (hP₁ : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hP₂ : det3 (c - c') (a' - c') (axisView G.l G.m a' a c' b) ≠ 0)
    (hz₁ : [⟪a', axisView G.l G.m a a' b c⟫, ⟪b, axisView G.l G.m a a' b c⟫,
      ⟪a, axisView G.l G.m a a' b c⟫, ⟪b', axisView G.l G.m a a' b c⟫].Nodup)
    (hz₂ : [⟪a, axisView G.l G.m a' a c' b⟫, ⟪c', axisView G.l G.m a' a c' b⟫,
      ⟪a', axisView G.l G.m a' a c' b⟫, ⟪c, axisView G.l G.m a' a c' b⟫].Nodup)
    (hm₁ : AxisExtra a a' b b' (axisView G.l G.m a a' b c) m)
    (hm₂ : AxisExtra a' a c' c (axisView G.l G.m a' a c' b) m)
    (hnd₁ : NoHDNAt (insert m {a, a', b, b', c, c'}) (axisView G.l G.m a a' b c))
    (hnd₂ : NoHDNAt (insert m {a, a', b, b', c, c'}) (axisView G.l G.m a' a c' b)) :
    IsRupert (insert m {a, a', b, b', c, c'}) := by
  refine isRupert_octAxis_gen F G h₁ h₂ h₃ h₄ hP₁ hP₂ hz₁ hz₂ _ (Finset.subset_insert _ _)
    (fun _ hv => ?_) (fun _ hv => ?_) hnd₁ hnd₂ <;>
  · rcases Finset.mem_insert.mp hv with rfl | h
    · first | exact Or.inr hm₁ | exact Or.inr hm₂
    · exact Or.inl h

end Minimality

end
