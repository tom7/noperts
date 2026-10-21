module

public import Minimality.Type21Lemmas

@[expose] public section

/-!
# Type 21: Lemmas 2 and 3 of §9 (`FEWER-FACES-PROOFS.md` §9)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`,
`O = O6 = K − 2`, the cap `d` (`IsCap21`).

* **Lemma 2 of §9 (exact lift).**  (a) `isRupert_type21_hidden`: at a quad edge of an
  octahedron that is not bad, with one more point hidden at its view (`HiddenAt`), the
  reduced polygons are those of the octahedron and Lemma 9.3 applies (any octahedron and
  any point: it serves both `K − 2` and `K − 6`).  (b) A middle (`QuadMiddle`): the
  first cases of Lemma 3 below, through `isRupert_quad_edge_lift`.
* **Lemma 3 of §9 (the quad edges always lift).**  For each of the eight directions of
  the K-quad edges `05, 34, 06, 46` of `O6`, a quad edge of `O6` that is not bad gives a
  passage, off special positions (`GenPos`, `NoHDNEdges`):
  - `0 → 5` (`isRupert_type21_05`): `3` hidden forces `β < 1`, so `2` is a middle of
    `0256` (Lemma 3 (a));
  - `5 → 0` (`isRupert_type21_50`): `4` hidden forces `β > 1`, so `2` is the far end and
    `6` the middle; then `K`'s test is the test of the octahedron `O2 = K − 6`
    (`IsCap21.O2`), at the quad edge `5 → 0` of `O2`, which is not bad
    (`type21_far_not_bad_core`: the diagonal `0 – 2` of `0256`, the up face `2346`, the
    silhouette edge `23` of the faces `2346`, `235`, the side `36` of the shadow of `O`)
    (Lemma 3 (b));
  - `0 → 6` (`isRupert_type21_06`): `3` hidden forces `α < 1`, a middle;
  - `6 → 0` (`isRupert_type21_60`): `α < 1`, a middle; `α > 1`, `2` the far end and `5`
    the middle, `K_6`'s rim is the face `2346` (`isRupert_type21_60_far`, planar, hence
    unimodal; `1` is hidden because it is hidden in `O`) (Lemma 3 (c)); `α = 1` would
    make `25 ∥ 06`;
  - `4 → 3`, `3 → 4`, `4 → 6`, `6 → 4`: the images under `σ1 = (04)(35)`.
  The paper's route through Lemma 1 (the rim neighbours) to exclude the other hidden
  vertex is replaced by the facet inequality of the quad edge itself.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- No horizontal double normal at the view along any segment (the exclusion of
Theorem 8.9 with Theorem 7.3). -/
def NoHDNEdges (V : Finset ℝ³) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, v ≠ w → NoHDNAt (V.erase w) (w - v)

/-- The relabellings of `K` used in this file. -/
theorem type21_set (a a' b b' c c' d : ℝ³) :
    insert d ({a, a', b', b, c, c'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert c' ({b', b, a, a', c, d} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({a, a', c', c, b, b'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({c', c, a, a', b, b'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({b, b', a, a', c, c'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

/-! ### Lemma 2 (a): a hidden point -/

/-- **Lemma 2 (a) of §9 (exact lift at a hidden point).**  Let `x → y` be a quad edge of an
octahedron `O` that is not bad, and `m` one more point, hidden at the view along `x y`
(`HiddenAt`).  Then the reduced polygons of `K = O ∪ {m}` at that view are those of `O`,
closing by closing, and Lemma 9.3 gives a passage, off special positions. -/
theorem isRupert_type21_hidden {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hH : HiddenAt {x, x', y, y', p, p'} (y - x) m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hgen : GenPos (insert m ({x, x', y, y', p, p'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert m ({x, x', y, y', p, p'} : Finset ℝ³))) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  exact isRupert_quad_edge_lift F hq₁ hq₂ hgood (Or.inr (quadHidden_of_hiddenAt F hq₁ hq₂ hH))
    hmO (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hxy
      ⟨Ne.symm hxy', Ne.symm hyy', Ne.symm hxp, Ne.symm hyp, Ne.symm hxp', Ne.symm hyp'⟩)
    (noHDN_pair hnd (by simp) (by simp) hxy)

/-! ### Lemma 3: the quad edges `05` and `06` with the cap a middle -/

section Lift

variable {a a' b b' c c' d : ℝ³}

/-- **Lemma 3 of §9 at `0 → 5`.**  If `0 → 5` is a quad edge of `O6` (`3` hidden: the facet
inequalities at `134`, `346`) that is not bad, then `β < 1` (the inequality at `346`, on
which `2` lies), so `2` is a middle of `0256` at the view along `05` (Lemma 2 (b)), and `K`
is Rupert. -/
theorem isRupert_type21_05 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.a'bc.f a < F.a'bc.f b') (hq₂ : F.a'bc'.f a < F.a'bc'.f b')
    (hgood : ¬ max ⟪b', b' - a⟫ ⟪b, b' - a⟫ ≤ min ⟪c, b' - a⟫ ⟪c', b' - a⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨α, β, hα, hβ, hαβ, hco⟩ := hd.coords'
  have hβ1 : β < 1 := by
    have hf := affine_frame F.a'bc'.hN a b' c' α β
    rw [← hco, hd.a'bc', F.a'bc'.hR] at hf
    have n := F.a'bc'.neg a (by simp) haa' hab hac'
    nlinarith [mul_lt_mul_of_pos_left hq₂ hα]
  have hmid : QuadMiddle a b' c c' d :=
    ⟨β, α + β - 1, hβ, hβ1, by linarith, by linarith, Or.inr (by rw [hco]; module)⟩
  rw [← (type21_set a a' b b' c c' d).1] at hgen hnd ⊢
  exact isRupert_quad_edge_lift F.swap₂ hq₁ hq₂ hgood (Or.inl hmid)
    ⟨hda, hda', hdb', hdb, hdc, hdc'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hab'
      ⟨Ne.symm hab, hbb', Ne.symm hac, Ne.symm hb'c, Ne.symm hac', Ne.symm hb'c'⟩)
    (noHDN_pair hnd (by simp) (by simp) hab')

/-- **Lemma 3 of §9 at `0 → 6`.**  If `0 → 6` is a quad edge of `O6` (`3` hidden: the facet
inequalities at `134`, `135`) that is not bad, then `α < 1` (the inequality at `135` with
`2` beneath `135`), so `2` is a middle of `0256` at the view along `06`. -/
theorem isRupert_type21_06 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.a'bc.f a < F.a'bc.f c') (hq₂ : F.a'b'c.f a < F.a'b'c.f c')
    (hgood : ¬ max ⟪c', c' - a⟫ ⟪c, c' - a⟫ ≤ min ⟪b, c' - a⟫ ⟪b', c' - a⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨α, β, hα, hβ, hαβ, hco⟩ := hd.coords'
  have hα1 : α < 1 := by
    have hf := affine_frame F.a'b'c.hN a b' c' α β
    rw [← hco, F.a'b'c.hQ] at hf
    have n := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
    have na := F.a'b'c.neg a (by simp) haa' hab' hac
    nlinarith [mul_lt_mul_of_pos_left hq₂ hβ, hd.a'b'c]
  have hmid : QuadMiddle a c' b b' d :=
    ⟨α, α + β - 1, hα, hα1, by linarith, by linarith, Or.inr (by rw [hco]; module)⟩
  rw [← (type21_set a a' b b' c c' d).2.2.1] at hgen hnd ⊢
  exact isRupert_quad_edge_lift F.perm₂₃.swap₂ hq₁ hq₂ hgood (Or.inl hmid)
    ⟨hda, hda', hdc', hdc, hdb, hdb'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hac'
      ⟨Ne.symm hac, hcc', Ne.symm hab, hbc', Ne.symm hab', hb'c'⟩)
    (noHDN_pair hnd (by simp) (by simp) hac')

/-! ### Lemma 3 (c): `6 → 0` with the cap the far end; `K_6` is the face `2346` -/

theorem zmod4_three_sub_one : (3 : ZMod 4) - 1 = 2 := by decide
theorem zmod4_one_sub_one : (1 : ZMod 4) - 1 = 0 := by decide

/-- **Lemma 3 (c) of §9.**  Let `6 → 0` be a quad edge of `O6` (`1` hidden: the facet
inequalities at `134`, `135`) with `α > 1`: at the view along `06` the far end of `0256`
is `2` and `5` is a middle.  Then `K_6 = {6, 1, 2, 3, 4}` has the rim `6, 4, 3, 2`, the
face `2346` in its cyclic order (`1` is hidden: it is hidden in `O`, whose shadow
`q, 4, 3, 5` lies in `q, 4, 3, 2` since `5` lies on `[q, 2]`), planar, so unimodal unless
an edge of `2346` is level; with distinct depths and no horizontal double normal, `K` is
Rupert.  This case does not use the goodness of the quad edge. -/
theorem isRupert_type21_60_far (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.a'bc.f c' < F.a'bc.f a) (hq₂ : F.a'b'c.f c' < F.a'b'c.f a)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hco : d = a + α • (b' - a) + β • (c' - a))
    (hα1 : 1 < α)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : a - c' ≠ 0 := sub_ne_zero.mpr hac'
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the shadow of `O` at the quad edge `6 → 0`: `q, 4, 3, 5` (orientation `σ`)
  obtain ⟨σ, hσ, -, E1, E2, E3, E4⟩ := quad_edge_testsσ F.perm₂₃.swap₂.perm₁₂ hq₁ hq₂
  have mc : c ∈ ({c', c, a, a', b, b'} : Finset ℝ³) := by simp
  have ma : a ∈ ({c', c, a, a', b, b'} : Finset ℝ³) := by simp
  have ma' : a' ∈ ({c', c, a, a', b, b'} : Finset ℝ³) := by simp
  have e1c := E1 c mc (Ne.symm hac) (Ne.symm hbc) hcc'
  have e1a' := E1 a' ma' (Ne.symm haa') ha'b ha'c'
  have e2c := E2 c mc (Ne.symm hbc) (Ne.symm ha'c)
  have e3c := E3 c mc (Ne.symm ha'c) (Ne.symm hb'c)
  have e3a := E3 a ma haa' hab'
  have e4c := E4 c mc (Ne.symm hb'c) (Ne.symm hac) hcc'
  -- the planar rim `4, 3, 2, 6` of the face `2346`
  obtain ⟨μ, ν, hμ, hν, hμν, hco2⟩ := hd.sigma1.coords'
  set D := det3 (a' - b) (c' - b) (a - c') with hDdef
  obtain ⟨T1, T3, T4, T5, T6, T7, T8, R1, R2, R3, R4, R5, R6, R7, R8⟩ :=
    q_dets (u := a - c') hco2
  have hσD : 0 < σ * D := by
    have e : D = det3 (b - a) (a' - a) (a - c') := by
      simp only [hDdef, det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact e1a'
  have hμν1 : 0 < μ + ν - 1 := by linarith
  -- the four tests of the hidden vertex `1`, in the orientation `σ`
  have t1 : 0 < σ * det3 (a' - b) (c - b) (a - c') := e2c
  have t4 : 0 < σ * det3 (b - c') (c - c') (a - c') := by rw [det3_shift_xy]; exact e1c
  have t3 : 0 < σ * det3 (c' - d) (c - d) (a - c') := by
    have e : det3 (c' - d) (c - d) (a - c') = α * det3 (a - b') (c - b') (a - c') := by
      rw [hco]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e, show σ * (α * det3 (a - b') (c - b') (a - c')) =
      α * (σ * det3 (a - b') (c - b') (a - c')) by ring]
    exact mul_pos hα e4c
  have hd'c' : 0 < σ * det3 (d - a') (c' - a') (a - c') := by
    rw [T3, show σ * ((μ + ν - 1) * D) = (μ + ν - 1) * (σ * D) by ring]
    exact mul_pos hμν1 hσD
  have t2 : 0 < σ * det3 (d - a') (c - a') (a - c') := by
    refine inside_line_pos (a0 := a') (a1 := b') (a2 := a) (a3 := b) hσ ?_ e3a e3c t1 ?_ ?_ ?_
    · rw [← det3_cyc a' a b]; exact e1a'
    · have e : α * det3 (d - a') (b' - a') (a - c') = (α - 1) * det3 (d - a') (c' - a') (a - c') := by
        rw [hco]
        simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      have h : 0 < α * (σ * det3 (d - a') (b' - a') (a - c')) := by
        rw [show α * (σ * det3 (d - a') (b' - a') (a - c')) =
          σ * (α * det3 (d - a') (b' - a') (a - c')) by ring, e,
          show σ * ((α - 1) * det3 (d - a') (c' - a') (a - c')) =
            (α - 1) * (σ * det3 (d - a') (c' - a') (a - c')) by ring]
        exact mul_pos (sub_pos.mpr hα1) hd'c'
      exact (pos_of_mul_pos_right h hα.le).le
    · have e : det3 (d - a') (a - a') (a - c') = det3 (d - a') (c' - a') (a - c') := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact hd'c'
    · rw [T4, show σ * (ν * D) = ν * (σ * D) by ring]; exact (mul_pos hν hσD).le
  -- `5`, over the chord from `6` to the far end `2`
  have hb'0 : b' = a + α⁻¹ • (d - a - β • (c' - a)) := by
    rw [hco, show a + α • (b' - a) + β • (c' - a) - a - β • (c' - a) = α • (b' - a) by abel,
      smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
    abel
  have hαi : 0 < α⁻¹ := inv_pos.mpr hα
  have hαi1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα1
  have hδ : 0 < 1 - α⁻¹ + β * α⁻¹ := by nlinarith [mul_pos hβ hαi]
  -- distinct depths along `06`
  have hdep : ∀ s t, s ∈ V → t ∈ V → s ≠ t → s ≠ a → t ≠ a → ⟪s, a - c'⟫ ≠ ⟪t, a - c'⟫ :=
    fun s t hs ht hst hsa hta =>
      hgen.inner_ne_of_ne hs ht (by simp [V]) (by simp [V]) hst (Ne.symm hac') (Or.inr ⟨hsa, hta⟩)
  have mV : ∀ z, (z = d ∨ z = a' ∨ z = b ∨ z = c') → z ∈ V := by
    intro z hz; rcases hz with rfl | rfl | rfl | rfl <;> simp [V]
  have hnd6 : NoHDNAt (V.erase a) (a - c') := hnd c' (by simp [V]) a (by simp [V]) (Ne.symm hac')
  rcases lt_or_gt_of_ne (show D ≠ 0 from fun h => by rw [h, mul_zero] at hσD; exact lt_irrefl _ hσD)
    with hDn | hDp
  · -- `σ = -1`: the rim `4, 6, 2, 3` counterclockwise; `v = 6` is its corner `1`
    have hσ1 : σ = -1 := by
      rcases hσ with rfl | rfl
      · linarith
      · rfl
    rw [hσ1] at t1 t2 t3 t4
    refine isRupert_of_edgeView V {b'} (a - c') hu (k := 4) (by norm_num) (quad b c' d a') 1 a (-1)
      (by simp [V]) (by simp only [quad_1, neg_smul, one_smul, sub_neg_eq_add]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd6 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_singleton]
      exacts [hbb', Ne.symm hb'c', hdb', ha'b']
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [R1]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hμ hDn)
      · rw [R2]; exact neg_pos.mpr hDn
      · rw [R3]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hμν1 hDn)
      · rw [R4]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hμ hDn)
      · rw [R5]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hν hDn)
      · rw [R6]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hμν1 hDn)
      · rw [R7]; exact neg_pos.mpr hDn
      · rw [R8]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hν hDn)
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · exact absurd h h2
      · exact absurd h hzw
      · exact absurd h h3
      · exact absurd h h0
      · exact absurd (by simp [h]) hzM
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_rev]; linarith
        · rw [det3_rev]; linarith
        · rw [det3_rev]; linarith
        · rw [det3_rev]; linarith
      · exact absurd h h1
    · rw [quad_inner]
      refine isCyclicUnimodal_of_NWS4 (quad_injective
        (hdep b c' (mV b (by simp)) (mV c' (by simp)) hbc' (Ne.symm hab) (Ne.symm hac'))
        (hdep b d (mV b (by simp)) (mV d (by simp)) (Ne.symm hdb) (Ne.symm hab) hda)
        (hdep b a' (mV b (by simp)) (mV a' (by simp)) (Ne.symm ha'b) (Ne.symm hab) (Ne.symm haa'))
        (hdep c' d (mV c' (by simp)) (mV d (by simp)) (Ne.symm hdc') (Ne.symm hac') hda)
        (hdep c' a' (mV c' (by simp)) (mV a' (by simp)) (Ne.symm ha'c') (Ne.symm hac')
          (Ne.symm haa'))
        (hdep d a' (mV d (by simp)) (mV a' (by simp)) hda' hda (Ne.symm haa'))) ?_
      refine nws4_of_planar_quad hν hμ (by linarith) (by rw [hco2]; abel)
        (hdep b c' (mV b (by simp)) (mV c' (by simp)) hbc' (Ne.symm hab) (Ne.symm hac'))
    · intro m hm
      rw [mem_singleton.mp hm, a1, zmod4_one_sub_one]
      simp only [quad_0, quad_1, quad_2]
      refine ⟨c', α⁻¹, 1 - α⁻¹ + β * α⁻¹, Or.inl rfl, hαi, hαi1, hδ.ne', Or.inl ?_⟩
      conv_lhs => rw [hb'0]
      module
  · -- `σ = 1`: the rim `4, 3, 2, 6` counterclockwise; `v = 6` is its corner `3`
    have hσ1 : σ = 1 := by
      rcases hσ with rfl | rfl
      · rfl
      · linarith
    rw [hσ1, one_mul] at t1 t2 t3 t4
    refine isRupert_of_edgeView V {b'} (a - c') hu (k := 4) (by norm_num) (quad b a' d c') 3 a (-1)
      (by simp [V]) (by simp only [quad_3, neg_smul, one_smul, sub_neg_eq_add]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd6 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_singleton]
      exacts [hbb', ha'b', hdb', Ne.symm hb'c']
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [T1]; exact mul_pos hν hDp
      · exact hDp
      · rw [T3]; exact mul_pos hμν1 hDp
      · rw [T4]; exact mul_pos hν hDp
      · rw [T5]; exact mul_pos hμ hDp
      · rw [T6]; exact mul_pos hμν1 hDp
      · rw [T7]; exact hDp
      · rw [T8]; exact mul_pos hμ hDp
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · exact absurd h h2
      · exact absurd h hzw
      · exact absurd h h1
      · exact absurd h h0
      · exact absurd (by simp [h]) hzM
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        exacts [t1, t2, t3, t4]
      · exact absurd h h3
    · rw [quad_inner]
      refine isCyclicUnimodal_of_NWS4 (quad_injective
        (hdep b a' (mV b (by simp)) (mV a' (by simp)) (Ne.symm ha'b) (Ne.symm hab) (Ne.symm haa'))
        (hdep b d (mV b (by simp)) (mV d (by simp)) (Ne.symm hdb) (Ne.symm hab) hda)
        (hdep b c' (mV b (by simp)) (mV c' (by simp)) hbc' (Ne.symm hab) (Ne.symm hac'))
        (hdep a' d (mV a' (by simp)) (mV d (by simp)) (Ne.symm hda') (Ne.symm haa') hda)
        (hdep a' c' (mV a' (by simp)) (mV c' (by simp)) ha'c' (Ne.symm haa') (Ne.symm hac'))
        (hdep d c' (mV d (by simp)) (mV c' (by simp)) hdc' hda (Ne.symm hac'))) ?_
      exact nws4_of_planar_quad hμ hν hμν hco2
        (hdep b a' (mV b (by simp)) (mV a' (by simp)) (Ne.symm ha'b) (Ne.symm hab) (Ne.symm haa'))
    · intro m hm
      rw [mem_singleton.mp hm, a3, zmod4_three_sub_one]
      simp only [quad_0, quad_2, quad_3]
      refine ⟨c', 1 - α⁻¹, 1 - α⁻¹ + β * α⁻¹, Or.inl rfl, by linarith, by linarith, hδ.ne',
        Or.inr ?_⟩
      conv_lhs => rw [hb'0]
      module

/-- **Lemma 3 of §9 at `6 → 0`.**  If `6 → 0` is a quad edge of `O6` (`1` hidden: the facet
inequalities at `134`, `135`) that is not bad, `K` is Rupert: for `α < 1`, `2` is a middle
of `0256` at the view along `06` (Lemma 2 (b)); for `α > 1`, Lemma 3 (c)
(`isRupert_type21_60_far`); `α = 1` would make `25 ∥ 06` (`GenPos`). -/
theorem isRupert_type21_60 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.a'bc.f c' < F.a'bc.f a) (hq₂ : F.a'b'c.f c' < F.a'b'c.f a)
    (hgood : ¬ max ⟪a, a - c'⟫ ⟪a', a - c'⟫ ≤ min ⟪b, a - c'⟫ ⟪b', a - c'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨α, β, hα, hβ, hαβ, hco⟩ := hd.coords'
  rcases lt_trichotomy α 1 with hα1 | hα1 | hα1
  · have hmid : QuadMiddle c' a b b' d :=
      ⟨α, -β, hα, hα1, by linarith, by linarith, Or.inr (by rw [hco]; module)⟩
    rw [← (type21_set a a' b b' c c' d).2.2.2.1] at hgen hnd ⊢
    exact isRupert_quad_edge_lift F.perm₂₃.swap₂.perm₁₂ hq₁ hq₂ hgood (Or.inl hmid)
      ⟨hdc', hdc, hda, hda', hdb, hdb'⟩
      (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) (Ne.symm hac')
        ⟨ha'c', Ne.symm haa', hbc', Ne.symm hab, hb'c', Ne.symm hab'⟩)
      (noHDN_pair hnd (by simp) (by simp) (Ne.symm hac'))
  · exfalso
    refine hgen.ne_smul (s := b') (t := d) (x := a) (y := c') (by simp) (by simp) (by simp)
      (by simp) (Ne.symm hdb') hac' ⟨hda, hdc'⟩ β ?_
    rw [hco, hα1]; module
  · exact isRupert_type21_60_far F hd hq₁ hq₂ hα hβ hco hα1 hgen hnd

/-! ### Lemma 3 (b): `5 → 0` with the cap the far end, through `O2 = K − 6` -/

/-- Two facets through `P Q` with a combination constant along `u`, negative at `r` and
`w`: the tests of `r` and `w` at the line `P Q` have one sign. -/
theorem det3_mul_pos_of_combo {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³}
    (hr : det3 (Q - P) (r - P) u ≠ 0) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) :
    0 < det3 (Q - P) (r - P) u * det3 (Q - P) (w - P) u := by
  have e : ∀ z, det3 (P - Q) (z - Q) u = -det3 (Q - P) (z - P) u := fun z => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rcases lt_or_gt_of_ne hr with hn | hp
  · have := det3_pos_of_combo h₁ h₂ h1Q h1P h2Q h2P hαβ (r := r) (w := w)
      (by rw [e]; linarith) hgr hgw
    rw [e] at this
    nlinarith
  · exact mul_pos hp (det3_pos_of_combo h₁ h₂ h1P h1Q h2P h2Q hαβ hp hgr hgw)

/-- **Step 3 of Lemma 3 (b), in reals.**  Depths `z` along `u = 0 − 5` (`uu = ⟪u, u⟫`): the
middle `6 = 0 + (2 − 0)/β + (α/β) u` lies above the diagonal `0 – 2` (`hc'`); the identity
`D (1 − 3) = S1 (6 − 3) − SA (2 − 3) + λ u` of the point `1` in the frame `6, 2, 3` on the
screen (`D = S_{623}`), applied to the face `2346` (`hf`: `fc = f(1) < 0`, `Nu = ⟪N, u⟫ > 0`,
the up face) and to the depth (`hz`); `D S1 > 0` (`1`, `6` on one side of the side `23` of
`S_K`) and `D SA > 0` (the side `36` of `S_O` against the far end `2`).  If `5 → 0` is not
bad in `O6`, it is not bad in `O2`. -/
theorem type21_far_not_bad_core {za za' zc zc' zd uu α β D S1 SA SB lam fc Nu : ℝ}
    (huu : 0 < uu) (hα : 0 < α) (hβ : 1 < β)
    (hc' : β * zc' = β * za + (zd - za) + α * uu)
    (hf : -(D * fc) = lam * Nu)
    (hz : S1 * zc' - SA * zd + SB * za' - D * zc = lam * uu)
    (hsum : S1 - SA + SB - D = 0)
    (hS1 : 0 < D * S1) (hSA : 0 < D * SA) (hfc : fc < 0) (hNu : 0 < Nu)
    (hgoodO : ¬ max za za' ≤ min zc zc') : ¬ max za za' ≤ min zc zd := by
  intro hbad
  rw [max_le_iff, le_min_iff, le_min_iff] at hbad
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  have hD : D ≠ 0 := by rintro rfl; simp at hS1
  have hD2 : 0 < D * D := mul_self_pos.mpr hD
  have hlam : 0 < lam * D := by
    have e : (lam * D) * Nu = -(D * D * fc) := by linear_combination (-D) * hf
    have : 0 < (lam * D) * Nu := by rw [e]; nlinarith
    by_contra hneg
    push Not at hneg
    nlinarith
  have hza : za < zc' := by nlinarith [mul_pos hα huu]
  have hzc' : zc' < za' := by
    by_contra hcon
    push Not at hcon
    apply hgoodO
    rw [max_le_iff, le_min_iff, le_min_iff]
    exact ⟨⟨h1, hza.le⟩, h3, hcon⟩
  have key : D * D * (za' - zc) =
      lam * D * uu - D * S1 * (zc' - za') + D * SA * (zd - za') := by
    have hSB : SB = D - S1 + SA := by linarith
    rw [hSB] at hz
    linear_combination D * hz
  have : 0 < D * D * (za' - zc) := by
    rw [key]
    nlinarith [mul_pos hlam huu, mul_neg_of_pos_of_neg hS1 (sub_neg.mpr hzc'),
      mul_nonneg hSA.le (sub_nonneg.mpr h4)]
  nlinarith

/-- **Lemma 3 (b) of §9 at `5 → 0`.**  If `5 → 0` is a quad edge of `O6` (`4` hidden: the
facet inequalities at `134`, `346`) that is not bad, then `β > 1`: the far end of `0256` at
the view along `05` is `2` and `6` is the middle.  So `K`'s test is the test of
`O2 = K − 6` at its quad edge `5 → 0` (the same facet inequalities: `134` is a face of `O2`
and `234` lies in the plane of `346`), with `6` a middle; that edge is not bad in `O2`
(`type21_far_not_bad_core`), and Lemma 2 for `O2` gives a passage. -/
theorem isRupert_type21_50 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.a'bc.f b' < F.a'bc.f a) (hq₂ : F.a'bc'.f b' < F.a'bc'.f a)
    (hgood : ¬ max ⟪a, a - b'⟫ ⟪a', a - b'⟫ ≤ min ⟪c, a - b'⟫ ⟪c', a - b'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨α, β, hα, hβ, hαβ, hco⟩ := hd.coords'
  have hβ1 : 1 < β := by
    have hf := affine_frame F.a'bc'.hN a b' c' α β
    rw [← hco, hd.a'bc', F.a'bc'.hR] at hf
    have n := F.a'bc'.neg a (by simp) haa' hab hac'
    nlinarith [mul_lt_mul_of_pos_left hq₂ hα]
  have hu : a - b' ≠ 0 := sub_ne_zero.mpr hab'
  -- the shadow of `O6` at the quad edge `5 → 0`: `q, 1, 3, 6` (orientation `σ`)
  obtain ⟨σ, hσ, -, E1, E2, E3, E4⟩ := quad_edge_testsσ F.swap₂.perm₁₂ hq₁ hq₂
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have e3c := E3 c (by simp) (Ne.symm ha'c) hcc'
  have e4a' := E4 a' (by simp) ha'c' (Ne.symm haa') ha'b'
  -- `D = S_{623} = (1 − β) det (0 6 3)`
  have hDX : det3 (d - c') (a' - c') (a - b') =
      (1 - β) * det3 (a - c') (a' - c') (a - b') := by
    rw [hco]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hX : det3 (a - c') (a' - c') (a - b') ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e4a'; exact lt_irrefl _ e4a'
  have hD : det3 (d - c') (a' - c') (a - b') ≠ 0 := by
    rw [hDX]; exact mul_ne_zero (by linarith) hX
  -- `D SA > 0`
  have hDSA : 0 < det3 (d - c') (a' - c') (a - b') * det3 (a' - c') (c - c') (a - b') := by
    rw [hDX, det3_rev a' c' c]
    have hXY : 0 < det3 (a - c') (a' - c') (a - b') * det3 (c' - a') (c - a') (a - b') := by
      have h := mul_pos e4a' e3c
      have e : σ * det3 (a - c') (a' - c') (a - b') * (σ * det3 (c' - a') (c - a') (a - b')) =
          det3 (a - c') (a' - c') (a - b') * det3 (c' - a') (c - a') (a - b') := by
        rw [show σ * det3 (a - c') (a' - c') (a - b') * (σ * det3 (c' - a') (c - a') (a - b')) =
          (σ * σ) * (det3 (a - c') (a' - c') (a - b') * det3 (c' - a') (c - a') (a - b')) by ring,
          hσ2, one_mul]
      linarith
    nlinarith [mul_pos (sub_pos.mpr hβ1) hXY]
  -- `D S1 > 0`: the silhouette edge `23` between the faces `2346` and `235`
  have hN₁ : 0 < ⟪F.a'bc'.N, a - b'⟫ := by rw [← F.a'bc'.hN]; linarith
  have hN₂ : ⟪hd.f235.N, a - b'⟫ < 0 := by
    rw [← hd.f235.hN, hd.f235.hP]
    have := hd.f235.neg a (by simp) hab' haa' hda.symm
    linarith
  have hf235c' : hd.f235.f c' < 0 := hd.sigma2.abc'
  have hDS1 : 0 < det3 (d - c') (a' - c') (a - b') * det3 (a' - d) (c - d) (a - b') := by
    have e : det3 (d - c') (a' - c') (a - b') = det3 (a' - d) (c' - d) (a - b') := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]
    refine det3_mul_pos_of_combo F.a'bc'.hN hd.f235.hN hd.a'bc' F.a'bc'.hP hd.f235.hR
      hd.f235.hQ (α := -⟪hd.f235.N, a - b'⟫) (β := ⟪F.a'bc'.N, a - b'⟫) (by ring)
      (by rw [← e]; exact hD) ?_ ?_
    · rw [F.a'bc'.hR]; nlinarith
    · have n1 := F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
      have n2 := hd.f235.neg c (by simp) (Ne.symm hb'c) (Ne.symm ha'c) hdc.symm
      nlinarith [mul_pos (neg_pos.mpr hN₂) (neg_pos.mpr n1), mul_pos hN₁ (neg_pos.mpr n2)]
  -- the identity of `1` in the frame `6, 2, 3`
  have hpar := four_point_parallel c' d a' c (a - b') hu
  have hsum := four_point_sum c' d a' c (a - b')
  set S1 := det3 (a' - d) (c - d) (a - b') with hS1
  set SA := det3 (a' - c') (c - c') (a - b') with hSA
  set SB := det3 (d - c') (c - c') (a - b') with hSB
  set D := det3 (d - c') (a' - c') (a - b') with hDdef
  set uu := ⟪a - b', a - b'⟫ with huu
  set Nu := ⟪F.a'bc'.N, a - b'⟫ with hNu
  set lam := ⟪S1 • c' - SA • d + SB • a' - D • c, a - b'⟫ / uu with hlam
  have hL : S1 • c' - SA • d + SB • a' - D • c =
      S1 • (c' - c) - SA • (d - c) + SB • (a' - c) := by
    rw [show D = S1 - SA + SB by linarith]; module
  have hf : -(D * F.a'bc'.f c) = lam * Nu := by
    have e1 : ⟪F.a'bc'.N, S1 • c' - SA • d + SB • a' - D • c⟫ = lam * Nu := by
      rw [hpar, real_inner_smul_right]
    rw [hL, inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← F.a'bc'.hN, ← F.a'bc'.hN, ← F.a'bc'.hN, F.a'bc'.hR, hd.a'bc',
      F.a'bc'.hP] at e1
    rw [← e1, show D = S1 - SA + SB by linarith]; ring
  have hz : S1 * ⟪c', a - b'⟫ - SA * ⟪d, a - b'⟫ + SB * ⟪a', a - b'⟫ - D * ⟪c, a - b'⟫ =
      lam * uu := by
    have e1 : ⟪S1 • c' - SA • d + SB • a' - D • c, a - b'⟫ = lam * uu := by
      rw [hpar, real_inner_smul_left]
    rw [inner_sub_left, inner_add_left, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left] at e1
    exact e1
  have hc' : β * ⟪c', a - b'⟫ = β * ⟪a, a - b'⟫ + (⟪d, a - b'⟫ - ⟪a, a - b'⟫) + α * uu := by
    have e : ⟪d, a - b'⟫ = ⟪a, a - b'⟫ + α * ⟪b' - a, a - b'⟫ +
        β * (⟪c', a - b'⟫ - ⟪a, a - b'⟫) := by
      rw [hco]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
    have e' : ⟪b' - a, a - b'⟫ = -uu := by rw [huu, ← neg_sub a b', inner_neg_left]
    rw [e'] at e
    linarith
  have hgood2 : ¬ max ⟪a, a - b'⟫ ⟪a', a - b'⟫ ≤ min ⟪c, a - b'⟫ ⟪d, a - b'⟫ :=
    type21_far_not_bad_core (real_inner_self_pos.mpr hu) hα hβ1 hc' hf hz hsum hDS1 hDSA
      (F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc') hN₁ hgood
  -- `6` is a middle over the chord from `0` to the far end `2`
  have hβ0 : β ≠ 0 := by linarith
  have hβi : 0 < β⁻¹ := inv_pos.mpr (by linarith)
  have hmid : QuadMiddle b' a c d c' := by
    refine ⟨β⁻¹, α * β⁻¹, hβi, inv_lt_one_of_one_lt₀ hβ1, (mul_pos hα hβi).ne', ?_, Or.inr ?_⟩
    · have := inv_lt_one_of_one_lt₀ hβ1
      exact (show 0 < α * β⁻¹ + 1 - β⁻¹ by linarith [mul_pos hα hβi]).ne'
    · calc c' = a + β⁻¹ • (β • (c' - a)) := by
            rw [smul_smul, inv_mul_cancel₀ hβ0, one_smul]; abel
        _ = a + β⁻¹ • (d - a) + (α * β⁻¹) • (a - b') := by
            rw [show β • (c' - a) = d - a - α • (b' - a) by rw [hco]; abel]; module
  rw [← (type21_set a a' b b' c c' d).2.1] at hgen hnd ⊢
  exact isRupert_quad_edge_lift hd.O2.swap₂ hq₁ hq₂ hgood2 (Or.inl hmid)
    ⟨Ne.symm hb'c', Ne.symm hbc', Ne.symm hac', Ne.symm ha'c', Ne.symm hcc', Ne.symm hdc'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) (Ne.symm hab')
      ⟨ha'b', Ne.symm haa', Ne.symm hb'c, Ne.symm hac, hdb', hda⟩)
    (noHDN_pair hnd (by simp) (by simp) (Ne.symm hab'))

/-! ### The images under `σ1 = (04)(35)` -/

/-- **Lemma 3 of §9 at `4 → 3`** (`σ1` of `0 → 5`). -/
theorem isRupert_type21_43 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.ab'c.f b < F.ab'c.f a') (hq₂ : F.ab'c'.f b < F.ab'c'.f a')
    (hgood : ¬ max ⟪a', a' - b⟫ ⟪a, a' - b⟫ ≤ min ⟪c, a' - b⟫ ⟪c', a' - b⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rw [← (type21_set a a' b b' c c' d).2.2.2.2] at hgen hnd ⊢
  exact isRupert_type21_05 F.perm₁₂ hd.sigma1 hq₁ hq₂ hgood hgen hnd

/-- **Lemma 3 of §9 at `3 → 4`** (`σ1` of `5 → 0`). -/
theorem isRupert_type21_34 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.ab'c.f a' < F.ab'c.f b) (hq₂ : F.ab'c'.f a' < F.ab'c'.f b)
    (hgood : ¬ max ⟪b, b - a'⟫ ⟪b', b - a'⟫ ≤ min ⟪c, b - a'⟫ ⟪c', b - a'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rw [← (type21_set a a' b b' c c' d).2.2.2.2] at hgen hnd ⊢
  exact isRupert_type21_50 F.perm₁₂ hd.sigma1 hq₁ hq₂ hgood hgen hnd

/-- **Lemma 3 of §9 at `4 → 6`** (`σ1` of `0 → 6`). -/
theorem isRupert_type21_46 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.ab'c.f b < F.ab'c.f c') (hq₂ : F.a'b'c.f b < F.a'b'c.f c')
    (hgood : ¬ max ⟪c', c' - b⟫ ⟪c, c' - b⟫ ≤ min ⟪a, c' - b⟫ ⟪a', c' - b⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rw [← (type21_set a a' b b' c c' d).2.2.2.2] at hgen hnd ⊢
  exact isRupert_type21_06 F.perm₁₂ hd.sigma1 hq₁ hq₂ hgood hgen hnd

/-- **Lemma 3 of §9 at `6 → 4`** (`σ1` of `6 → 0`). -/
theorem isRupert_type21_64 (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    (hq₁ : F.ab'c.f c' < F.ab'c.f b) (hq₂ : F.a'b'c.f c' < F.a'b'c.f b)
    (hgood : ¬ max ⟪b, b - c'⟫ ⟪b', b - c'⟫ ≤ min ⟪a, b - c'⟫ ⟪a', b - c'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rw [← (type21_set a a' b b' c c' d).2.2.2.2] at hgen hnd ⊢
  exact isRupert_type21_60 F.perm₁₂ hd.sigma1 hq₁ hq₂ hgood hgen hnd

end Lift

end Minimality

end
