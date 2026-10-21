module

public import Minimality.Type29Lift

@[expose] public section

/-!
# Type 29: Theorem P of §12 (`FEWER-FACES-PROOFS.md` §12), partial

Labels of §12 with `a, a', b, b', c, c', d = 0, 4, 1, 3, 2, 5, 6`: the octahedron
`O = K − 6` has the opposite pairs `(0, 4)`, `(1, 3)`, `(2, 5)` (`F : OctFacets a a' b b' c c'`),
and the cap `6` lies on the plane `145` (`a'bc'`), strictly beyond `345` (`a'b'c'`) and
strictly beneath the other six faces of `O` (`IsCap29`); conversely such a point gives
type 29 (Lemma 0 (a)).  The automorphism `σ = (0 2)(4 5)` is `IsCap29.sigma`.

* **Lemma 0 (b)** — `IsCap29.coords`: `6 = 1 + s (4 − 1) + t (5 − 1)` with `s, t > 0`,
  `s + t > 1`.
* **Lemma 3 (the quad edges at 1 always lift)** — (a) `isRupert_type29_14`: a quad edge
  `1 → 4` of `O` forces `t < 1`, so `6` is a middle (Lemma 2); (b)
  `isRupert_type29_41`: a quad edge `4 → 1` with `t < 1` lifts by Lemma 2, with `t > 1`
  by the far-end lift `isRupert_lift_far` (`Type29Lift.lean`: the up/down-face rule
  and the contradiction argument); `t = 1` would make `56 ∥ 14`.  At `15`:
  `isRupert_type29_15`, `isRupert_type29_51` (by `σ`).
* **Lemma 4 (the cap is hidden)** — `type29_hidden_03`, `type29_hidden_05` (and by `σ`
  `2 → 3`, `2 → 4`): at the views along these quad edges `6` is hidden
  (`quadHidden_of_beneath`; the paper's finer `P6 ∈ int P(345)` is not needed), so
  Lemma 2 applies: `isRupert_type29_03`, `isRupert_type29_05`, `isRupert_type29_23`,
  `isRupert_type29_24`.
* **Theorem P** — `isRupert_type29_C1` (clause C1: an inner-tailed quad edge of `O` in
  `G = {1→4, 4→1, 1→5, 5→1, 0→3, 0→5, 2→3, 2→4}`, `Type29C1`), `isRupert_type29_C2`
  (clause C2: `K − 5` an octahedron with an inner-tailed quad edge along `14` with
  `t > 1` or along `46` with `s < 1`, `Type29C2`; `K − 4` by `σ`),
  `isRupert_type29_C3` (clause C3: an inner-tailed quad edge of any octahedron `K − m`
  with `m` hidden), and `isRupert_type29_P` (any of them).  General position: `GenPos`
  (no two segments parallel or orthogonal: distinct depths, no touching, `s, t ≠ 1`),
  `NoPlaneParallel` (Lemma 3 (b)'s corner condition), `NoHDNAt` at the views along the
  segments (no horizontal double normal), and no planar equator (`κ ≠ 0`) of the
  octahedron used.  Theorem P is partial: it does not show that some clause always
  holds, so there is no `not_type29_of_isNopert`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### General position at an edge view -/

theorem genPos_hinj {V : Finset ℝ³} (hg : GenPos V) {x y y' p p' : ℝ³} (hx : x ∈ V)
    (hy : y ∈ V) (hy' : y' ∈ V) (hp : p ∈ V) (hp' : p' ∈ V) (hxy : x ≠ y)
    (hne : y' ≠ x ∧ y' ≠ y ∧ p ≠ x ∧ p ≠ y ∧ p' ≠ x ∧ p' ≠ y) :
    ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫ := by
  intro s t hs ht hst
  have hsV : s ∈ V := by rcases hs with rfl | rfl | rfl | rfl | rfl <;> assumption
  have htV : t ∈ V := by rcases ht with rfl | rfl | rfl <;> assumption
  have htxy : t ≠ x ∧ t ≠ y := by rcases ht with rfl | rfl | rfl <;> tauto
  exact hg.inner_ne_of_ne hsV htV hx hy hst hxy (Or.inl htxy)

theorem noHDN_pair {V : Finset ℝ³}
    (hnd : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → NoHDNAt (V.erase w) (w - v)) {x y : ℝ³} (hx : x ∈ V)
    (hy : y ∈ V) (hxy : x ≠ y) : NoHDNAt (V.erase x) (y - x) ∧ NoHDNAt (V.erase y) (y - x) :=
  ⟨by simpa only [neg_sub] using (hnd y hy x hx (Ne.symm hxy)).neg, hnd x hx y hy hxy⟩

/-! ### The cap -/

/-- The cap `d` (`6`) of a type-29 point set over the octahedron `O` with opposite
pairs `(a, a') = (0, 4)`, `(b, b') = (1, 3)`, `(c, c') = (2, 5)`: on the plane of
`a'bc'` (`145`, which becomes the quadrilateral `1456`), strictly beyond `a'b'c'`
(`345`), strictly beneath the other six faces. -/
structure IsCap29 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop where
  a'bc' : F.a'bc'.f d = 0
  a'b'c' : 0 < F.a'b'c'.f d
  abc : F.abc.f d < 0
  abc' : F.abc'.f d < 0
  ab'c : F.ab'c.f d < 0
  ab'c' : F.ab'c'.f d < 0
  a'bc : F.a'bc.f d < 0
  a'b'c : F.a'b'c.f d < 0

/-- The automorphism `σ = (0 2)(4 5)` of type 29. -/
theorem IsCap29.sigma {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    IsCap29 F.perm₂₃.perm₁₂.perm₂₃ d :=
  ⟨h.a'bc', h.a'b'c', h.abc, h.a'bc, h.ab'c, h.a'b'c, h.abc', h.ab'c'⟩

theorem IsCap29.ne {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    d ≠ a ∧ d ≠ a' ∧ d ≠ b ∧ d ≠ b' ∧ d ≠ c ∧ d ≠ c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have := h.abc; rw [F.abc.hP] at this; exact lt_irrefl _ this
  · have := h.a'bc; rw [F.a'bc.hP] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hQ] at this; exact lt_irrefl _ this
  · have := h.ab'c; rw [F.ab'c.hQ] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hR] at this; exact lt_irrefl _ this
  · have := h.abc'; rw [F.abc'.hR] at this; exact lt_irrefl _ this

/-- **Lemma 0 (b) of §12.**  `6 = 1 + s (4 − 1) + t (5 − 1)` with `s, t > 0` (`6` is
beneath `015` and `124`) and `s + t > 1` (`6` is beyond `345`). -/
theorem IsCap29.coords {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    0 < F.abc'.f d / F.abc'.f a' ∧ 0 < F.a'bc.f d / F.a'bc.f c' ∧
      1 < F.abc'.f d / F.abc'.f a' + F.a'bc.f d / F.a'bc.f c' ∧
      d = b + (F.abc'.f d / F.abc'.f a') • (a' - b) + (F.a'bc.f d / F.a'bc.f c') • (c' - b) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n0 := F.a'bc'.neg a (by simp) haa' hab hac'
  have n1 := F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c'
  have n2 := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc')
  have hco := coords_of_affine3 F.a'bc'.hN F.abc'.hN F.a'bc.hN F.a'bc'.hQ F.a'bc'.hP
    F.a'bc'.hR h.a'bc' n0.ne F.abc'.hQ F.abc'.hR n1.ne F.a'bc.hQ F.a'bc.hP n2.ne
  set s := F.abc'.f d / F.abc'.f a'
  set t := F.a'bc.f d / F.a'bc.f c'
  refine ⟨div_pos_of_neg_of_neg h.abc' n1, div_pos_of_neg_of_neg h.a'bc n2, ?_, hco⟩
  have hf := affine_frame F.a'b'c'.hN b a' c' s t
  rw [← hco, F.a'b'c'.hP, F.a'b'c'.hR] at hf
  have := F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc'
  nlinarith [h.a'b'c']

theorem type29_set (a a' b b' c c' d : ℝ³) :
    (insert d ({b, b', a', a, c, c'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({a', a, b, b', c, c'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({a, a', b', b, c, c'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({a, a', c', c, b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({c, c', b, b', a, a'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

/-! ### Lemma 3: the quad edges at 1 always lift -/

/-- **Lemma 3 (a) of §12.**  If `1 → 4` is a quad edge of `O` (`3` hidden; the facet
inequalities at `023`, `035`) that is not bad, then `t < 1` (Lemma 9.1 (a) for `035`
and `6` beneath `035`), so `6` is a middle of the quad at the view along `14`, and by
Lemma 2 `K` is Rupert. -/
theorem isRupert_type29_14 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d)
    (hq₁ : F.ab'c.f b < F.ab'c.f a') (hq₂ : F.ab'c'.f b < F.ab'c'.f a')
    (hgood : ¬ max ⟪a', a' - b⟫ ⟪a, a' - b⟫ ≤ min ⟪c, a' - b⟫ ⟪c', a' - b⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨hs, ht, hst, hco⟩ := hd.coords
  set s := F.abc'.f d / F.abc'.f a'
  set t := F.a'bc.f d / F.a'bc.f c'
  -- `t < 1`
  have ht1 : t < 1 := by
    have hf := affine_frame F.ab'c'.hN b a' c' s t
    rw [← hco, F.ab'c'.hR] at hf
    have n := F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c'
    have hdn := hd.ab'c'
    nlinarith [mul_lt_mul_of_pos_left hq₂ hs]
  have hmid : QuadMiddle b a' c c' d :=
    ⟨t, s + t - 1, ht, ht1, by linarith, by linarith, Or.inr (by rw [hco]; module)⟩
  rw [← (type29_set a a' b b' c c' d).1]
  rw [← (type29_set a a' b b' c c' d).1] at hgen hnd
  exact isRupert_quad_edge_lift F.swap₁.perm₁₂ hq₁ hq₂ hgood (Or.inl hmid)
    ⟨hdb, hdb', hda', hda, hdc, hdc'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) (Ne.symm ha'b)
      ⟨hab, haa', Ne.symm hbc, Ne.symm ha'c, Ne.symm hbc', Ne.symm ha'c'⟩)
    (noHDN_pair hnd (by simp) (by simp) (Ne.symm ha'b))

/-- **Lemma 3 (b) of §12.**  If `4 → 1` is a quad edge of `O` (`0` hidden; the facet
inequalities at `023`, `035`) that is not bad, then `K` is Rupert: for `t < 1`, `6` is a
middle at the view along `14` (Lemma 2); for `t > 1`, `6` is the far end and `5` the
middle, and `isRupert_lift_far` (rim `v, 2, 3, 6` or the triangle `v, 2, 6`; the claim
through the down face `234`; `K` not bad by the up face `356`) applies.  `t = 1` would
make `56` parallel to `14` (`GenPos`); `NoPlaneParallel` gives the corner condition at
`3`. -/
theorem isRupert_type29_41 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d)
    (hq₁ : F.ab'c.f a' < F.ab'c.f b) (hq₂ : F.ab'c'.f a' < F.ab'c'.f b)
    (hgood : ¬ max ⟪b, b - a'⟫ ⟪b', b - a'⟫ ≤ min ⟪c, b - a'⟫ ⟪c', b - a'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hpar : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨hs, ht, hst, hco⟩ := hd.coords
  set s := F.abc'.f d / F.abc'.f a'
  set t := F.a'bc.f d / F.a'bc.f c'
  have hpair := noHDN_pair hnd (x := a') (y := b) (by simp) (by simp) ha'b
  rw [← (type29_set a a' b b' c c' d).2.1]
  rw [← (type29_set a a' b b' c c' d).2.1] at hpair
  rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
  · have hmid : QuadMiddle a' b c c' d :=
      ⟨t, -s, ht, ht1, by linarith, by linarith, Or.inr (by rw [hco]; module)⟩
    exact isRupert_quad_edge_lift F.swap₁ hq₁ hq₂ hgood (Or.inl hmid)
      ⟨hda', hda, hdb, hdb', hdc, hdc'⟩
      (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) ha'b
        ⟨Ne.symm ha'b', Ne.symm hbb', Ne.symm ha'c, Ne.symm hbc, Ne.symm ha'c', Ne.symm hbc'⟩)
      hpair
  · exfalso
    refine hgen.ne_smul (s := c') (t := d) (x := b) (y := a') (by simp) (by simp) (by simp)
      (by simp) (Ne.symm hdc') (Ne.symm ha'b) ⟨hdb, hda'⟩ s ?_
    · rw [hco, ht1]; module
  · refine isRupert_lift_far F.swap₁ hq₁ hq₂ hgood hs ht1 hco hd.a'bc hd.a'b'c hd.ab'c
      hd.a'b'c' hd.ab'c' ⟨hda', hda, hdb, hdb', hdc, hdc'⟩ ?_
      (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) ha'b
        ⟨Ne.symm ha'b', Ne.symm hbb', Ne.symm ha'c, Ne.symm hbc, hda', hdb⟩) hpair
    exact hpar b' (by simp) d (by simp) c (by simp) a' (by simp) b (by simp)
      (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, and_true]
          exact ⟨⟨Ne.symm hdb', hb'c, Ne.symm ha'b', Ne.symm hbb'⟩, ⟨hdc, hda', hdb⟩,
            ⟨Ne.symm ha'c, Ne.symm hbc⟩, ha'b, not_false⟩)

/-- **Lemma 3 (a) at `15`** (the `σ`-image of `isRupert_type29_14`): a quad edge
`1 → 5` of `O` (facets `023`, `234`) that is not bad gives a passage. -/
theorem isRupert_type29_15 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d)
    (hq₁ : F.ab'c.f b < F.ab'c.f c') (hq₂ : F.a'b'c.f b < F.a'b'c.f c')
    (hgood : ¬ max ⟪c', c' - b⟫ ⟪c, c' - b⟫ ≤ min ⟪a, c' - b⟫ ⟪a', c' - b⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have e := (type29_set a a' b b' c c' d).2.2.2.2
  rw [← e] at hgen hnd ⊢
  exact isRupert_type29_14 F.perm₂₃.perm₁₂.perm₂₃ hd.sigma hq₁ hq₂ hgood hgen hnd

/-- **Lemma 3 (b) at `15`** (the `σ`-image of `isRupert_type29_41`): a quad edge
`5 → 1` of `O` that is not bad gives a passage. -/
theorem isRupert_type29_51 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d)
    (hq₁ : F.ab'c.f c' < F.ab'c.f b) (hq₂ : F.a'b'c.f c' < F.a'b'c.f b)
    (hgood : ¬ max ⟪b, b - c'⟫ ⟪b', b - c'⟫ ≤ min ⟪a, b - c'⟫ ⟪a', b - c'⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hpar : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have e := (type29_set a a' b b' c c' d).2.2.2.2
  rw [← e] at hgen hpar hnd ⊢
  exact isRupert_type29_41 F.perm₂₃.perm₁₂.perm₂₃ hd.sigma hq₁ hq₂ hgood hgen hpar hnd

/-! ### Lemma 4: the cap is hidden -/

/-- **Lemma 4 of §12 at `0 → 3`.**  If `0 → 3` is a quad edge of `O` (`4` hidden;
facets `124`, `145`), the cap `6` is hidden at its view: it is beneath the six faces
`023`, `035`, `012`, `124`, `015` and on `145` (`quadHidden_of_beneath`). -/
theorem type29_hidden_03 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.a'bc.f a < F.a'bc.f b') (hq₂ : F.a'bc'.f a < F.a'bc'.f b') :
    QuadHidden a b' b c c' d :=
  quadHidden_of_beneath F.swap₂ hq₁ hq₂ hd.ab'c hd.ab'c'
    ⟨hd.abc.le, hd.a'bc.le, Or.inl hd.abc⟩ ⟨hd.abc'.le, hd.a'bc'.le, Or.inl hd.abc'⟩

/-- **Lemma 4 of §12 at `0 → 5`** (`4` hidden; facets `124`, `234`): `6` is beneath all
six faces used. -/
theorem type29_hidden_05 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.a'bc.f a < F.a'bc.f c') (hq₂ : F.a'b'c.f a < F.a'b'c.f c') :
    QuadHidden a c' c b b' d :=
  quadHidden_of_beneath F.perm₂₃.swap₂ hq₁ hq₂ hd.abc' hd.ab'c'
    ⟨hd.abc.le, hd.a'bc.le, Or.inl hd.abc⟩ ⟨hd.ab'c.le, hd.a'b'c.le, Or.inl hd.ab'c⟩

/-- **Lemma 4 with Lemma 2 at `0 → 3`.** -/
theorem isRupert_type29_03 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.a'bc.f a < F.a'bc.f b') (hq₂ : F.a'bc'.f a < F.a'bc'.f b')
    (hgood : ¬ max ⟪b', b' - a⟫ ⟪b, b' - a⟫ ≤ min ⟪c, b' - a⟫ ⟪c', b' - a⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have e := (type29_set a a' b b' c c' d).2.2.1
  rw [← e] at hgen hnd ⊢
  exact isRupert_quad_edge_lift F.swap₂ hq₁ hq₂ hgood (Or.inr (type29_hidden_03 F hd hq₁ hq₂))
    ⟨hda, hda', hdb', hdb, hdc, hdc'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hab'
      ⟨Ne.symm hab, hbb', Ne.symm hac, Ne.symm hb'c, Ne.symm hac', Ne.symm hb'c'⟩)
    (noHDN_pair hnd (by simp) (by simp) hab')

/-- **Lemma 4 with Lemma 2 at `0 → 5`.** -/
theorem isRupert_type29_05 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.a'bc.f a < F.a'bc.f c') (hq₂ : F.a'b'c.f a < F.a'b'c.f c')
    (hgood : ¬ max ⟪c', c' - a⟫ ⟪c, c' - a⟫ ≤ min ⟪b, c' - a⟫ ⟪b', c' - a⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have e := (type29_set a a' b b' c c' d).2.2.2.1
  rw [← e] at hgen hnd ⊢
  exact isRupert_quad_edge_lift F.perm₂₃.swap₂ hq₁ hq₂ hgood
    (Or.inr (type29_hidden_05 F hd hq₁ hq₂)) ⟨hda, hda', hdc', hdc, hdb, hdb'⟩
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hac'
      ⟨Ne.symm hac, hcc', Ne.symm hab, hbc', Ne.symm hab', hb'c'⟩)
    (noHDN_pair hnd (by simp) (by simp) hac')

/-- **Lemma 4 with Lemma 2 at `2 → 3`** (`σ` of `0 → 3`; facets `015`, `145`). -/
theorem isRupert_type29_23 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.abc'.f c < F.abc'.f b') (hq₂ : F.a'bc'.f c < F.a'bc'.f b')
    (hgood : ¬ max ⟪b', b' - c⟫ ⟪b, b' - c⟫ ≤ min ⟪a, b' - c⟫ ⟪a', b' - c⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have e := (type29_set a a' b b' c c' d).2.2.2.2
  rw [← e] at hgen hnd ⊢
  exact isRupert_type29_03 F.perm₂₃.perm₁₂.perm₂₃ hd.sigma hq₁ hq₂ hgood hgen hnd

/-- **Lemma 4 with Lemma 2 at `2 → 4`** (`σ` of `0 → 5`; facets `015`, `035`). -/
theorem isRupert_type29_24 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (hq₁ : F.abc'.f c < F.abc'.f a') (hq₂ : F.ab'c'.f c < F.ab'c'.f a')
    (hgood : ¬ max ⟪a', a' - c⟫ ⟪a, a' - c⟫ ≤ min ⟪b, a' - c⟫ ⟪b', a' - c⟫)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have e := (type29_set a a' b b' c c' d).2.2.2.2
  rw [← e] at hgen hnd ⊢
  exact isRupert_type29_05 F.perm₂₃.perm₁₂.perm₂₃ hd.sigma hq₁ hq₂ hgood hgen hnd

/-! ### Theorem P, clause C1 -/

/-- Four of the edges of `G` (the others are their `σ`-images): `1 → 4`, `4 → 1`,
`0 → 3`, `0 → 5` is a quad edge of `O` (its two facet inequalities) whose tail is an
inner vertex of the third pair (`[p x] [x x'] < 0`, Lemma 1). -/
def Type29C1Half {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') : Prop :=
  (F.ab'c.f b < F.ab'c.f a' ∧ F.ab'c'.f b < F.ab'c'.f a' ∧
    galeD G.l G.m c b * galeD G.l G.m b b' < 0) ∨
  (F.ab'c.f a' < F.ab'c.f b ∧ F.ab'c'.f a' < F.ab'c'.f b ∧
    galeD G.l G.m c a' * galeD G.l G.m a' a < 0) ∨
  (F.a'bc.f a < F.a'bc.f b' ∧ F.a'bc'.f a < F.a'bc'.f b' ∧
    galeD G.l G.m c a * galeD G.l G.m a a' < 0) ∨
  (F.a'bc.f a < F.a'bc.f c' ∧ F.a'b'c.f a < F.a'b'c.f c' ∧
    galeD G.l G.m b a * galeD G.l G.m a a' < 0)

/-- **Clause C1 of Theorem P**: `O` has a quad edge with inner tail in
`G = {1→4, 4→1, 0→3, 0→5}` (`Type29C1Half F G`) or in its `σ`-image
`{1→5, 5→1, 2→3, 2→4}` (`Type29C1Half` of the relabelled octahedron
`F.perm₂₃.perm₁₂.perm₂₃` with opposite pairs `(2, 5)`, `(1, 3)`, `(0, 4)`; spelled out,
the facet inequalities at `023, 234`; `023, 234`; `015, 145`; `015, 035` and the inner
signs `[0 1] [1 3]`, `[0 5] [5 2]`, `[0 2] [2 5]`, `[1 2] [2 5]` are negative). -/
def Type29C1 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') : Prop :=
  Type29C1Half F G ∨ Type29C1Half F.perm₂₃.perm₁₂.perm₂₃ G.perm₂₃.perm₁₂.perm₂₃

theorem isRupert_type29_C1_half {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (G : GaleData a a' b b' c c')
    (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hpar : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v))
    (hC : Type29C1Half F G) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases hC with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact isRupert_type29_14 F hd h1 h2
      (not_bad_of_inner F.swap₁.perm₁₂ G.swap₁.perm₁₂ h1 h2 hκc h3) hgen hnd
  · exact isRupert_type29_41 F hd h1 h2
      (not_bad_of_inner F.swap₁ G.swap₁ h1 h2 hκc h3) hgen hpar hnd
  · exact isRupert_type29_03 F hd h1 h2
      (not_bad_of_inner F.swap₂ G.swap₂ h1 h2 hκc h3) hgen hnd
  · exact isRupert_type29_05 F hd h1 h2
      (not_bad_of_inner F.perm₂₃.swap₂ G.perm₂₃.swap₂ h1 h2 hκb h3) hgen hnd

/-- **Theorem P of §12, clause C1** (Lemmas 1, 3, 4, 2): if `O` has a quad edge with an
inner tail in `G = {1→4, 4→1, 1→5, 5→1, 0→3, 0→5, 2→3, 2→4}`, the type-29 point set is
Rupert, provided `O` has no planar equator (`κ ≠ 0`), general position (`GenPos`,
`NoPlaneParallel`) and no horizontal double normal at the views along the segments
(`NoHDNAt`). -/
theorem isRupert_type29_C1 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (G : GaleData a a' b b' c c')
    (hκa : galeD G.l G.m a a' ≠ 0) (hκb : galeD G.l G.m b b' ≠ 0)
    (hκc : galeD G.l G.m c c' ≠ 0)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hpar : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v))
    (hC : Type29C1 F G) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases hC with hC | hC
  · exact isRupert_type29_C1_half F hd G hκb hκc hgen hpar hnd hC
  · have e := (type29_set a a' b b' c c' d).2.2.2.2
    rw [← e] at hgen hpar hnd ⊢
    exact isRupert_type29_C1_half _ hd.sigma _ hκb hκa hgen hpar hnd hC

/-! ### Theorem P, clauses C2 and C3 -/

/-- **Clause C2 of Theorem P** for the octahedron `K − 5` (`F5`, opposite pairs
`(0, 4)`, `(1, 3)`, `(2, 6)`, Gale data `G5`): with `s, t` the coordinates of
Lemma 0 (b), `K − 5` has an inner-tailed quad edge along `14` (`1 → 4` or `4 → 1`) with
`t > 1`, or along `46` (`4 → 6` or `6 → 4`) with `s < 1`; in these cases `5` is a middle
of the quadrilateral at the view.  (The `σ`-image, `K − 4` along `15` or `56`, is this
clause for the relabelled `F.perm₂₃.perm₁₂.perm₂₃`.) -/
def Type29C2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (F5 : OctFacets a a' b b' c d) (G5 : GaleData a a' b b' c d) : Prop :=
  (1 < F.a'bc.f d / F.a'bc.f c' ∧
    ((F5.ab'c.f b < F5.ab'c.f a' ∧ F5.ab'c'.f b < F5.ab'c'.f a' ∧
      galeD G5.l G5.m c b * galeD G5.l G5.m b b' < 0) ∨
     (F5.ab'c.f a' < F5.ab'c.f b ∧ F5.ab'c'.f a' < F5.ab'c'.f b ∧
      galeD G5.l G5.m c a' * galeD G5.l G5.m a' a < 0))) ∨
  (F.abc'.f d / F.abc'.f a' < 1 ∧
    ((F5.abc.f a' < F5.abc.f d ∧ F5.ab'c.f a' < F5.ab'c.f d ∧
      galeD G5.l G5.m b a' * galeD G5.l G5.m a' a < 0) ∨
     (F5.abc.f d < F5.abc.f a' ∧ F5.ab'c.f d < F5.ab'c.f a' ∧
      galeD G5.l G5.m b d * galeD G5.l G5.m d c < 0)))

set_option maxHeartbeats 2000000 in
/-- **Theorem P of §12, clause C2** (Lemma 1 for `K − 5`, Lemma 2 with `5` the middle,
Lemma 9.3). -/
theorem isRupert_type29_C2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (F5 : OctFacets a a' b b' c d) (G5 : GaleData a a' b b' c d)
    (hκb : galeD G5.l G5.m b b' ≠ 0) (hκc : galeD G5.l G5.m c d ≠ 0)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v))
    (hC : Type29C2 F F5 G5) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨hs, ht, hst, hco⟩ := hd.coords
  set s := F.abc'.f d / F.abc'.f a'
  set t := F.a'bc.f d / F.a'bc.f c'
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hc' : c' = b + t⁻¹ • (d - b) - (s * t⁻¹) • (a' - b) := by
    have h1 : t • (c' - b) = d - b - s • (a' - b) := by rw [hco]; module
    calc c' = b + t⁻¹ • (t • (c' - b)) := by
          rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]; abel
      _ = _ := by rw [h1]; module
  set K : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hK
  have hset : ∀ x x' y y' p p' : ℝ³,
      ({x, x', y, y', p, p'} : Finset ℝ³) = {a, a', b, b', c, d} →
      insert c' ({x, x', y, y', p, p'} : Finset ℝ³) = K := by
    intro x x' y y' p p' h; rw [h, hK]
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have mem : ∀ z, (z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' ∨ z = d) → z ∈ K := by
    intro z hz; rw [hK]; rcases hz with h | h | h | h | h | h | h <;> simp [h]
  have hpos : 0 < 1 + (s - 1) * t⁻¹ := by
    nlinarith [mul_lt_mul_of_pos_right (show 1 - s < t by linarith) hti]
  rcases hC with ⟨ht1, h | h⟩ | ⟨hs1, h | h⟩
  · obtain ⟨h1, h2, h3⟩ := h
    have hmid : QuadMiddle b a' c d c' :=
      ⟨t⁻¹, t⁻¹ - 1 - s * t⁻¹, hti, inv_lt_one_of_one_lt₀ ht1,
        by nlinarith [mul_pos hs hti, inv_lt_one_of_one_lt₀ ht1],
        by nlinarith [mul_pos hs hti], Or.inr (by rw [hc']; module)⟩
    have e := hset b b' a' a c d (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have hp := noHDN_pair hnd (x := b) (y := a') (mem b (by simp)) (mem a' (by simp)) (Ne.symm ha'b)
    rw [← e] at hp ⊢
    exact isRupert_inner_quad_edge_lift F5.swap₁.perm₁₂ G5.swap₁.perm₁₂ h1 h2 hκc h3
      (Or.inl hmid) ⟨Ne.symm hbc', Ne.symm hb'c', Ne.symm ha'c', Ne.symm hac', Ne.symm hcc', Ne.symm hdc'⟩
      (genPos_hinj hgen (mem b (by simp)) (mem a' (by simp)) (mem a (by simp)) (mem c (by simp))
        (mem d (by simp)) (Ne.symm ha'b) ⟨hab, haa', Ne.symm hbc, Ne.symm ha'c, hdb, hda'⟩) hp
  · obtain ⟨h1, h2, h3⟩ := h
    have hmid : QuadMiddle a' b c d c' :=
      ⟨t⁻¹, s * t⁻¹, hti, inv_lt_one_of_one_lt₀ ht1, (mul_pos hs hti).ne',
        by nlinarith [mul_pos hs hti, inv_lt_one_of_one_lt₀ ht1], Or.inr (by rw [hc']; module)⟩
    have e := hset a' a b b' c d (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have hp := noHDN_pair hnd (x := a') (y := b) (mem a' (by simp)) (mem b (by simp)) ha'b
    rw [← e] at hp ⊢
    exact isRupert_inner_quad_edge_lift F5.swap₁ G5.swap₁ h1 h2 hκc h3
      (Or.inl hmid) ⟨Ne.symm ha'c', Ne.symm hac', Ne.symm hbc', Ne.symm hb'c', Ne.symm hcc', Ne.symm hdc'⟩
      (genPos_hinj hgen (mem a' (by simp)) (mem b (by simp)) (mem b' (by simp)) (mem c (by simp))
        (mem d (by simp)) ha'b ⟨Ne.symm ha'b', Ne.symm hbb', Ne.symm ha'c, Ne.symm hbc, hda', hdb⟩) hp
  · obtain ⟨h1, h2, h3⟩ := h
    have hmid : QuadMiddle a' d b b' c' :=
      ⟨1 + (s - 1) * t⁻¹, s * t⁻¹, hpos, by nlinarith [mul_pos (show 0 < 1 - s by linarith) hti],
        (mul_pos hs hti).ne',
        by rw [show s * t⁻¹ + 1 - (1 + (s - 1) * t⁻¹) = t⁻¹ by ring]; exact hti.ne',
        Or.inl (by rw [hc']; module)⟩
    have e := hset a' a d c b b' (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have hp := noHDN_pair hnd (x := a') (y := d) (mem a' (by simp)) (mem d (by simp)) (Ne.symm hda')
    rw [← e] at hp ⊢
    exact isRupert_inner_quad_edge_lift F5.perm₂₃.swap₁.swap₂ G5.perm₂₃.swap₁.swap₂ h1 h2 hκb h3
      (Or.inl hmid) ⟨Ne.symm ha'c', Ne.symm hac', Ne.symm hdc', Ne.symm hcc', Ne.symm hbc', Ne.symm hb'c'⟩
      (genPos_hinj hgen (mem a' (by simp)) (mem d (by simp)) (mem c (by simp)) (mem b (by simp))
        (mem b' (by simp)) (Ne.symm hda') ⟨Ne.symm ha'c, Ne.symm hdc, Ne.symm ha'b, Ne.symm hdb,
          Ne.symm ha'b', Ne.symm hdb'⟩) hp
  · obtain ⟨h1, h2, h3⟩ := h
    have hmid : QuadMiddle d a' b b' c' :=
      ⟨1 + (s - 1) * t⁻¹, -t⁻¹, hpos, by nlinarith [mul_pos (show 0 < 1 - s by linarith) hti],
        by linarith,
        by rw [show -t⁻¹ + 1 - (1 + (s - 1) * t⁻¹) = -(s * t⁻¹) by ring]
           exact neg_ne_zero.mpr (mul_pos hs hti).ne',
        Or.inl (by rw [hc']; module)⟩
    have e := hset d c a' a b b' (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have hp := noHDN_pair hnd (x := d) (y := a') (mem d (by simp)) (mem a' (by simp)) hda'
    rw [← e] at hp ⊢
    exact isRupert_inner_quad_edge_lift F5.perm₂₃.swap₁.swap₂.perm₁₂
      G5.perm₂₃.swap₁.swap₂.perm₁₂ h1 h2 hκb h3
      (Or.inl hmid) ⟨Ne.symm hdc', Ne.symm hcc', Ne.symm ha'c', Ne.symm hac', Ne.symm hbc', Ne.symm hb'c'⟩
      (genPos_hinj hgen (mem d (by simp)) (mem a' (by simp)) (mem a (by simp)) (mem b (by simp))
        (mem b' (by simp)) hda' ⟨Ne.symm hda, haa', Ne.symm hdb, Ne.symm ha'b, Ne.symm hdb',
          Ne.symm ha'b'⟩) hp

/-- **Clause C3 of Theorem P** (for any octahedron `K − m`, so for `O = K − 6`,
`K − 5`, `K − 4`): `K = O' ∪ {m}` with `O'` an octahedron (`F'`, Gale data `G'`, no
planar equator at the third pair) that has an inner-tailed quad edge `x → y` at whose
view `m` is hidden. -/
def Type29C3 (K : Finset ℝ³) : Prop :=
  ∃ (x x' y y' p p' m : ℝ³) (F' : OctFacets x x' y y' p p') (G' : GaleData x x' y y' p p'),
    insert m ({x, x', y, y', p, p'} : Finset ℝ³) = K ∧
    (m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p') ∧
    F'.a'b'c.f x < F'.a'b'c.f y ∧ F'.a'b'c'.f x < F'.a'b'c'.f y ∧
    galeD G'.l G'.m p p' ≠ 0 ∧ galeD G'.l G'.m p x * galeD G'.l G'.m x x' < 0 ∧
    QuadHidden x y y' p p' m

/-- **Theorem P of §12, clause C3** (Lemmas 1, 2 and 9.3). -/
theorem isRupert_type29_C3 {K : Finset ℝ³} (hgen : GenPos K)
    (hnd : ∀ v ∈ K, ∀ w ∈ K, v ≠ w → NoHDNAt (K.erase w) (w - v)) (hC : Type29C3 K) :
    IsRupert K := by
  obtain ⟨x, x', y, y', p, p', m, F', G', hK, hmO, hq₁, hq₂, hκ, hin, hhid⟩ := hC
  subst hK
  have hnd' := F'.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  exact isRupert_inner_quad_edge_lift F' G' hq₁ hq₂ hκ hin (Or.inr hhid) hmO
    (genPos_hinj hgen (by simp) (by simp) (by simp) (by simp) (by simp) hxy
      ⟨Ne.symm hxy', Ne.symm hyy', Ne.symm hxp, Ne.symm hyp, Ne.symm hxp', Ne.symm hyp'⟩)
    (noHDN_pair hnd (by simp) (by simp) hxy)

/-- **Theorem P of §12** (partial).  Let `K = O ∪ {6}` be of type 29 (`IsCap29`), with
no planar equator of `O` (`κ ≠ 0`), in general position (`GenPos`, `NoPlaneParallel`)
and without a horizontal double normal at the views along its segments (`NoHDNAt`).
If one of the clauses holds — C1 (`Type29C1`: an inner-tailed quad edge of `O` in
`G`), C2 (`Type29C2` for `K − 5`, or for `K − 4` via `σ`; with `κ ≠ 0` for the pairs
used), or C3 (`Type29C3`: an inner-tailed quad edge of an octahedron `K − m` with `m`
hidden) — the edge crossing it names has a unimodal reduced polygon with strict depths
and `K` is Rupert (Theorem 8.9 with Theorem 7.3).  That some clause always holds is not
proved. -/
theorem isRupert_type29_P {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap29 F d) (G : GaleData a a' b b' c c')
    (hκa : galeD G.l G.m a a' ≠ 0) (hκb : galeD G.l G.m b b' ≠ 0)
    (hκc : galeD G.l G.m c c' ≠ 0)
    (hgen : GenPos (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hpar : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : ∀ v ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      ∀ w ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³), v ≠ w →
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase w) (w - v))
    (hC : Type29C1 F G ∨
      (∃ (F5 : OctFacets a a' b b' c d) (G5 : GaleData a a' b b' c d),
        galeD G5.l G5.m b b' ≠ 0 ∧ galeD G5.l G5.m c d ≠ 0 ∧ Type29C2 F F5 G5) ∨
      (∃ (F4 : OctFacets c c' b b' a d) (G4 : GaleData c c' b b' a d),
        galeD G4.l G4.m b b' ≠ 0 ∧ galeD G4.l G4.m a d ≠ 0 ∧
        Type29C2 F.perm₂₃.perm₁₂.perm₂₃ F4 G4) ∨
      Type29C3 (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases hC with h | ⟨F5, G5, h1, h2, h⟩ | ⟨F4, G4, h1, h2, h⟩ | h
  · exact isRupert_type29_C1 F hd G hκa hκb hκc hgen hpar hnd h
  · exact isRupert_type29_C2 F hd F5 G5 h1 h2 hgen hnd h
  · have e := (type29_set a a' b b' c c' d).2.2.2.2
    rw [← e] at hgen hnd ⊢
    exact isRupert_type29_C2 _ hd.sigma F4 G4 h1 h2 hgen hnd h
  · exact isRupert_type29_C3 hgen hnd h

end Minimality

end
