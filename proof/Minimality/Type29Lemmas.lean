module

public import Minimality.Type08

@[expose] public section

/-!
# Type 29: the reusable lemmas of Theorem P of §12 (`FEWER-FACES-PROOFS.md` §12)

Two lemmas about an octahedron `O` with opposite pairs `(x, x')`, `(y, y')`,
`(p, p')` and one more point `m` (in type 29, `O = K − m` for `m = 6`, `5` or `4`).
A *quad edge* `x → y` of `O` is one whose view `u = y − x` hides `x'` (the two facet
inequalities `hq₁`, `hq₂` of `isRupert_quad_edge`); it is *bad* if
`max (z y, z y') ≤ min (z p, z p')` for `z = ⟪·, y − x⟫`.

* **Lemma 1 of §12** (certification without a crossed pair) — `not_bad_of_inner`:
  if the tail `x` is an *inner* vertex of the third pair `W = {p, p'}`, i.e.
  `[p x] [x x'] < 0` in the Gale diagram (`galeD`), the quad edge is not bad.  The
  dependency `±[x' ·]` is negative on `x, y, y'` (`inner_dep_signs`, from the pole
  signs (G3)), Lemma 9.7 (`inTri_of_dep`) puts the axis point `p` inside the
  triangle `y' x y` in the view along `p p'`, and Lemma 3 of §10
  (`not_bad_of_inTri`) concludes; its separation hypothesis holds at every quad
  edge (`quad_edge_sep`).
* **Lemma 2 of §12** (exact lift) — `isRupert_quad_edge_lift`: if the extra point
  `m` is a *middle* at the view along `x y` (over the chord from `y` to a far end
  `p` or `p'`; `QuadMiddle`) or *hidden* (its image strictly inside the shadow of
  `O`; `QuadHidden`), then `K = O ∪ {m}` has the reduced polygons of `O` at that
  view, and a quad edge of `O` that is not bad gives a unimodal closing of `K`'s
  test (Lemma 9.3), so Theorem 8.9 with Theorem 7.3
  (`isRupert_of_edgeChords_unimodal`, via `isRupert_of_edgeView`) gives a passage.
  `quadHidden_of_beneath`: `m` is hidden if it lies beneath the six faces of `O`
  other than `x' y p`, `x' y p'` (on at most one face of each far edge).
* Both together — `isRupert_inner_quad_edge_lift` (the clause C3 of Theorem P, and
  with a middle the clauses C1, C2).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The separation at a quad edge -/

/-- At a quad edge `x → y` of an octahedron, the plane `x y y'` separates `p` from
`p'` (its image in the view along `x y` is the diagonal `q Y'` of the shadow). -/
theorem quad_edge_sep {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y) :
    det3 (y - x) (y' - x) (p - x) * det3 (y - x) (y' - x) (p' - x) < 0 := by
  have key : ∀ {p p' : ℝ³} (F : OctFacets x x' y y' p p'), F.a'b'c.f x < F.a'b'c.f y →
      F.a'b'c'.f x < F.a'b'c'.f y → 0 < det3 (p - y) (p' - y) (y - x) →
      det3 (y - x) (y' - x) (p - x) < 0 ∧ 0 < det3 (y - x) (y' - x) (p' - x) := by
    intro p p' F hq₁ hq₂ hor
    obtain ⟨E1, -, -, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
      ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
    have e1 := E1 y' (by simp) (Ne.symm hyy') hy'p (Ne.symm hxy')
    have e4 := E4 y' (by simp) hy'p' (Ne.symm hyy') (Ne.symm hxy')
    have i1 : det3 (y - x) (y' - x) (p - x) = -det3 (p - y) (y' - y) (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have i4 : det3 (y - x) (y' - x) (p' - x) = det3 (y - p') (y' - p') (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    exact ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · obtain ⟨h1, h2⟩ := key F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
    nlinarith
  · obtain ⟨h1, h2⟩ := key F hq₁ hq₂ hpos
    nlinarith

/-! ### Lemma 1: certification without a crossed pair -/

/-- **The sign chain of Lemma 1.**  If `x` is an inner vertex of `W = {p, p'}`
(`[p x] [x x'] < 0`), the dependency `[x' ·]` has one sign on `x`, `y`, `y'`. -/
theorem inner_dep_signs {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (G : GaleData x x' y y' p p') (hκW : galeD G.l G.m p p' ≠ 0)
    (hinner : galeD G.l G.m p x * galeD G.l G.m x x' < 0) :
    0 < galeD G.l G.m x' x * galeD G.l G.m x' y ∧
      0 < galeD G.l G.m x' x * galeD G.l G.m x' y' := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have hxx' : galeD G.l G.m x x' ≠ 0 := right_ne_zero_of_mul hinner.ne
  obtain ⟨d1, -, d3⟩ := pole_signs F.swap₁ (hl.galeD hm x').swap₁ (galeD_self _ _ x')
    (by rw [anti]; exact neg_ne_zero.mpr hxx')
  obtain ⟨e1, -, -⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm p).perm₂₃.perm₁₂
    (galeD_self _ _ p) hκW
  -- `[x' y] [p x'] > 0`, `[p x] [p x'] > 0`, `[p x] [x x'] < 0`
  have hpx' : galeD G.l G.m x' p = -galeD G.l G.m p x' := anti p x'
  have hxx'a : galeD G.l G.m x' x = -galeD G.l G.m x x' := anti x x'
  rw [hpx'] at d3
  rw [hxx'a]
  have f1 : 0 < galeD G.l G.m x' y * galeD G.l G.m p x' := by nlinarith
  have hpx : galeD G.l G.m p x ≠ 0 := left_ne_zero_of_mul hinner.ne
  have s1 : 0 < -galeD G.l G.m x x' * galeD G.l G.m x' y := by
    rcases lt_or_gt_of_ne hpx with h | h
    · have h1 : galeD G.l G.m p x' < 0 := neg_of_mul_pos_neg e1 h
      have h2 : galeD G.l G.m x' y < 0 := by nlinarith
      have h3 : 0 < galeD G.l G.m x x' := by nlinarith
      nlinarith
    · have h1 : 0 < galeD G.l G.m p x' := pos_of_mul_pos_pos e1 h
      have h2 : 0 < galeD G.l G.m x' y := by nlinarith
      have h3 : galeD G.l G.m x x' < 0 := by nlinarith
      nlinarith
  refine ⟨s1, ?_⟩
  have hy : galeD G.l G.m x' y ≠ 0 := by intro h0; rw [h0, mul_zero] at s1; exact lt_irrefl _ s1
  rcases lt_or_gt_of_ne hy with h | h
  · have : galeD G.l G.m x' y' < 0 := neg_of_mul_pos_neg d1 h
    nlinarith
  · have : 0 < galeD G.l G.m x' y' := pos_of_mul_pos_pos d1 h
    nlinarith

/-- The facet `x y p` is not degenerate: `p'` is off its plane. -/
theorem det3_xyp_ne {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p') :
    det3 (x - p) (y - p) (p' - p) ≠ 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  intro h0
  have hc := cross_ne_zero_of_affine F.abc'.hN hxy F.abc'.hP F.abc'.hQ
    (F.abc'.neg p (by simp) (Ne.symm hxp) (Ne.symm hyp) hpp')
  have hw : det3 (y - x) (p - x) (p' - x) = 0 := by
    rw [← h0]; simp only [det3_expand, PiLp.sub_apply]; ring
  have := affine_zero_of_coplanar F.abc.hN F.abc.hP F.abc.hQ F.abc.hR hc hw
  have := F.abc.neg p' (by simp) (Ne.symm hxp') (Ne.symm hyp') (Ne.symm hpp')
  linarith

/-- **Lemma 1 of §12 (certification without a crossed pair).**  Let `x → y` be a
quad edge of an octahedron (`x'` hidden along `y − x`) with third pair
`W = {p, p'}` (`κ_W = [p p'] ≠ 0`).  If the tail `x` is an inner vertex of `W`
(`[p x] [x x'] < 0`: the primed vertex of `U_W` or the unprimed vertex of `V_W`),
the edge is not bad: `max (z y, z y') > min (z p, z p')` for `z = ⟪·, y − x⟫`.
Lemma 9.7 (`inTri_of_dep`, with the dependency `±[x' ·]`) puts `p` inside the
triangle `y' x y` in the view along `p p'`, and Lemma 3 of §10
(`not_bad_of_inTri`) applies. -/
theorem not_bad_of_inner {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (G : GaleData x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hκW : galeD G.l G.m p p' ≠ 0)
    (hinner : galeD G.l G.m p x * galeD G.l G.m x x' < 0) :
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  obtain ⟨s1, s2⟩ := inner_dep_signs F G hκW hinner
  -- a dependency vanishing at `x'`, negative at `x`, `y`, `y'`
  obtain ⟨L, hL, h0, hx, hy, hy'⟩ : ∃ L : ℝ³ → ℝ, IsDep x x' y y' p p' L ∧ L x' = 0 ∧
      L x < 0 ∧ L y < 0 ∧ L y' < 0 := by
    rcases lt_or_gt_of_ne (show galeD G.l G.m x' x ≠ 0 by
      intro h; rw [h, zero_mul] at s1; exact lt_irrefl _ s1) with h | h
    · exact ⟨_, G.hl.galeD G.hm x', galeD_self _ _ x', h, neg_of_mul_pos_neg s1 h,
        neg_of_mul_pos_neg s2 h⟩
    · refine ⟨_, G.mirror.hl.galeD G.mirror.hm x', galeD_self _ _ x', ?_, ?_, ?_⟩ <;>
        rw [G.galeD_mirror]
      · linarith
      · linarith [pos_of_mul_pos_pos s1 h]
      · linarith [pos_of_mul_pos_pos s2 h]
  have hsep := quad_edge_sep F hq₁ hq₂
  have hD := det3_xyp_ne F
  have hT : (0 < det3 (x - p) (y - p) (p' - p) ∧ 0 < det3 (y - p) (y' - p) (p' - p) ∧
        0 < det3 (y' - p) (x - p) (p' - p)) ∨
      (det3 (x - p) (y - p) (p' - p) < 0 ∧ det3 (y - p) (y' - p) (p' - p) < 0 ∧
        det3 (y' - p) (x - p) (p' - p) < 0) := by
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · have he : p - p' = -(p' - p) := by abel
      obtain ⟨t1, t2⟩ := inTri_of_dep hL h0 hx hy hy' (e := p - p') (Or.inr rfl)
        (by rw [he, det3_neg_right]; linarith)
      rw [he, det3_neg_right] at t1 t2
      exact Or.inr ⟨hneg, by linarith, by linarith⟩
    · obtain ⟨t1, t2⟩ := inTri_of_dep hL h0 hx hy hy' (e := p' - p) (Or.inl rfl) hpos
      exact Or.inl ⟨hpos, t1, t2⟩
  refine not_bad_of_inTri (g := fun X => det3 (y - x) (y' - x) (X - x))
    (N := cross (y - x) (y' - x)) (fun s t => by simp only [det3, ← inner_sub_right]; abel_nf)
    (by simp only [sub_self]; simp [det3_expand]) (by simp only [det3_expand]; ring)
    (by simp only [det3_expand]; ring) hsep hxy hT

/-! ### Lemma 2: the exact lift -/

/-- The extra point `m` is a *middle* at the view along `x y`: it lies over the
chord from `y` to the far end `p` or `p'`, strictly between (`0 < s < 1`), off the
two vertical planes through that chord's ends along the view (`δ ≠ 0` measured from
`y`, `δ + 1 − s ≠ 0` measured from `x`). -/
def QuadMiddle (x y p p' m : ℝ³) : Prop :=
  ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ δ + 1 - s ≠ 0 ∧
    (m = y + s • (p - y) + δ • (y - x) ∨ m = y + s • (p' - y) + δ • (y - x))

/-- The extra point `m` is *hidden* at the view along `x y`: its image lies strictly
inside the quadrilateral of the images of `y, p, y', p'` (each edge test has the sign
of the orientation `det3 (p − y) (p' − y) (y − x)`). -/
def QuadHidden (x y y' p p' m : ℝ³) : Prop :=
  0 < det3 (p - y) (m - y) (y - x) * det3 (p - y) (p' - y) (y - x) ∧
  0 < det3 (y' - p) (m - p) (y - x) * det3 (p - y) (p' - y) (y - x) ∧
  0 < det3 (p' - y') (m - y') (y - x) * det3 (p - y) (p' - y) (y - x) ∧
  0 < det3 (y - p') (m - p') (y - x) * det3 (p - y) (p' - y) (y - x)

theorem QuadMiddle.swap {x y p p' m : ℝ³} (h : QuadMiddle x y p p' m) : QuadMiddle x y p' p m := by
  obtain ⟨s, δ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨s, δ, h1, h2, h3, h4, h5.symm⟩

theorem QuadHidden.swap {x y y' p p' m : ℝ³} (h : QuadHidden x y y' p p' m) :
    QuadHidden x y y' p' p m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have o : det3 (p' - y) (p - y) (y - x) = -det3 (p - y) (p' - y) (y - x) := by
    rw [det3_swap12]
  have e1 : det3 (p' - y) (m - y) (y - x) = -det3 (y - p') (m - p') (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e2 : det3 (y' - p') (m - p') (y - x) = -det3 (p' - y') (m - y') (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e3 : det3 (p - y') (m - y') (y - x) = -det3 (y' - p) (m - p) (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e4 : det3 (y - p) (m - p) (y - x) = -det3 (p - y) (m - y) (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o, e1, neg_mul_neg]; exact h4
  · rw [o, e2, neg_mul_neg]; exact h3
  · rw [o, e3, neg_mul_neg]; exact h2
  · rw [o, e4, neg_mul_neg]; exact h1

/-- **Lemma 2 of §12, oriented core.**  Lemma 9.3 at a quad edge `x → y` of an
octahedron (counterclockwise shadow `y, p, y', p'`), with one more point `m` that is a
middle (`m ∈ M`) or hidden (`m ∉ M`): the reduced polygons are those of the
octahedron, and the closing of Lemma 9.3 gives a unimodal `K_v`. -/
theorem isRupert_quad_edge_lift_core {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (M : Finset ℝ³) (hMm : M ⊆ {m}) (hmid : m ∈ M → QuadMiddle x y p p' m)
    (hhid : m ∉ M → QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hmx, hmx', hmy, hmy', hmp, hmp'⟩ := hmO
  set V : Finset ℝ³ := insert m {x, x', y, y', p, p'} with hV
  have mx : x ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have hmemV : ∀ z ∈ V, z = m ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hnotM : ∀ z, z ≠ m → z ∉ M := fun z hz hzM => hz (mem_singleton.mp (hMm hzM))
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the middle, for either choice of `v`
  have hEM : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = y ∧ w = x ∧ hh = 1) ∨ (v = x ∧ w = y ∧ hh = -1)) →
      ∀ m' ∈ M, EdgeMiddle (y - x) v w p p' hh m' := by
    intro v w hh hvw m' hm'
    have hm'm : m' = m := mem_singleton.mp (hMm hm')
    subst hm'm
    obtain ⟨s, δ, hs0, hs1, hδ, hδ', hm⟩ := hmid hm'
    rcases hvw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases hm with hm | hm
      · exact ⟨v, s, δ, Or.inl rfl, hs0, hs1, hδ, Or.inl hm⟩
      · refine ⟨v, 1 - s, δ, Or.inl rfl, by linarith, by linarith, hδ, Or.inr ?_⟩
        rw [hm]; module
    · rcases hm with hm | hm
      · refine ⟨v, s, δ + 1 - s, Or.inl rfl, hs0, hs1, hδ', Or.inl ?_⟩
        rw [hm]; module
      · refine ⟨v, 1 - s, δ + 1 - s, Or.inl rfl, by linarith, by linarith, hδ', Or.inr ?_⟩
        rw [hm]; module
  -- the hidden point passes the edge tests
  have hH : m ∉ M → 0 < det3 (p - y) (m - y) (y - x) ∧ 0 < det3 (y' - p) (m - p) (y - x) ∧
      0 < det3 (p' - y') (m - y') (y - x) ∧ 0 < det3 (y - p') (m - p') (y - x) := by
    intro hmM
    obtain ⟨h1, h2, h3, h4⟩ := hhid hmM
    exact ⟨pos_of_mul_pos_pos (by rwa [mul_comm] at h1) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h2) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h3) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h4) hor⟩
  have hpy' : ⟪p, y - x⟫ ≠ ⟪y', y - x⟫ := fun h =>
    hinj p y' (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inl rfl) (Ne.symm hy'p) h
  have hpp'u : ⟪p, y - x⟫ ≠ ⟪p', y - x⟫ :=
    hinj p p' (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr (Or.inr rfl)) hpp'
  have hy'p'u : ⟪y', y - x⟫ ≠ ⟪p', y - x⟫ :=
    hinj y' p' (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl)) hy'p'
  have hinjq : ∀ z : ℝ³, (z = x ∨ z = y) → z ≠ p → z ≠ y' → z ≠ p' → Function.Injective
      (quad ⟪z, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
    intro z hz h1 h2 h3
    have hs : z = x ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
      rcases hz with h | h
      exacts [Or.inl h, Or.inr (Or.inl h)]
    exact quad_injective (hinj z p hs (Or.inr (Or.inl rfl)) h1)
      (hinj z y' hs (Or.inl rfl) h2) (hinj z p' hs (Or.inr (Or.inr rfl)) h3) hpy' hpp'u hy'p'u
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)
  · -- `K_y` is unimodal
    refine isRupert_of_edgeView V M (y - x) hu (k := 4) (by norm_num) (quad y p y' p') 0 x 1
      (by simp [V]) (by simp only [quad_0, one_smul]; abel) one_ne_zero ?_ ?_ ?_ ?_ ?_
      hnd.1 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM y (Ne.symm hmy), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 y my hyp hyy'
      · exact E3 y my hyy' hyp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        exacts [t1, t2, t3, t4]
      · exact absurd h hzw
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h h0
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq y (Or.inr rfl) hyp hyy' hyp') hN
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM y x 1 (Or.inl ⟨rfl, rfl, rfl⟩)
  · -- `K_x` is unimodal (the closing by `x` of Lemma 9.3)
    have hS₁ := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) (y - x) := by
      rw [← det3_cyc x y' p']; exact E3 x mx hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) (y - x) := by
      rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hN' := nws4_closing_x hS₁ hS₂ hS₃ hS₄ (quad_edge_lower F hS₁ hS₂ hS₃ hS₄) hN hgood
      hpp'u
    refine isRupert_of_edgeView V M (y - x) hu (k := 4) (by norm_num) (quad x p y' p') 0 y (-1)
      (by simp [V]) (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd.2 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM x (Ne.symm hmx), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 x mx hxp hxy'
      · exact E3 x mx hxy' hxp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact t1
        · exact t2
        · exact t3
        · rw [det3_shift_p']; exact t4
      · exact absurd h h0
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h hzw
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq x (Or.inl rfl) hxp hxy' hxp') hN'
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM x y (-1) (Or.inr ⟨rfl, rfl, rfl⟩)

/-- **Lemma 2 of §12 (exact lift).**  Let `x → y` be a quad edge of an octahedron
`O` (`x'` hidden along `y − x`) that is not bad, and let `m` be one more point that is
a middle (`QuadMiddle`: over the chord from `y` to a far end) or hidden
(`QuadHidden`: its image strictly inside the shadow of `O`) at the view along
`x y`.  Then the reduced polygons of `K = O ∪ {m}` at that view are those of `O`,
closing by closing, so Lemma 9.3's unimodal closing is one of `K`; with distinct
depths along `y − x` (no touching) and no horizontal double normal there, `K` is
Rupert (Theorem 8.9 with Theorem 7.3, `isRupert_of_edgeChords_unimodal`). -/
theorem isRupert_quad_edge_lift {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hm : QuadMiddle x y p p' m ∨ QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  -- the set `M` of middles
  obtain ⟨M, hMm, hmid, hhid⟩ : ∃ M : Finset ℝ³, M ⊆ {m} ∧ (m ∈ M → QuadMiddle x y p p' m) ∧
      (m ∉ M → QuadHidden x y y' p p' m) := by
    rcases hm with h | h
    · exact ⟨{m}, subset_rfl, fun _ => h, fun h' => absurd (mem_singleton_self m) h'⟩
    · exact ⟨∅, empty_subset _, fun h' => absurd h' (notMem_empty m), fun _ => h⟩
  have e : (insert m {x, x', y, y', p', p} : Finset ℝ³) = insert m {x, x', y, y', p, p'} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := isRupert_quad_edge_lift_core F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
      (by rwa [min_comm]) M hMm (fun h => (hmid h).swap) (fun h => (hhid h).swap)
      ⟨hmO.1, hmO.2.1, hmO.2.2.1, hmO.2.2.2.1, hmO.2.2.2.2.2, hmO.2.2.2.2.1⟩
      (fun s t hs ht => hinj s t (by rcases hs with h | h | h | h | h <;> simp only [h, true_or, or_true])
        (by rcases ht with h | h | h <;> simp only [h, true_or, or_true])) (by rw [e]; exact hnd)
    rwa [e] at this
  · exact isRupert_quad_edge_lift_core F hq₁ hq₂ hpos hgood M hMm hmid hhid hmO hinj hnd

/-! ### A hidden point from the facets; Lemmas 1 and 2 together -/

/-- A point beneath (or on) both facets of a far edge `Q P` of the edge view, strictly
beneath one, is strictly on the inner side of that edge (`far_edge_pos` for a point
that need not be a vertex). -/
theorem far_edge_pos_pt {V : Finset ℝ³} {x x' y P Q : ℝ³} (G : FacetFn V x Q P)
    (H : FacetFn V x' Q P) (hHx : H.f x < 0) (hGy : G.f y < 0) (hq : H.f x < H.f y)
    (href : 0 < det3 (Q - P) (y - P) (y - x)) {m : ℝ³}
    (hm : G.f m ≤ 0 ∧ H.f m ≤ 0 ∧ (G.f m < 0 ∨ H.f m < 0)) :
    0 < det3 (Q - P) (m - P) (y - x) := by
  have hα : 0 < H.f y - H.f x := by linarith
  have hβ : 0 < -(G.f y - G.f x) := by rw [G.hP]; linarith
  refine det3_pos_of_combo G.hN H.hN G.hR G.hQ H.hR H.hQ (α := H.f y - H.f x)
    (β := -(G.f y - G.f x)) ?_ href ?_ ?_
  · rw [← G.hN, ← H.hN]; ring
  · rw [G.hP]; nlinarith
  · obtain ⟨h1, h2, h3⟩ := hm
    rcases h3 with h3 | h3
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ.le h2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hα.le h1]

/-- A point strictly beneath a vertical facet `x y P` (containing the view `y − x`) is
strictly on the inner side of the shadow edge `y → P`. -/
theorem vert_edge_pos_pt {V : Finset ℝ³} {x y P : ℝ³} (G : FacetFn V x y P) {r m : ℝ³}
    (hr : G.f r < 0) (href : 0 < det3 (P - y) (r - y) (y - x)) (hm : G.f m < 0) :
    0 < det3 (P - y) (m - y) (y - x) := by
  refine det3_pos_of_combo G.hN G.hN G.hQ G.hR G.hQ G.hR (α := 1) (β := 0) ?_ href
    (by linarith) (by linarith)
  rw [← G.hN, G.hQ, G.hP]; ring

theorem vert_edge_pos_pt' {V : Finset ℝ³} {x y P : ℝ³} (G : FacetFn V x y P) {r m : ℝ³}
    (hr : G.f r < 0) (href : 0 < det3 (y - P) (r - P) (y - x)) (hm : G.f m < 0) :
    0 < det3 (y - P) (m - P) (y - x) := by
  refine det3_pos_of_combo G.hN G.hN G.hR G.hQ G.hR G.hQ (α := 1) (β := 0) ?_ href
    (by linarith) (by linarith)
  rw [← G.hN, G.hQ, G.hP]; ring

/-- The facet conditions for a hidden point, oriented. -/
theorem quadHidden_tests {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (h1 : F.abc.f m < 0) (h2 : F.abc'.f m < 0)
    (h3 : F.ab'c.f m ≤ 0 ∧ F.a'b'c.f m ≤ 0 ∧ (F.ab'c.f m < 0 ∨ F.a'b'c.f m < 0))
    (h4 : F.ab'c'.f m ≤ 0 ∧ F.a'b'c'.f m ≤ 0 ∧ (F.ab'c'.f m < 0 ∨ F.a'b'c'.f m < 0)) :
    0 < det3 (p - y) (m - y) (y - x) ∧ 0 < det3 (y' - p) (m - p) (y - x) ∧
      0 < det3 (p' - y') (m - y') (y - x) ∧ 0 < det3 (y - p') (m - p') (y - x) := by
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  refine ⟨vert_edge_pos_pt F.abc (F.abc.neg p' (by simp) (Ne.symm hxp') (Ne.symm hyp')
      (Ne.symm hpp')) hor h1, ?_, ?_, ?_⟩
  · exact far_edge_pos_pt F.ab'c F.a'b'c (F.a'b'c.neg x (by simp) hxx' hxy' hxp)
      (F.ab'c.neg y (by simp) (Ne.symm hxy) hyy' hyp) hq₁ (E2 y (by simp) hyp hyy') h3
  · exact far_edge_pos_pt F.ab'c'.p23 F.a'b'c'.p23 (F.a'b'c'.neg x (by simp) hxx' hxy' hxp')
      (F.ab'c'.neg y (by simp) (Ne.symm hxy) hyy' hyp') hq₂ (E3 y (by simp) hyy' hyp')
      ⟨h4.1, h4.2.1, h4.2.2⟩
  · exact vert_edge_pos_pt' F.abc' (F.abc'.neg p (by simp) (Ne.symm hxp) (Ne.symm hyp) hpp')
      (by rw [← det3_cyc p' y p]; exact hor) h2

/-- **A hidden point from the facets.**  At a quad edge `x → y` of an octahedron, a
point strictly beneath the vertical facets `x y p`, `x y p'` and beneath both facets
of each far edge `y' p`, `y' p'` (strictly beneath at least one of each pair) is
hidden: its image is strictly inside the shadow.  The facets `x' y p`, `x' y p'` play
no role. -/
theorem quadHidden_of_beneath {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (h1 : F.abc.f m < 0) (h2 : F.abc'.f m < 0)
    (h3 : F.ab'c.f m ≤ 0 ∧ F.a'b'c.f m ≤ 0 ∧ (F.ab'c.f m < 0 ∨ F.a'b'c.f m < 0))
    (h4 : F.ab'c'.f m ≤ 0 ∧ F.a'b'c'.f m ≤ 0 ∧ (F.ab'c'.f m < 0 ∨ F.a'b'c'.f m < 0)) :
    QuadHidden x y y' p p' m := by
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := quadHidden_tests F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith) h2 h1 h4 h3
    obtain ⟨t1, t2, t3, t4⟩ := this
    have h : QuadHidden x y y' p' p m :=
      ⟨mul_pos t1 (by rw [det3_swap12]; linarith), mul_pos t2 (by rw [det3_swap12]; linarith),
        mul_pos t3 (by rw [det3_swap12]; linarith), mul_pos t4 (by rw [det3_swap12]; linarith)⟩
    exact h.swap
  · obtain ⟨t1, t2, t3, t4⟩ := quadHidden_tests F hq₁ hq₂ hpos h1 h2 h3 h4
    exact ⟨mul_pos t1 hpos, mul_pos t2 hpos, mul_pos t3 hpos, mul_pos t4 hpos⟩

/-- **Lemmas 1 and 2 of §12 together** (the clause C3 of Theorem P; with a middle, the
step shared by C1 and C2).  An octahedron `O` with an inner-tailed quad edge `x → y`
(`[p x] [x x'] < 0`, `κ_W ≠ 0`) and one more point `m`, a middle or hidden at the view
along `x y`: with distinct depths along `y − x` and no horizontal double normal there,
`O ∪ {m}` is Rupert. -/
theorem isRupert_inner_quad_edge_lift {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (G : GaleData x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hκW : galeD G.l G.m p p' ≠ 0)
    (hinner : galeD G.l G.m p x * galeD G.l G.m x x' < 0)
    (hm : QuadMiddle x y p p' m ∨ QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) :=
  isRupert_quad_edge_lift F hq₁ hq₂ (not_bad_of_inner F G hq₁ hq₂ hκW hinner) hm hmO hinj hnd

end Minimality

end
