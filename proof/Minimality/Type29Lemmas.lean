module

public import Minimality.Type08

@[expose] public section

/-!
# Type 29: the reusable lemmas of Theorem P of §12

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

/-! ### Lemma 1: certification without a crossed pair -/

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

end Minimality

end
