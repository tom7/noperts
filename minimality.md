# Minimality: every nopert has at least 7 vertices

Every convex polyhedron with at most 6 vertices is Rupert. Together with the
[Septopert](septopert.md), which has 7 vertices and is not Rupert, this
makes 7 the smallest possible number of vertices of a nopert.

This is a **Lean proof**: every step is checked by Lean's kernel, it uses no
certificate data, and it depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Lean entry point: [`proof/Minimality.lean`](proof/Minimality.lean).

## The statement

```lean
/-- A nopert: points that are not all in one plane (so their convex hull is a
genuine solid), whose convex hull is not Rupert. -/
def IsNopert (V : Finset ℝ³) : Prop := ¬ Coplanar ℝ (V : Set ℝ³) ∧ ¬ IsRupert V

/-- Every nopert has at least 7 points. -/
theorem seven_le_card_of_isNopert (V : Finset ℝ³) (h : IsNopert V) : 7 ≤ V.card
```

`IsRupert` (in `proof/MainTheorem.lean`) is the same definition used for the
Septopert. `V` is a finite set of points; the solid is its convex hull. The
theorem counts points, so it also bounds the number of vertices: the vertices
of the hull form a set with the same hull, which is therefore a nopert too.

The same file also states sharper facts about point sets, including flat ones
(the Rupert property only looks at shadows, so a flat polygon can pass
through a copy of itself):

- every set of 6 or fewer points whose hull is a solid is Rupert
  (`isRupert_of_card_le_six`);
- every set of points that lies in a plane but not on a line is Rupert, for
  any number of points (`isRupert_of_coplanar_of_not_collinear`);
- a nonempty set of points on a line is never Rupert
  (`not_isRupert_of_collinear`);
- so for 6 or fewer points: Rupert ⟺ empty, or not all on one line
  (`isRupert_iff_of_card_le_six`).

## How it is proved

The proof finds an explicit passage for every possible solid. Each passage is
"near the identity": the inner copy is rotated by a tiny amount relative to
the outer one, viewed from a carefully chosen direction.

1. **First order suffices.** If, at some view, a small rotation and
   translation of the inner copy moves every corner of its shadow strictly
   into the outer shadow, then for a small enough rotation the inner shadow
   lies strictly inside: a passage.
2. **Planar silhouettes.** If, at some oblique view, the corners of the
   shadow all come from vertices lying in one plane, such a motion exists,
   unless the view's level direction happens to be a "double normal" of the
   shadow, which only happens on finitely many great circles of views.
3. **Unimodal silhouettes.** More generally, it suffices that the depth of
   the shadow's corners, walking around the outline, rises once and falls
   once. The proof goes through the balancing forces at the corners.
4. **Tilting off degenerate views.** Views where an edge or face is seen
   exactly edge-on can be tilted slightly to produce a unimodal view with a
   chosen outline.
5. **The cases.** Up to 5 vertices: a pyramid, or (by Radon's theorem) a
   segment piercing a triangle, i.e. a bipyramid. With 6 vertices, the
   points' affine dependencies (a "Gale diagram") either show the solid is a
   prism, or give a segment piercing a quadrilateral; in the latter case the
   signs of a few determinants determine the solid's faces, and each of the
   seven combinatorial types of 6-vertex polyhedra (octahedra, bicapped
   tetrahedra, triangular prisms, pentagonal pyramids, and three others) has
   its own argument built from 1–4. Octahedra are the hardest case.

No classification of polyhedra by face structure is assumed; everything is
derived from the coordinates.

The informal notes this proof follows, with referee reports, are maintained
separately (`LEMMAS.md` and `L7_REVIEW.md`–`L9_REVIEW.md` in the authors'
notes) and may be added to this repository.
