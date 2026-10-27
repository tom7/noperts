module

public import Minimality.Cases
public import Minimality.SevenTypes
public import Minimality.FaceBridge
public import Minimality.Classify
public import Minimality.Type29Bridge
public import Minimality.Type29Codim2
public import Minimality.Type02CaseC
public import Minimality.Type02HDN
public import Minimality.TripleTieObtuse
public import Minimality.TripleTieAdjacent
public import Minimality.ParDichotomy
public import Minimality.QuadTripleRect
public import Minimality.Type10Prism
public import Minimality.Type10RightPrism

/-!
# Every nopert has at least 7 points

A convex polyhedron is *Rupert* if a copy of it can pass through a straight
hole cut in another copy of the same size (`IsRupert`, `MainTheorem.lean`:
some view of the polyhedron, possibly shifted, fits strictly inside the
shadow of another view).  A *nopert* is a solid convex polyhedron that is not
Rupert (`IsNopert`, `Nopert.lean`).  Polyhedra are given by finite sets
`V : Finset ℝ³` of points; the polyhedron is their convex hull.

This file states the main results; the proofs are in the `Minimality/`
modules (see `Minimality/README.md` for an overview).

* `seven_le_card_of_isNopert`: every nopert has at least 7 points.  This
  follows from `isRupert_of_card_le_six`: every solid convex polyhedron
  given by at most 6 points is Rupert.
* `facet_card_le_four_of_isNopert`: a nopert with exactly 7 points has no
  facet containing 5 or more of them, so its faces are triangles and
  quadrilaterals.  This follows from `isRupert_of_card_seven_of_facet`: seven
  points with a solid hull, at least five (but not all) of them on a facet, are
  Rupert (Theorem A of the notes; `Minimality/FaceFive.lean`).
* For flat point sets the answer is known for any number of points: points in
  a plane, not all on one line, are Rupert
  (`isRupert_of_coplanar_of_not_collinear`), while points on one line are not
  (`not_isRupert_of_collinear`).  Hence `isRupert_iff_of_card_le_six`:
  at most 6 points are Rupert exactly when they are not all on one line (or
  there are none at all).
* `anySevenVertexNopertIsSimplicial` (skeleton, contains `sorry`): every
  7-vertex nopert is simplicial (`AnySevenVertexNopertIsSimplicial`,
  `MainTheorem.lean`), split into the 29 non-simplicial types; the per-type
  theorems are in `Minimality/Cases.lean`, the types in
  `Minimality/SevenTypes.lean`.

All results except `anySevenVertexNopertIsSimplicial` depend only on the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

@[expose] public section

/-- **Every solid convex polyhedron with at most 6 vertices is Rupert.**
More precisely: at most 6 points of `ℝ³`, not all in one plane, have a Rupert
convex hull.  (The points need not all be vertices of the hull.) -/
theorem isRupert_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6)
    (hsolid : ¬ Coplanar ℝ (V : Set ℝ³)) : IsRupert V :=
  Minimality.isRupert_of_card_le_six V hV
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp hsolid)

/-- **Every nopert has at least 7 points** (hence at least 7 vertices: its
vertex set has the same convex hull, so is a nopert too). -/
theorem seven_le_card_of_isNopert (V : Finset ℝ³) (h : IsNopert V) : 7 ≤ V.card := by
  by_contra hlt
  exact h.2 (isRupert_of_card_le_six V (by omega) h.1)

/-- **Seven points with a large facet are Rupert.**  Seven points of `ℝ³`, not
all in one plane, of which at least five but not all lie on a facet of their
convex hull, are Rupert.  (`Minimality.IsFacet V F`: some affine function
vanishes on `F` and is negative at the other points of `V`.) -/
theorem isRupert_of_card_seven_of_facet (V F : Finset ℝ³) (hV : V.card = 7)
    (hsolid : ¬ Coplanar ℝ (V : Set ℝ³)) (hFV : F ⊂ V) (hF : 5 ≤ F.card)
    (hfacet : Minimality.IsFacet V F) : IsRupert V :=
  Minimality.isRupert_of_card_seven_of_facet V F hV
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp hsolid) hFV hF hfacet

/-- **A nopert with 7 points has only triangles and quadrilaterals as faces**: no
facet of its hull contains 5 or more of its points. -/
theorem facet_card_le_four_of_isNopert (V F : Finset ℝ³) (h : IsNopert V) (hV : V.card = 7)
    (hFV : F ⊂ V) (hfacet : Minimality.IsFacet V F) : F.card ≤ 4 := by
  by_contra hlt
  push Not at hlt
  exact h.2 (isRupert_of_card_seven_of_facet V F hV h.1 hFV hlt hfacet)

/-- **A nopert with 7 points in general position has at most three quadrilateral
faces** (Theorem B of the notes: four quadrilateral facets force the face
structure called type 02, which is Rupert by a slightly tilted view along the
edge where two of the quadrilaterals meet). General position
(`Minimality.GenPos`): no two segments between the points are parallel or
orthogonal. The special positions are proved on paper (FEWER-FACES-PROOFS.md
§4) except several simultaneous depth ties, and not yet formalized. -/
theorem not_four_quad_facets_of_isNopert (V : Finset ℝ³) (h : IsNopert V) (hV : V.card = 7)
    (hgen : Minimality.GenPos V) (Q : Fin 4 → Finset ℝ³) (hQV : ∀ k, Q k ⊆ V)
    (hQc : ∀ k, (Q k).card = 4) (hQf : ∀ k, Minimality.IsFacet V (Q k))
    (hQi : Function.Injective Q) : False :=
  h.2 (Minimality.isRupert_of_four_quad_facets_solid V hV
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1) hgen Q hQV hQc hQf hQi)

/-- **No two quadrilateral facets sharing one vertex** (Corollary T1 of the
triangle-shadow lemma, `FEWER-FACES-PROOFS.md` §7; types 02, 07, 09, 14, 18, 20):
a 7-point nopert has no two quadrilateral facets meeting in a single vertex,
given general position at the line of their planes: `Minimality.TriGenTieT` (no
segment parallel to it, and the two far vertices at different depths along it,
or their tie settled by a top or bottom vertex, or by the robust form (the shared
vertex off the tied depth), or, at the triple tie with the shared vertex, settled
by Theorem 24.5 of `FEWER-FACES-PROOFS.md` §24: a face one-sided (its other
vertices all on one side of the tied depth) or the shadow triangle obtuse at a far
vertex; weaker than `Minimality.TriGenTieR` and `Minimality.TriGenFar`), or
`Minimality.TriGenFarP` (segments parallel to it allowed, the far vertices at
different depths, except that a tie is allowed when exactly one face has a vertical far edge
(`Minimality.FarDepthOKT`, Proposition 23.19 (1)); when both faces have a vertical far edge,
any tie is allowed except the full rectangle (tops tied and bottoms tied), the tilt sector being
chosen by the depths of the tops, else of the bottoms, `isRupert_vertex_frame_par'`; the
rectangle is allowed too when one face is a triangle (Proposition 24.12), or when both faces are
quadrilaterals and the shared vertex is not at a far depth with all vertices of both faces on
one side of it (`Minimality.RectOK`): then the four mixed sectors, or else one of the two
non-mixed arcs `(−, +, −)`, `(+, −, +)` of Proposition 24.12 (`Minimality.vertex_core_nm`),
works). Besides a parallel segment, the
only position excluded is the triple tie with both faces two-sided and both far
angles of the shadow triangle acute or right (case (c) of Theorem 24.5). -/
theorem not_two_quad_facets_vertex_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hV : V.card = 7) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenTieT V Q1 Q2 v ∨ Minimality.TriGenFarP V Q1 Q2 v) : False := by
  classical
  have hsol := (not_coplanar_iff_interior_convexHull_nonempty _).mp h.1
  -- the two quadrilaterals cover all seven points
  have hcov : Q1 ∪ Q2 = V := by
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset h1V h2V) ?_
    rw [hV, Finset.card_union, hint, h1c, h2c, Finset.card_singleton]
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  obtain ⟨xa, hxa, hxav⟩ := Finset.exists_mem_ne (by omega : 1 < Q1.card) v
  obtain ⟨xb, hxb, hxbv⟩ := Finset.exists_mem_ne (by omega : 1 < Q2.card) v
  have hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1 :=
    ⟨xa, hxa, xb, hxb, hxav, hxbv, fun _ _ _ _ _ _ y hy hy1 hy2 => by
      rw [← hcov, Finset.mem_union] at hy
      exact absurd hy (by tauto)⟩
  have hgen := Minimality.noThreeCollinear_of_not_isRupert hV hsol h.2
  rcases hT with hT | hT
  · exact h.2 (Minimality.isRupert_of_facets_vertex_tieT V hgen Q1 Q2 h1V h2V h1f h2f v hint
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hT hin hsol)
  · exact h.2 (Minimality.isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hT hin)

/-- **No two quadrilateral facets sharing one vertex, with a right or obtuse apex settled**
(Corollary T1 of the triangle-shadow lemma, `FEWER-FACES-PROOFS.md` §7, with Theorems 24.5 and
24.8 of §24; types 02, 07, 09, 14, 18, 20): as `not_two_quad_facets_vertex_of_isNopert`, with
`Minimality.TriGenTieO` in place of `Minimality.TriGenTieT`.  In addition to everything that
`TriGenTieT` allows, the triple tie of case (c) (the far vertices and the shared vertex at one
depth along the line of the planes, both faces two-sided) is settled when the angle of the
shadow triangle at the shared vertex is at least `π/2` (Theorem 24.8: the views of the face circle
of one quadrilateral beside the view along its far edge have a unimodal rim with distinct
depths and no persistent horizontal double normal, so the polyhedron is Rupert by the slide
theorem 18.1).  The only position still excluded besides a parallel segment (other than between two middles of one
face or two hidden vertices) is the triple tie
with both faces two-sided and all three angles of the shadow triangle acute or right
(case (c) of Theorem 24.5 with acute T, or a right angle at a far vertex). -/
theorem not_two_quad_facets_vertex_obtuse_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hV : V.card = 7) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenTieO V Q1 Q2 v ∨ Minimality.TriGenFarP V Q1 Q2 v) : False := by
  classical
  have hsol := (not_coplanar_iff_interior_convexHull_nonempty _).mp h.1
  have hcov : Q1 ∪ Q2 = V := by
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset h1V h2V) ?_
    rw [hV, Finset.card_union, hint, h1c, h2c, Finset.card_singleton]
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  obtain ⟨xa, hxa, hxav⟩ := Finset.exists_mem_ne (by omega : 1 < Q1.card) v
  obtain ⟨xb, hxb, hxbv⟩ := Finset.exists_mem_ne (by omega : 1 < Q2.card) v
  have hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1 :=
    ⟨xa, hxa, xb, hxb, hxav, hxbv, fun _ _ _ _ _ _ y hy hy1 hy2 => by
      rw [← hcov, Finset.mem_union] at hy
      exact absurd hy (by tauto)⟩
  have hgen := Minimality.noThreeCollinear_of_not_isRupert hV hsol h.2
  rcases hT with hT | hT
  · exact h.2 (Minimality.isRupert_of_facets_vertex_tieO V hgen Q1 Q2 h1V h2V h1f h2f v hint
      h1c h2c hcov hT hin hsol)
  · exact h.2 (Minimality.isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hT hin)

/-- **Lemma T at a vertex** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets meeting in a single vertex `v`, with general
position at the line of their planes (`Minimality.TriGenTieT`: no segment
parallel to it, distinct depths along it at the two far ends, or a tie settled
by a top or bottom vertex or by the robust form, or the triple tie with the
shared vertex settled by Theorem 24.5 (a face one-sided or a far angle obtuse);
weaker than `Minimality.TriGenTieR` and `Minimality.TriGenFar`; or `Minimality.TriGenFarP`:
parallel segments allowed, distinct far depths unless exactly one face has a vertical far edge),
never have every
other point strictly inside the shadow triangle of `v` and two further points
`xa`, `xb` of the facets. The interior condition is barycentric, stated with any
facet functionals `f1`, `f2` (it does not depend on their scaling). -/
theorem not_facets_vertex_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1c : 1 < Q1.card) (h2c : 1 < Q2.card) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenTieT V Q1 Q2 v ∨ Minimality.TriGenFarP V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  rcases hT with hT | hT
  · exact h.2 (Minimality.isRupert_of_facets_vertex_tieT V hgen Q1 Q2 h1V h2V h1f h2f v hint
      (Finset.exists_mem_ne h1c v) (Finset.exists_mem_ne h2c v) hT hin
      ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1))
  · exact h.2 (Minimality.isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint
      (Finset.exists_mem_ne h1c v) (Finset.exists_mem_ne h2c v) hT hin)

/-- **Lemma T over an edge** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets sharing exactly the edge `v w`, with general
position along it (`Minimality.EdgeTieR`: no other segment parallel to it except between
two middles of one face or two hidden vertices,
distinct depths along it at the two far ends, or a tie settled by a top or
bottom vertex or with no right angle at the far ends (Lemma T at the tie, robust
form); weaker than `Minimality.EdgeFar`; or `Minimality.EdgeFarP`: segments
parallel to it allowed, distinct far depths unless exactly one face has a vertical far edge),
never have every
other point strictly inside the shadow triangle of the edge and two further
points `xa ∈ Q1 \ Q2`, `xb ∈ Q2 \ Q1` (barycentric form with any facet
functionals `f1`, `f2`). -/
theorem not_facets_edge_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1f : Minimality.IsFacet V Q1) (h2f : Minimality.IsFacet V Q2) (v w : ℝ³) (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w})
    (hZ : Minimality.EdgeTieR V Q1 Q2 v w ∨ Minimality.EdgeFarP V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  rcases hZ with hZ | hZ
  · exact h.2 (Minimality.isRupert_of_facets_edge_tieR V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
      ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hZ ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩
      ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1))
  · exact h.2 (Minimality.isRupert_of_facets_edge_par V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
      ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hZ ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩)

/-- **Lemma T over an edge with a triangle face** (Lemma T at the tie): as
`not_facets_edge_triShadow_of_isNopert`, but when `Q1` or `Q2` is a triangle
the only general position needed is `Minimality.EdgePar` (no other segment
parallel to the edge, except between two middles of one face or two hidden vertices:
Proposition 23.19 (2), (3)): the triangle settles any tie of the far ends. -/
theorem not_facets_edge_tri_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1f : Minimality.IsFacet V Q1) (h2f : Minimality.IsFacet V Q2) (v w : ℝ³) (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w}) (hcard : Q1.card = 3 ∨ Q2.card = 3)
    (hZ : Minimality.EdgePar V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  exact h.2 (Minimality.isRupert_of_facets_edge_tri V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
    ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hcard hZ ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1))

/-- **Flat polygons are Rupert.**  Points in a plane, not all on one line, are
Rupert, whatever their number: hold one copy face-on and pass the other
through it edge-on. -/
theorem isRupert_of_coplanar_of_not_collinear (V : Finset ℝ³)
    (hpl : Coplanar ℝ (V : Set ℝ³)) (hcol : ¬ Collinear ℝ (V : Set ℝ³)) : IsRupert V :=
  Minimality.isRupert_of_coplanar_of_not_collinear V hpl hcol

/-- **Segments and points are not Rupert.**  A nonempty set of points on one
line is not Rupert: all its shadows lie on lines, so they have no interior. -/
theorem not_isRupert_of_collinear (V : Finset ℝ³) (h : Collinear ℝ (V : Set ℝ³))
    (hne : V.Nonempty) : ¬ IsRupert V :=
  Minimality.not_isRupert_of_collinear V h hne

/-- **At most 6 points: exactly the non-collinear sets are Rupert** (and the
empty set, vacuously). -/
theorem isRupert_iff_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6) :
    IsRupert V ↔ (V = ∅ ∨ ¬ Collinear ℝ (V : Set ℝ³)) := by
  constructor
  · intro hR
    by_contra hcon
    push Not at hcon
    exact not_isRupert_of_collinear V hcon.2 hcon.1 hR
  · rintro (rfl | hcol)
    · exact Minimality.isRupert_empty
    · by_cases hpl : Coplanar ℝ (V : Set ℝ³)
      · exact isRupert_of_coplanar_of_not_collinear V hpl hcol
      · exact isRupert_of_card_le_six V hV hpl



/-! ### Every 7-vertex nopert is simplicial: the case split (skeleton)

`anySevenVertexNopertIsSimplicial` proves `AnySevenVertexNopertIsSimplicial` (`MainTheorem.lean`)
down to the combinatorial types. Proved steps: at most 6 points (`isRupert_of_card_le_six`), a
point inside the hull of the others (`isRupert_of_mem_convexHull_erase`), faces of 5 or more
vertices (Theorem A, `facet_card_le_four_of_isNopert`), and that a 2-dimensional extreme face is
a facet (`Minimality.exists_facet_of_isExtreme`, `Minimality/FaceBridge.lean`), and the
classification into the 29 types (`Minimality.exists_sevenType`, `Minimality/Classify.lean`: a
sign-vector certificate checked in the kernel). Not formalized (`sorry`): type 24 inside
`C̄ ∪ Σ_B` (it is proved outside, `not_type24_outside_Cbar_of_isNopert`); for type 29 (split by
the class of its octahedron, `Minimality.type29_cap`, `Minimality.NF29.classes`) the classes K1,
K2 and the class boundaries; and for every other type except 05, 07, 12, 13, 14, 17, 19, 22, 23,
25, 26, 27, 28 (closed completely: each of their views pairs a triangle with another facet,
so `TriGenPar`
or `TriGenFarP` always holds, `Minimality.triGenPar_or_farP_idx`, and `EdgePar` or `EdgeFarP` at the
edge views of 23, 25, 26, 27, `Minimality.edgePar_or_farP_idx`; types 13 and 19 are closed too: at
their edge of two quadrilaterals the only residual is the edge rectangle `Minimality.EdgeRect`,
refuted by a triangle facet, `Minimality.not_edgeRect_type13`, `…type19`; type 10 is closed except
a right triangular prism (`Minimality.type10_rightPrism`: the rectangle at `14` and, by the cyclic
relabelling, at `25`, `36`); for 07 and 14, two quadrilaterals,
the residual position `QuadTripleRect` is refuted from the facets,
`Minimality.not_quadTripleRect_type07`, `…type14`), and for K3 and K4, the special
positions: each type's theorem in `Minimality/Cases.lean` closes the case under its general-position
hypotheses (`byGen1`, …), and the `sorry` that remains has exactly their negation as hypothesis.
Every remaining `sorry` also assumes that no face of the type has an admissible view, i.e.
Theorem 5 (`byThm5Faces`) does not apply to any face. -/

/-- A realized type with a face of 5 or 6 vertices is not a nopert (Theorem A). -/
theorem not_isNopert_of_realizes_big_face {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (h : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hR : Minimality.RealizesFaces x fs) {f : Finset (Fin 7)} (hf : f ∈ fs) (h5 : 5 ≤ f.card)
    (h7 : f.card < 7) : False := by
  classical
  have hV : (Finset.univ.image x).card = 7 := by rw [Finset.card_image_of_injective _ hx]; simp
  have hc : (f.image x).card = f.card := Finset.card_image_of_injective _ hx
  have hsub : f.image x ⊂ Finset.univ.image x := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.image_subset_image (Finset.subset_univ f), ?_⟩
    intro heq
    have := congrArg Finset.card heq
    omega
  have := facet_card_le_four_of_isNopert _ _ h hV hsub (Minimality.isFacet_of_realizesFaces hR hf)
  omega

/-- Split on general position: a per-type theorem with `n` general-position hypotheses
closes the generic case; `spec` is the special-position case. -/
theorem byGen1 {P : Prop} (key : P → False) (spec : ¬ P → False) : False :=
  (Classical.em P).elim key spec

theorem byGen2 {P Q : Prop} (key : P → Q → False) (spec : ¬ (P ∧ Q) → False) : False :=
  byGen1 (fun h : P ∧ Q => key h.1 h.2) spec

theorem byGen3 {P Q R : Prop} (key : P → Q → R → False) (spec : ¬ (P ∧ Q ∧ R) → False) :
    False :=
  byGen1 (fun h : P ∧ Q ∧ R => key h.1 h.2.1 h.2.2) spec

theorem byGen4 {P Q R S : Prop} (key : P → Q → R → S → False)
    (spec : ¬ (P ∧ Q ∧ R ∧ S) → False) : False :=
  byGen1 (fun h : P ∧ Q ∧ R ∧ S => key h.1 h.2.1 h.2.2.1 h.2.2.2) spec

theorem byGen5 {P Q R S T : Prop} (key : P → Q → R → S → T → False)
    (spec : ¬ (P ∧ Q ∧ R ∧ S ∧ T) → False) : False :=
  byGen1 (fun h : P ∧ Q ∧ R ∧ S ∧ T => key h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) spec

theorem byGen7 {P Q R S T U W : Prop} (key : P → Q → R → S → T → U → W → False)
    (spec : ¬ (P ∧ Q ∧ R ∧ S ∧ T ∧ U ∧ W) → False) : False :=
  byGen1 (fun h : P ∧ Q ∧ R ∧ S ∧ T ∧ U ∧ W =>
    key h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2) spec

/-- Cor. T1 for a realized type: two quadrilateral faces `q1`, `q2` meeting only in `v`, under
general position `TriGenTieO` (the triple tie settled by Theorems 24.5 and 24.8, including a
right or obtuse apex of the shadow triangle) or `TriGenFarP` (segments parallel to the line
allowed; for two quadrilaterals also the rectangle of two vertical far edges, tops tied and
bottoms tied, unless the shared vertex is at a far depth with both faces on one side of it:
Proposition 24.12, `Minimality.RectOK`). -/
theorem quadPair {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hR : Minimality.RealizesFaces x fs) (q1 q2 : Finset (Fin 7)) (v : Fin 7)
    (h1 : q1 ∈ fs) (h2 : q2 ∈ fs) (hc1 : q1.card = 4) (hc2 : q2.card = 4)
    (hint : q1 ∩ q2 = {v}) :
    (Minimality.TriGenTieO (Finset.univ.image x) (q1.image x) (q2.image x) (x v) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (q1.image x) (q2.image x) (x v)) → False := by
  classical
  intro hT
  have hV : (Finset.univ.image x).card = 7 := by rw [Finset.card_image_of_injective _ hx]; simp
  refine not_two_quad_facets_vertex_obtuse_of_isNopert _ hN hV (q1.image x) (q2.image x)
    (Finset.image_subset_image (Finset.subset_univ _)) (Finset.image_subset_image (Finset.subset_univ _))
    (by rw [Finset.card_image_of_injective _ hx, hc1]) (by rw [Finset.card_image_of_injective _ hx, hc2])
    (Minimality.isFacet_of_realizesFaces hR h1) (Minimality.isFacet_of_realizesFaces hR h2) (x v) ?_ hT
  rw [← Finset.image_inter _ _ hx, hint, Finset.image_singleton]

/-- Cor. T1 for the types 07 and 14 under the weaker general position `TriGenPar` (no segment
parallel to the line of the two planes) or `TriGenFarP`: case (c) of the triple tie does not occur
at the quadrilaterals `0256`, `1234` of type 07 (`Minimality.triGenTieO_type07`) and `0235`,
`1456` of type 14 (`Minimality.triGenTieO_type14`), by Lemma 23.0 (a) of
`FEWER-FACES-PROOFS.md`, so `TriGenPar` gives `TriGenTieO`.  For two quadrilaterals one of
`TriGenPar`, `TriGenFarP` and the residual position `Minimality.QuadTripleRect` always holds
(`Minimality.triGenPar_or_farP_quad_idx`: a vertical far edge is allowed, and the rectangle of two
of them too, Proposition 24.12), so the general position of the type is `¬ QuadTripleRect` (which holds,
`Minimality.not_quadTripleRect_type07`, `…type14`): the
rectangle of two vertical far edges (tops tied, bottoms tied) with the shared vertex at a tied far
depth and every vertex of both faces on one side of it (the triple tie with both faces one-sided
and a vertical far edge at each far corner; by Lemma 24.14 (α′) a first-order tilt works there
only for an obtuse apex). -/
theorem quadPairPar07 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 6) (hR : Minimality.RealizesFaces x fs) :
    ¬ Minimality.QuadTripleRect (Finset.univ.image x) (({0, 2, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 3, 4} : Finset (Fin 7)).image x) (x 2) → False := by
  subst hfs
  intro hQ
  have hgen := noThreeCollinear_seven x hN hx
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 2, 5, 6} {1, 2, 3, 4} 2 (by decide)
    (by decide) (by decide) with h | h | h
  · exact quadPair hx hN hR {0, 2, 5, 6} {1, 2, 3, 4} 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (Minimality.triGenTieO_type07 hx hR h))
  · exact quadPair hx hN hR {0, 2, 5, 6} {1, 2, 3, 4} 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)
  · exact hQ h

/-- Type 14 of `quadPairPar07`: the quadrilaterals `0235`, `1456` at vertex `5`. -/
theorem quadPairPar14 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 13) (hR : Minimality.RealizesFaces x fs) :
    ¬ Minimality.QuadTripleRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) → False := by
  subst hfs
  intro hQ
  have hgen := noThreeCollinear_seven x hN hx
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 2, 3, 5} {1, 4, 5, 6} 5 (by decide)
    (by decide) (by decide) with h | h | h
  · exact quadPair hx hN hR {0, 2, 3, 5} {1, 4, 5, 6} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (Minimality.triGenTieO_type14 hx hR h))
  · exact quadPair hx hN hR {0, 2, 3, 5} {1, 4, 5, 6} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)
  · exact hQ h

/-- Type 02 of `quadPairPar07`: the quadrilaterals `0235`, `1246` at vertex `2`.  Unlike types 07
and 14, case (c) of the triple tie can occur, so `TriGenPar` does not give `TriGenTieO`; and
`QuadTripleRect` is not refuted from the facets: of the four tie pairs `(a, b)` (`a` in `{0, 5}`,
`b` in `{1, 6}`; far corners `3`, `4`) only `(0, 6)` and `(5, 1)` are killed (by `0134`/`3456` and
`012`/`256`), while `(0, 1)` and `(5, 6)`, the vertical far edges `01`, `56` at the edge view `34`,
are not (`KillL … 2 0 3 5 1 4 6` and `KillL … 2 5 3 0 6 4 1` are false).  Hence what is left of
Cor. T1 here is the acute case-(c) triple tie (`TriGenPar` holds, `TriGenTieO` fails) or
`QuadTripleRect`. -/
theorem quadPairPar02 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 1) (hR : Minimality.RealizesFaces x fs) :
    (Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∧
      ¬ Minimality.TriGenTieO (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2)) ∨
    Minimality.QuadTripleRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2) := by
  subst hfs
  have hgen := noThreeCollinear_seven x hN hx
  by_contra hcon
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 2, 3, 5} {1, 2, 4, 6} 2 (by decide)
    (by decide) (by decide) with h | h | h
  · refine hcon (Or.inl ⟨h, fun hT => ?_⟩)
    exact quadPair hx hN hR {0, 2, 3, 5} {1, 2, 4, 6} 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl hT)
  · exact quadPair hx hN hR {0, 2, 3, 5} {1, 2, 4, 6} 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)
  · exact hcon (Or.inr h)

/-- Type 09 of `quadPairPar02`: the quadrilaterals `0134`, `0256` at vertex `0`.  What is left of
Cor. T1 here is the acute case-(c) triple tie (`TriGenPar` holds, `TriGenTieO` fails) or
`QuadTripleRect`. -/
theorem quadPairPar09 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 8) (hR : Minimality.RealizesFaces x fs) :
    (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0) ∧
      ¬ Minimality.TriGenTieO (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0)) ∨
    Minimality.QuadTripleRect (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
      (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0) := by
  subst hfs
  have hgen := noThreeCollinear_seven x hN hx
  by_contra hcon
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 1, 3, 4} {0, 2, 5, 6} 0 (by decide)
    (by decide) (by decide) with h | h | h
  · refine hcon (Or.inl ⟨h, fun hT => ?_⟩)
    exact quadPair hx hN hR {0, 1, 3, 4} {0, 2, 5, 6} 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl hT)
  · exact quadPair hx hN hR {0, 1, 3, 4} {0, 2, 5, 6} 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)
  · exact hcon (Or.inr h)

/-- Type 18 of `quadPairPar02`: the quadrilaterals `0356`, `1245` at vertex `5`.  Here
`QuadTripleRect` is refuted from the facets (`not_quadTripleRect_type18`), so what is left of
Cor. T1 is exactly the acute case-(c) triple tie (`TriGenPar` holds, `TriGenTieO` fails). -/
theorem quadPairPar18 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 17) (hR : Minimality.RealizesFaces x fs) :
    Minimality.TriGenPar (Finset.univ.image x) (({0, 3, 5, 6} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 5) ∧
      ¬ Minimality.TriGenTieO (Finset.univ.image x) (({0, 3, 5, 6} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 5) := by
  subst hfs
  have hgen := noThreeCollinear_seven x hN hx
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 3, 5, 6} {1, 2, 4, 5} 5 (by decide)
    (by decide) (by decide) with h | h | h
  · refine ⟨h, fun hT => ?_⟩
    exact quadPair hx hN hR {0, 3, 5, 6} {1, 2, 4, 5} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl hT)
  · exact (quadPair hx hN hR {0, 3, 5, 6} {1, 2, 4, 5} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)).elim
  · exact (Minimality.not_quadTripleRect_type18 hx hgen hR h).elim

/-- Type 20 of `quadPairPar02`: the quadrilaterals `0135`, `2456` at vertex `5`.  Here
`QuadTripleRect` is refuted from the facets (`not_quadTripleRect_type20`), so what is left of
Cor. T1 is exactly the acute case-(c) triple tie (`TriGenPar` holds, `TriGenTieO` fails). -/
theorem quadPairPar20 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hfs : fs = Minimality.sevenTypeFaces 19) (hR : Minimality.RealizesFaces x fs) :
    Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) ∧
      ¬ Minimality.TriGenTieO (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) := by
  subst hfs
  have hgen := noThreeCollinear_seven x hN hx
  rcases Minimality.triGenPar_or_farP_quad_idx hx hgen {0, 1, 3, 5} {2, 4, 5, 6} 5 (by decide)
    (by decide) (by decide) with h | h | h
  · refine ⟨h, fun hT => ?_⟩
    exact quadPair hx hN hR {0, 1, 3, 5} {2, 4, 5, 6} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl hT)
  · exact (quadPair hx hN hR {0, 1, 3, 5} {2, 4, 5, 6} 5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr h)).elim
  · exact (Minimality.not_quadTripleRect_type20 hx hgen hR h).elim

/-- Theorem B (`not_four_quad_facets_of_isNopert`) for a realized type with four quadrilateral
faces: in `Minimality.GenPos` the points are not a nopert. -/
theorem fourQuad {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hR : Minimality.RealizesFaces x fs) (q : Fin 4 → Finset (Fin 7)) (hq : ∀ k, q k ∈ fs)
    (hc : ∀ k, (q k).card = 4) (hi : Function.Injective q) :
    Minimality.GenPos (Finset.univ.image x) → False := by
  classical
  intro hg
  have hV : (Finset.univ.image x).card = 7 := by rw [Finset.card_image_of_injective _ hx]; simp
  exact not_four_quad_facets_of_isNopert _ hN hV hg (fun k => (q k).image x)
    (fun k => Finset.image_subset_image (Finset.subset_univ _))
    (fun k => by rw [Finset.card_image_of_injective _ hx, hc k])
    (fun k => Minimality.isFacet_of_realizesFaces hR (hq k))
    ((Finset.image_injective hx).comp hi)

/-- Theorem 5 on the faces of a realized type: if some face has an admissible view, the
points are Rupert. Used to narrow the special-position branches of the skeleton. -/
theorem byThm5Faces {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x)) (fs : List (Finset (Fin 7)))
    (hfs : ∀ f ∈ fs, 3 ≤ f.card)
    (rest : (∀ f ∈ fs, ¬ (Minimality.admissibleViews (Finset.univ.image x) (f.image x)).Nonempty) → False) :
    False := by
  classical
  by_cases hex : ∃ f ∈ fs, (Minimality.admissibleViews (Finset.univ.image x) (f.image x)).Nonempty
  · obtain ⟨f, hf, hU⟩ := hex
    have hV : (Finset.univ.image x).card = 7 := by
      rw [Finset.card_image_of_injective _ hx]; simp
    have hsol : (interior (convexHull ℝ ((Finset.univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty :=
      (not_coplanar_iff_interior_convexHull_nonempty _).mp hN.1
    have h3 := Minimality.noThreeCollinear_of_not_isRupert hV hsol hN.2
    have hcol : ¬ Collinear ℝ ((f.image x : Finset ℝ³) : Set ℝ³) := by
      intro hc
      obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := (Finset.two_lt_card (s := f)).mp (by have := hfs f hf; omega)
      have hmem : ∀ i ∈ f, x i ∈ ((f.image x : Finset ℝ³) : Set ℝ³) := fun i hi => by
        simp only [Finset.coe_image]; exact ⟨i, hi, rfl⟩
      obtain ⟨v, hv⟩ := (collinear_iff_of_mem (hmem a ha)).mp hc
      obtain ⟨s, hs⟩ := hv _ (hmem b hb)
      obtain ⟨t, ht⟩ := hv _ (hmem c hc')
      have hs0 : s ≠ 0 := by
        rintro rfl
        have e : x b = x a := by simpa using hs
        exact hab (hx e).symm
      refine h3 (x a) ?_ (x b) ?_ (x c) ?_ (fun h => hab (hx h)) (fun h => hac (hx h))
        (fun h => hbc (hx h)) (t / s) ?_
      · simp
      · simp
      · simp
      · rw [ht, hs]
        simp only [vadd_eq_add]
        rw [add_sub_cancel_right, add_sub_cancel_right, smul_smul, div_mul_cancel₀ _ hs0]
    exact Minimality.isRupert_of_admissibleViews_nonempty _ _
      (Finset.image_subset_image (Finset.subset_univ _)) hcol hU |> hN.2
  · push Not at hex
    exact rest (fun f hf => by simpa [Set.not_nonempty_iff_eq_empty] using hex f hf)

/-- **Every 7-vertex nopert is simplicial** (skeleton: the case split into the 29 non-simplicial
types is complete; the `sorry`s are listed in the section comment). -/
theorem anySevenVertexNopertIsSimplicial : AnySevenVertexNopertIsSimplicial := by
  classical
  intro V hcard hsol hnR face ⟨hext, hdim, hconv⟩
  -- at most six points are Rupert
  have h7 : V.card = 7 := by
    by_contra hne
    exact hnR (Minimality.isRupert_of_card_le_six V (by omega) hsol)
  -- a point in the hull of the others leaves six points
  have hvert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³) :=
    fun v hv hin => hnR (Minimality.isRupert_of_mem_convexHull_erase h7 hsol hv hin)
  have hN : IsNopert V := (isNopert_iff V).2 ⟨hsol, hnR⟩
  -- the face is a facet `F` with at least 3 and (Theorem A) at most 4 points
  obtain ⟨F, hFV, hF3, hfacet, hFext⟩ :=
    Minimality.exists_facet_of_isExtreme V hsol hvert face hext hdim hconv
  rw [hFext, Set.ncard_coe_finset]
  have hF4 : F.card ≤ 4 := facet_card_le_four_of_isNopert V F hN h7 hFV hfacet
  by_contra hne
  -- a quadrilateral facet: label the points by one of the 29 types
  obtain ⟨k, x, hx, rfl, hR⟩ :=
    Minimality.exists_sevenType _ h7 hvert F hFV.subset (by omega) hfacet
  have big : ∀ f ∈ Minimality.sevenTypeFaces k, 5 ≤ f.card → f.card < 7 → False :=
    fun f hf h5 h7' => not_isNopert_of_realizes_big_face hx hN hR hf h5 h7'
  have h3 : ∀ k : Fin 29, ∀ f ∈ Minimality.sevenTypeFaces k, 3 ≤ f.card := by decide +kernel
  have h3 := h3 k
  fin_cases k
  · exact big {1, 2, 4, 5, 6} (by decide) (by decide) (by decide)  -- type 01: Theorem A
  · -- type 02: Cor. T1 at the quadrilaterals 0235, 1246 (sharing vertex 2); where its general
    -- position fails, Theorem B on the four quadrilaterals 0134, 0235, 1246, 3456 under
    -- `GenPos`, and Lemma E or a planar closing at the edge 34 (23.12, metric-free:
    -- `type02_edge34_byGen''`, off a far triple tie, or an HDN at 34 with the conditions of §22.4 failing; a vertical far edge 01 or
    -- 56 at the edge view 34 is no exception: its far point is a double over the rim corner,
    -- Lemma 16.27′, `isRupert_edgePair_robustD`).
    -- The `sorry` has in context: `¬ Type02EdgeGen'' x` (a far depth triple tie, codimension 2; or a
    -- horizontal double normal at 34 of a closing together with a failure of the conditions of
    -- §22.4 there, `Type02HDNOK`: a segment other than 34 parallel to it, (G1), two equal depths, two
    -- directions of double normals, a double normal perpendicular to a face from a face vertex, or
    -- a far edge parallel to a face with Lemma E not strict; codimension >= 2);
    -- `¬ GenPos` (Theorem B); and
    -- `quadPairPar02`: the acute case-(c) triple tie at 0235, 1246 (`TriGenPar` but not
    -- `TriGenTieO`, vertex 2) or `QuadTripleRect` there
    have hQ := quadPairPar02 hx hN rfl hR
    exact byGen1 (Minimality.type02_edge34_byGen'' hx (noThreeCollinear_seven x hN hx) hN hR) (fun _ =>
      byGen1 (fourQuad hx hN hR ![{0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 6}, {3, 4, 5, 6}]
          (by decide) (by decide) (by decide))
        (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
  · exact big {0, 2, 3, 4, 5, 6} (by decide) (by decide) (by decide)  -- type 03: Theorem A
  · exact big {1, 2, 3, 5, 6} (by decide) (by decide) (by decide)  -- type 04: Theorem A
  · -- type 05: `not_type05_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  Both views pair a quadrilateral with the
    -- triangle `246`, so `TriGenPar` or `TriGenFarP` always holds (`triGenPar_or_farP_idx`:
    -- a vertical far edge is allowed, the full rectangle too, Proposition 24.12): closed, no
    -- special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 1, 2, 3} (by decide)
    obtain ⟨fB, hfB⟩ := hR {0, 1, 4, 5} (by decide)
    obtain ⟨fG, hfG⟩ := hR {2, 4, 6} (by decide)
    obtain ⟨fK, hfK⟩ := hR {4, 5, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {2, 3, 4} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type05_of_isNopert_sv x hN hx fA fB fG fK fH hfA hfB hfG hfK hfH
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 2, 3} {2, 4, 6} 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 4, 5} {2, 4, 6} 4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact big {1, 2, 4, 5, 6} (by decide) (by decide) (by decide)  -- type 06: Theorem A
  · -- type 07: Cor. T1 at the quadrilaterals 0256, 1234 (sharing vertex 2); case (c) of the
    -- triple tie does not occur (Lemma 23.0 (a)), so only `TriGenPar` (no segment parallel to the
    -- line of the two planes) or `TriGenFarP` is needed, and one of them holds unless
    -- `QuadTripleRect` (`triGenPar_or_farP_quad_idx`).  That residual position (a rectangle of two
    -- vertical far edges whose far corner is tied with the shared vertex, both faces one-sided)
    -- is refuted from the facets of the type (`not_quadTripleRect_type07`): closed, no special
    -- position is left
    have hgen := noThreeCollinear_seven x hN hx
    exact quadPairPar07 hx hN rfl hR (Minimality.not_quadTripleRect_type07 hx hgen hR)
  · -- type 08: `not_type08_of_isNopert'`; its general position (2 hypotheses) is asked, the special
    -- positions are open in Lean.  The far triple tie (touching) of the named closings N2, T4 is
    -- no longer excluded in `Type08Gen`: with `c'` (resp. `b'`) beyond it is closed by the
    -- horizontal end of a face circle (Proposition 30.4, `isRupert_touchN2`, `isRupert_touchT4`)
    -- under the codimension-3 conditions `Touch30N2`, `Touch30T4`, `touchTie`
    obtain ⟨fA, hfA⟩ := hR {0, 1, 2, 3} (by decide)
    obtain ⟨fB, hfB⟩ := hR {0, 2, 4, 5} (by decide)
    obtain ⟨fC, hfC⟩ := hR {2, 3, 5, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 1, 4} (by decide)
    obtain ⟨fE, hfE⟩ := hR {1, 3, 6} (by decide)
    obtain ⟨fF, hfF⟩ := hR {1, 4, 6} (by decide)
    obtain ⟨fG, hfG⟩ := hR {4, 5, 6} (by decide)
    exact byGen2 (not_type08_of_isNopert' x hN hx fA fB fC fD fE fF fG hfA hfB hfC hfD hfE hfF hfG)
      (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry))
  · -- type 09: Cor. T1 at the quadrilaterals 0134, 0256 (sharing vertex 0); general position
    -- asked, the special positions are open in Lean.  `quadPairPar09` (as `quadPairPar02`):
    -- `TriGenFarP` and `TriGenPar ∧ TriGenTieO` are closed by `quadPair`; the `sorry` has in
    -- context `hQ`: the acute case-(c) triple tie at 0134, 0256 (`TriGenPar` but not
    -- `TriGenTieO`, vertex 0) or `QuadTripleRect`
    have hQ := quadPairPar09 hx hN rfl hR
    exact byGen1 (quadPair hx hN hR {0, 1, 3, 4} {0, 2, 5, 6} 0 (by decide) (by decide) (by decide) (by decide)
      (by decide)) (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry))
  · -- type 10: `not_type10_of_isNopert_sv` closes everything except the edge rectangle at the
    -- edge `14` (`Minimality.type10_edgeRect`).  The face set is invariant under the cyclic
    -- relabelling `ρ10` (`1 → 2 → 3`, `4 → 5 → 6`), so the same holds at `25`, `36`; the three
    -- rectangles force a right triangular prism (`Minimality.type10_rightPrism`: lateral edges
    -- `14`, `25`, `36` equal vectors, triangle `123` orthogonal to them), and a capped right
    -- prism is Rupert (`Minimality.isRupert_type10_rightPrism`: the apex is hidden at the
    -- near-axis views of Theorem 8.1): closed
    have hP : Minimality.RightPrism10 x := Minimality.type10_rightPrism x hN hx hR
    exact (hN.2 (Minimality.isRupert_type10_rightPrism x hx hP hR)).elim
  · exact big {0, 2, 3, 4, 6} (by decide) (by decide) (by decide)  -- type 11: Theorem A
  · -- type 12: `not_type12_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 24.15).  Both views have a triangle (`024`), so
    -- `TriGenPar` or `TriGenFarP` always holds (`triGenPar_or_farP_idx`): closed
    obtain ⟨fA, hfA⟩ := hR {0, 1, 3, 5} (by decide)
    obtain ⟨fB, hfB⟩ := hR {0, 3, 4, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 2, 4} (by decide)
    obtain ⟨fG, hfG⟩ := hR {2, 3, 6} (by decide)
    obtain ⟨fJ, hfJ⟩ := hR {2, 4, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type12_of_isNopert_sv x hN hx fA fB fD fG fJ hfA hfB hfD hfG hfJ
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 3, 5} {0, 2, 4} 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4} {2, 3, 6} 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 13: `not_type13_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  The vertex view has the triangle `123`
    -- (`triGenPar_or_farP_idx`); at the edge `45` of the quadrilaterals `0145`, `2456`,
    -- `EdgeTieR` or `EdgeFarP` holds (`edgeTieR_or_farP_rect_idx`) unless the edge rectangle,
    -- which makes `0, 1, 2, 6` a parallelogram, contradicting the facet `126`
    -- (`not_edgeRect_type13`): closed, no special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 1, 4, 5} (by decide)
    obtain ⟨fB, hfB⟩ := hR {2, 4, 5, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {1, 2, 3} (by decide)
    obtain ⟨fG, hfG⟩ := hR {1, 2, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    have hT := Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 4, 5} {1, 2, 3} 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hE : _ ∨ _ := (Minimality.edgeTieR_or_farP_rect_idx hx hgen {0, 1, 4, 5} {2, 4, 5, 6} 4 5
      (by decide) (by decide) (by decide) (by decide)).imp_right fun h =>
      h.resolve_right (Minimality.not_edgeRect_type13 hx fG hfG)
    exact not_type13_of_isNopert_sv x hN hx fA fB fD fG hfA hfB hfD hfG (fun _ => hE) (fun _ => hT)
  · -- type 14: Cor. T1 at the quadrilaterals 0235, 1456 (sharing vertex 5); case (c) of the
    -- triple tie does not occur (Lemma 23.0 (a)), so only `TriGenPar` or `TriGenFarP` is needed,
    -- and one of them holds unless `QuadTripleRect`, which is refuted from the facets of the type
    -- (`not_quadTripleRect_type14`): closed
    have hgen := noThreeCollinear_seven x hN hx
    exact quadPairPar14 hx hN rfl hR (Minimality.not_quadTripleRect_type14 hx hgen hR)
  · exact big {0, 1, 4, 5, 6} (by decide) (by decide) (by decide)  -- type 15: Theorem A
  · -- type 16: `not_type16_of_multiView16` (Theorem 24.3: ties at a family of tilt tests with
    -- realizing tilts, `Minimality.MultiView16`; the cover is affine-invariant, so metric-free), where
    -- it holds; else `not_type16_of_isNopert_codim2'`; its general position (5 hypotheses) is asked,
    -- the special positions are open in Lean
    obtain ⟨fA, hfA⟩ := hR {0, 2, 3, 5} (by decide)
    obtain ⟨fB, hfB⟩ := hR {1, 3, 5, 6} (by decide)
    obtain ⟨fC, hfC⟩ := hR {0, 2, 4} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 3, 6} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 4, 6} (by decide)
    obtain ⟨fF, hfF⟩ := hR {1, 4, 5} (by decide)
    obtain ⟨fG, hfG⟩ := hR {1, 4, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {2, 4, 5} (by decide)
    exact byGen1 (not_type16_of_multiView16 x hN hx fA fB fC fD fE fF fG fH hfA hfB hfC hfD hfE hfF
      hfG hfH) (fun _ => byGen5 (fun h35 hEd hQ hV htie => not_type16_of_isNopert_codim2' x hN hx fA
        fB fC fD fE fF fG fH hfA hfB hfC hfD hfE hfF hfG hfH h35 hEd hQ hV (Or.inl htie))
      (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
  · -- type 17: `not_type17_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  Both views have the triangle `136`, so
    -- `TriGenPar` or `TriGenFarP` always holds (`triGenPar_or_farP_idx`): closed
    obtain ⟨fA, hfA⟩ := hR {0, 2, 4, 6} (by decide)
    obtain ⟨fB, hfB⟩ := hR {2, 3, 4, 5} (by decide)
    obtain ⟨fD, hfD⟩ := hR {1, 3, 6} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 3, 4} (by decide)
    obtain ⟨fF, hfF⟩ := hR {0, 3, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type17_of_isNopert_sv x hN hx fA fB fD fE fF hfA hfB hfD hfE hfF
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {1, 3, 6} {2, 3, 4, 5} 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4, 6} {1, 3, 6} 6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 18: Cor. T1 at the quadrilaterals 0356, 1245 (sharing vertex 5).  `quadPairPar18` (as
    -- `quadPairPar02`, with `QuadTripleRect` refuted from the facets): the `sorry` has in context
    -- `hQ`, exactly the acute case-(c) triple tie at 0356, 1245 (`TriGenPar` but not `TriGenTieO`,
    -- vertex 5); on paper closed off explicit special positions (§27 continued (4), 27.59)
    have hQ := quadPairPar18 hx hN rfl hR
    exact byGen1 (quadPair hx hN hR {0, 3, 5, 6} {1, 2, 4, 5} 5 (by decide) (by decide) (by decide) (by decide)
      (by decide)) (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry))
  · -- type 19: `not_type19_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  The vertex view has the triangle `046`
    -- (`triGenPar_or_farP_idx`); at the edge `35` of the quadrilaterals `0235`, `1356`,
    -- `EdgeTieR` or `EdgeFarP` holds (`edgeTieR_or_farP_rect_idx`) unless the edge rectangle,
    -- which makes `0, 2, 1, 6` a parallelogram, contradicting the facet `026`
    -- (`not_edgeRect_type19`): closed, no special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 2, 3, 5} (by decide)
    obtain ⟨fB, hfB⟩ := hR {1, 3, 5, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 4, 6} (by decide)
    obtain ⟨fG, hfG⟩ := hR {3, 4, 6} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 2, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    have hT := Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 3, 5} {0, 4, 6} 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hE : _ ∨ _ := (Minimality.edgeTieR_or_farP_rect_idx hx hgen {0, 2, 3, 5} {1, 3, 5, 6} 3 5
      (by decide) (by decide) (by decide) (by decide)).imp_right fun h =>
      h.resolve_right (Minimality.not_edgeRect_type19 hx fE hfE)
    exact not_type19_of_isNopert_sv x hN hx fA fB fD fG fE hfA hfB hfD hfG hfE (fun _ => hE) (fun _ => hT)
  · -- type 20: Cor. T1 at the quadrilaterals 0135, 2456 (sharing vertex 5).  `quadPairPar20` (as
    -- `quadPairPar02`, with `QuadTripleRect` refuted from the facets): the `sorry` has in context
    -- `hQ`, exactly the acute case-(c) triple tie at 0135, 2456 (`TriGenPar` but not `TriGenTieO`,
    -- vertex 5); on paper closed by §27 continued (4) up to a ~0.01% twisted remainder
    have hQ := quadPairPar20 hx hN rfl hR
    exact byGen1 (quadPair hx hN hR {0, 1, 3, 5} {2, 4, 5, 6} 5 (by decide) (by decide) (by decide) (by decide)
      (by decide)) (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry))
  · -- type 21: `not_type21_of_multiView21` (Theorem 24.3: ties at a family of tilt tests with
    -- realizing tilts, `Minimality.MultiView21`; the cover is affine-invariant, so metric-free), where
    -- it holds; else `not_type21_of_isNopert_codim2'`; its general position (7 hypotheses) is asked,
    -- the special positions are open in Lean
    obtain ⟨fA, hfA⟩ := hR {0, 1, 4} (by decide)
    obtain ⟨fB, hfB⟩ := hR {0, 1, 5} (by decide)
    obtain ⟨fC, hfC⟩ := hR {0, 2, 5, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 4, 6} (by decide)
    obtain ⟨fE, hfE⟩ := hR {1, 3, 4} (by decide)
    obtain ⟨fF, hfF⟩ := hR {1, 3, 5} (by decide)
    obtain ⟨fG, hfG⟩ := hR {2, 3, 4, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {2, 3, 5} (by decide)
    exact byGen1 (not_type21_of_multiView21 x hN hx fA fB fC fD fE fF fG fH hfA hfB hfC hfD hfE hfF
      hfG hfH) (fun _ => byGen7 (fun hQ h5 h26 hEd hVq hV htie =>
        not_type21_of_isNopert_codim2' x hN hx fA fB fC fD fE fF fG fH hfA hfB hfC hfD hfE hfF hfG
          hfH hQ h5 h26 hEd hVq hV (Or.inl htie))
      (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
  · -- type 22: `not_type22_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 24.15).  Both views have the triangle `246`, so
    -- `TriGenPar` or `TriGenFarP` always holds (`triGenPar_or_farP_idx`): closed
    obtain ⟨fA, hfA⟩ := hR {0, 1, 3, 4} (by decide)
    obtain ⟨fD, hfD⟩ := hR {1, 2, 5} (by decide)
    obtain ⟨fG, hfG⟩ := hR {2, 4, 6} (by decide)
    obtain ⟨fN, hfN⟩ := hR {1, 4, 6} (by decide)
    obtain ⟨fI, hfI⟩ := hR {2, 5, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type22_of_isNopert_sv x hN hx fA fD fG fN fI hfA hfD hfG hfN hfI
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {1, 2, 5} {2, 4, 6} 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 3, 4} {2, 4, 6} 4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 23: `not_type23_of_isNopert_sv`; its general position (3 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  The edge view `04` has the triangle `014`
    -- (`edgePar_or_farP_idx`: `EdgePar` or `EdgeFarP` always holds) and both vertex views have a
    -- triangle (`triGenPar_or_farP_idx`): closed, no special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 3, 4, 5} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 1, 4} (by decide)
    obtain ⟨fE, hfE⟩ := hR {1, 2, 5} (by decide)
    obtain ⟨fH, hfH⟩ := hR {1, 5, 6} (by decide)
    obtain ⟨fK, hfK⟩ := hR {4, 5, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type23_of_isNopert_sv x hN hx fA fD fE fH fK hfA hfD hfE hfH hfK
      (fun _ => (Minimality.edgePar_or_farP_idx hx hgen {0, 1, 4} {0, 3, 4, 5} 0 4
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ => (Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 4} {1, 5, 6} 1
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ => (Minimality.triGenPar_or_farP_idx hx hgen {0, 3, 4, 5} {1, 2, 5} 5
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
  · -- type 24: `not_type24_outside_Cbar_of_isNopert`; proved outside C̄ ∪ Σ_B
    obtain ⟨fA, hfA⟩ := hR {0, 1, 2} (by decide)
    obtain ⟨fB, hfB⟩ := hR {0, 1, 6} (by decide)
    obtain ⟨fC, hfC⟩ := hR {1, 2, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {2, 3, 6} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 4, 6} (by decide)
    obtain ⟨fF, hfF⟩ := hR {0, 2, 5} (by decide)
    -- the sorry: type 24 inside C̄ = {ω3, ω4, ω5 > 0, Δ ≥ 0} (open), or in Σ_B without a free side
    -- crossing
    exact byGen2
      (not_type24_outside_Cbar_of_isNopert x hN fA fB fC fD fE fF hfA hfB hfC hfD hfE hfF)
      (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry))
  · -- type 25: `not_type25_of_isNopert`; its general position (3 hypotheses) holds always: the
    -- edge view `13` has two triangles (`edgePar_or_farP_idx`), the vertex views a triangle
    -- (`triGenPar_or_farP_idx`): closed, no special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 2, 4, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 1, 3} (by decide)
    obtain ⟨fF, hfF⟩ := hR {1, 3, 6} (by decide)
    obtain ⟨fG, hfG⟩ := hR {0, 5, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {0, 3, 5} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 1, 4} (by decide)
    obtain ⟨fI, hfI⟩ := hR {1, 2, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type25_of_isNopert x hN hx fA fD fF fG fH fE fI hfA hfD hfF hfG hfH hfE hfI
      (Minimality.edgePar_or_farP_idx hx hgen {0, 1, 3} {1, 3, 6} 1 3
        (by decide) (by decide) (by decide) (by decide) (by decide))
      (Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 3} {0, 2, 4, 6} 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 3} {0, 5, 6} 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 26: `not_type26_of_isNopert`; its general position (3 hypotheses) holds always: the
    -- edge view `04` has the triangle `034` (`edgePar_or_farP_idx`), the vertex views a triangle
    -- (`triGenPar_or_farP_idx`): closed, no special position is left
    obtain ⟨fA, hfA⟩ := hR {0, 2, 4, 6} (by decide)
    obtain ⟨fT, hfT⟩ := hR {0, 3, 4} (by decide)
    obtain ⟨fG, hfG⟩ := hR {2, 3, 5} (by decide)
    obtain ⟨fH, hfH⟩ := hR {1, 3, 6} (by decide)
    obtain ⟨fU, hfU⟩ := hR {0, 1, 3} (by decide)
    obtain ⟨fW, hfW⟩ := hR {0, 1, 6} (by decide)
    obtain ⟨fY, hfY⟩ := hR {2, 4, 5} (by decide)
    obtain ⟨fZ, hfZ⟩ := hR {3, 4, 5} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type26_of_isNopert x hN hx fA fT fG fH fU fW fY fZ hfA hfT hfG hfH hfU hfW hfY hfZ
      (Minimality.edgePar_or_farP_idx hx hgen {0, 2, 4, 6} {0, 3, 4} 0 4
        (by decide) (by decide) (by decide) (by decide) (by decide))
      (Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4, 6} {2, 3, 5} 2
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4, 6} {1, 3, 6} 6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 27: `not_type27_of_isNopert_sv`; its general position (3 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 26.8).  The edge view `25` has the triangle `025`
    -- (`edgePar_or_farP_idx`) and both vertex views a triangle (`triGenPar_or_farP_idx`): closed,
    -- no special position is left
    obtain ⟨fB, hfB⟩ := hR {2, 3, 5, 6} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 2, 5} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 1, 6} (by decide)
    obtain ⟨fG, hfG⟩ := hR {0, 4, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {0, 4, 5} (by decide)
    obtain ⟨fI, hfI⟩ := hR {0, 1, 2} (by decide)
    obtain ⟨fJ, hfJ⟩ := hR {4, 5, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type27_of_isNopert_sv x hN hx fB fD fE fG fH fI fJ hfB hfD hfE hfG hfH hfI hfJ
      (fun _ => (Minimality.edgePar_or_farP_idx hx hgen {0, 2, 5} {2, 3, 5, 6} 2 5
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ => (Minimality.triGenPar_or_farP_idx hx hgen {0, 1, 6} {2, 3, 5, 6} 6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ => (Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 5} {0, 4, 6} 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
  · -- type 28: `not_type28_of_isNopert_sv`; its general position (2 hypotheses) is asked off the
    -- special value of Lemma T′ (settled there, 24.15).  Both views pair the quadrilateral `0245`
    -- with a triangle, so `TriGenPar` or `TriGenFarP` always holds (`triGenPar_or_farP_idx`):
    -- closed
    obtain ⟨fA, hfA⟩ := hR {0, 2, 4, 5} (by decide)
    obtain ⟨fD, hfD⟩ := hR {0, 3, 6} (by decide)
    obtain ⟨fG, hfG⟩ := hR {1, 4, 6} (by decide)
    obtain ⟨fH, hfH⟩ := hR {0, 2, 3} (by decide)
    obtain ⟨fF, hfF⟩ := hR {0, 1, 5} (by decide)
    obtain ⟨fM, hfM⟩ := hR {1, 4, 5} (by decide)
    obtain ⟨fE, hfE⟩ := hR {0, 1, 6} (by decide)
    have hgen := noThreeCollinear_seven x hN hx
    exact not_type28_of_isNopert_sv x hN hx fA fD fG fH fF fM fE hfA hfD hfG hfH hfF hfM hfE
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4, 5} {1, 4, 6} 4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Minimality.triGenPar_or_farP_idx hx hgen {0, 2, 4, 5} {0, 3, 6} 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · -- type 29: the octahedron `O = K − 6` with the cap `6` (`Minimality.type29_cap`) has the normal
    -- form `N` (Lemma 21.1); its class (Lemma 21.2) is the sign pattern of `(a2, b0, V)`. Classes K3
    -- and K4 (`NF29.isRupert_K3a_all`, …, as in `isRupert_type29_K3`, `isRupert_type29_K4`) are
    -- proved under their general position (`K3Gen`, `K3C1Gen`, `K4Gen`, `K4C1Gen` of `N` for the
    -- a forms, of `N.sigma` for the b forms), and outside codimension 2 (`NF29.isRupert_K3a_codim2`,
    -- …: at most one tie, and no HDN or its escape per closing, §28); open in Lean: the class
    -- boundaries, K2, K1, and the codimension-2 special positions of K3 and K4
    obtain ⟨F, hd⟩ := Minimality.type29_cap hx hvert hR
    set N := Minimality.IsCap29.toNF29 hx F hd
    rcases N.classes with hbd | hK2 | hK1 | ⟨ha2, hb0, hV⟩ | ⟨ha2, hb0, hV⟩ | ⟨ha2, hb0, hV⟩ |
      ⟨ha2, hb0, hV⟩
    · exact byThm5Faces hx hN _ h3 (fun _ => sorry)  -- a class boundary: `a2 = 0`, `b0 = 0` or `V = 0`
    · exact byThm5Faces hx hN _ h3 (fun _ => sorry)  -- class K2: `a2, b0 < 0`
    · exact byThm5Faces hx hN _ h3 (fun _ => sorry)  -- class K1: `a2 < 0 < b0`, `V < 0` (K1a), or `a2 > 0 > b0`, `V > 0` (K1b)
    · -- class K3a: outside codimension 2 (§28, `NF29.isRupert_K3a_codim2`), else its general position
      exact byGen2 (fun htie hH => hnR (N.isRupert_K3a_codim2 ha2 hb0 hV htie hH))
        (fun _ => byGen2 (fun G G1 => hnR (N.isRupert_K3a_all ha2 hb0 hV G G1))
          (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
    · -- class K3b: outside codimension 2 (§28, `NF29.isRupert_K3b_codim2`), else its general position
      exact byGen2 (fun htie hH => hnR (N.isRupert_K3b_codim2 ha2 hb0 hV htie hH))
        (fun _ => byGen2 (fun G G1 => hnR (N.isRupert_K3b_all ha2 hb0 hV G G1))
          (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
    · -- class K4a: outside codimension 2 (§28, `NF29.isRupert_K4a_codim2`), else its general position
      exact byGen2 (fun htie hH => hnR (N.isRupert_K4a_codim2 ha2 hb0 hV htie hH))
        (fun _ => byGen2 (fun G G1 => hnR (N.isRupert_K4a_all ha2 hb0 hV G G1))
          (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))
    · -- class K4b: outside codimension 2 (§28, `NF29.isRupert_K4b_codim2`), else its general position
      exact byGen2 (fun htie hH => hnR (N.isRupert_K4b_codim2 ha2 hb0 hV htie hH))
        (fun _ => byGen2 (fun G G1 => hnR (N.isRupert_K4b_all ha2 hb0 hV G G1))
          (fun _ => byThm5Faces hx hN _ h3 (fun _ => sorry)))

end
