module

public import Minimality.Cases
public import Minimality.SevenTypes

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
different depths, one far end a single vertex). Besides a parallel segment, the
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

/-- **Lemma T at a vertex** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets meeting in a single vertex `v`, with general
position at the line of their planes (`Minimality.TriGenTieT`: no segment
parallel to it, distinct depths along it at the two far ends, or a tie settled
by a top or bottom vertex or by the robust form, or the triple tie with the
shared vertex settled by Theorem 24.5 (a face one-sided or a far angle obtuse);
weaker than `Minimality.TriGenTieR` and `Minimality.TriGenFar`; or `Minimality.TriGenFarP`: parallel segments allowed,
distinct far depths, one far end a single vertex), never have every
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
position along it (`Minimality.EdgeTieR`: no other segment parallel to it,
distinct depths along it at the two far ends, or a tie settled by a top or
bottom vertex or with no right angle at the far ends (Lemma T at the tie, robust
form); weaker than `Minimality.EdgeFar`; or `Minimality.EdgeFarP`: segments
parallel to it allowed, distinct far depths, one far end a single vertex),
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
parallel to the edge): the triangle settles any tie of the far ends. -/
theorem not_facets_edge_tri_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1f : Minimality.IsFacet V Q1) (h2f : Minimality.IsFacet V Q2) (v w : ℝ³) (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w}) (hcard : Q1.card = 3 ∨ Q2.card = 3)
    (hZ : Minimality.EdgePar V v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  exact h.2 (Minimality.isRupert_of_facets_edge_tri V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
    ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hcard hZ ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩)

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
vertices (Theorem A, `facet_card_le_four_of_isNopert`). Not formalized (`sorry`): the passage
from an extreme face to a facet (`exists_facet_of_isExtreme`), the classification into the 29
types (`Minimality.exists_sevenType`), and every type except type 10 in general position, which
uses `not_type10_of_isNopert_sv` (`Minimality/Cases.lean`). -/

/-- **An extreme face of dimension 2 is a facet** (not formalized; standard polytope theory):
for points in convex position, a convex extreme subset of their hull with a 2-dimensional
affine span is cut out by an affine functional, and its extreme points are the points of `V`
on it: at least 3, and not all of `V` (a solid hull is not a facet). -/
theorem exists_facet_of_isExtreme (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hvert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³))
    (face : Set ℝ³) (hext : IsExtreme ℝ (convexHull ℝ (V : Set ℝ³)) face)
    (hdim : (affineSpan ℝ face).finDim = 2) (hconv : Convex ℝ face) :
    ∃ F : Finset ℝ³, F ⊂ V ∧ 3 ≤ F.card ∧ Minimality.IsFacet V F ∧
      face.extremePoints ℝ = (F : Set ℝ³) := by
  sorry

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

/-- **Every 7-vertex nopert is simplicial** (skeleton: the case split into the 29 non-simplicial
types is complete, most cases are `sorry`; see the section comment). -/
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
  obtain ⟨F, hFV, hF3, hfacet, hFext⟩ := exists_facet_of_isExtreme V hsol hvert face hext hdim hconv
  rw [hFext, Set.ncard_coe_finset]
  have hF4 : F.card ≤ 4 := facet_card_le_four_of_isNopert V F hN h7 hFV hfacet
  by_contra hne
  -- a quadrilateral facet: label the points by one of the 29 types
  obtain ⟨k, x, hx, rfl, hR⟩ :=
    Minimality.exists_sevenType _ h7 hsol hvert F hFV.subset (by omega) hfacet
  have big : ∀ f ∈ Minimality.sevenTypeFaces k, 5 ≤ f.card → f.card < 7 → False :=
    fun f hf h5 h7' => not_isNopert_of_realizes_big_face hx hN hR hf h5 h7'
  fin_cases k
  · exact big {1, 2, 4, 5, 6} (by decide) (by decide) (by decide)   -- type 01
  · sorry   -- type 02: `not_two_quad_facets_vertex_of_isNopert` (Cor. T1)
  · exact big {0, 2, 3, 4, 5, 6} (by decide) (by decide) (by decide)   -- type 03
  · exact big {1, 2, 3, 5, 6} (by decide) (by decide) (by decide)   -- type 04
  · sorry   -- type 05: `not_type05_of_isNopert_sv`
  · exact big {1, 2, 4, 5, 6} (by decide) (by decide) (by decide)   -- type 06
  · sorry   -- type 07: `not_two_quad_facets_vertex_of_isNopert`
  · sorry   -- type 08: `not_type08_of_isNopert'` (outside codimension 2)
  · sorry   -- type 09: `not_two_quad_facets_vertex_of_isNopert` (case (c) open)
  · -- type 10: Theorem E (`not_type10_of_isNopert_sv`) in general position
    obtain ⟨fA, hA⟩ := hR {1, 2, 4, 5} (by decide)
    obtain ⟨fB, hB⟩ := hR {1, 3, 4, 6} (by decide)
    obtain ⟨fC, hC⟩ := hR {2, 3, 5, 6} (by decide)
    obtain ⟨fD, hD⟩ := hR {0, 2, 3} (by decide)
    by_cases hgen :
        (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
          Minimality.EdgeTieR (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
            (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) ∨
          Minimality.EdgeFarP (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
            (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4)) ∧
        (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
          Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
            (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
          Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
            (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) ∧
        (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 →
          ¬ Minimality.SpecTriple (x 1) (x 4) (x 2) (x 3))
    · exact not_type10_of_isNopert_sv x hN hx fA fB fC fD hA hB hC hD hgen.1 hgen.2.1 hgen.2.2
    · sorry -- type 10 in special position (paper: §23 (ii), §24; codimension 3 left)
  · exact big {0, 2, 3, 4, 6} (by decide) (by decide) (by decide)   -- type 11
  · sorry  -- type 12: `not_type12_of_isNopert_sv`
  · sorry  -- type 13: `not_type13_of_isNopert_sv`
  · sorry  -- type 14: `not_two_quad_facets_vertex_of_isNopert`
  · exact big {0, 1, 4, 5, 6} (by decide) (by decide) (by decide)   -- type 15
  · sorry  -- type 16: `not_type16_of_isNopert_codim2`
  · sorry  -- type 17: `not_type17_of_isNopert_sv`
  · sorry  -- type 18: `not_two_quad_facets_vertex_of_isNopert` (case (c) open)
  · sorry  -- type 19: `not_type19_of_isNopert_sv`
  · sorry  -- type 20: `not_two_quad_facets_vertex_of_isNopert` (case (c) open)
  · sorry  -- type 21: `not_type21_of_isNopert_codim2`
  · sorry  -- type 22: `not_type22_of_isNopert_sv`
  · sorry  -- type 23: `not_type23_of_isNopert_sv`
  · sorry  -- type 24: open (`not_type24_outside_Cbar_of_isNopert` outside C̄)
  · sorry  -- type 25: `not_type25_of_isNopert`
  · sorry  -- type 26: `not_type26_of_isNopert`
  · sorry  -- type 27: `not_type27_of_isNopert_sv`
  · sorry  -- type 28: `not_type28_of_isNopert_sv`
  · sorry  -- type 29: open (classes K3, K4: `isRupert_type29_K3`, `isRupert_type29_K4`)

end
