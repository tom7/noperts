module

public import Nopert
public import Minimality.SixClass
public import Minimality.Planar
public import Minimality.FaceFive
public import Minimality.QuadFacets
public import Minimality.TriBridge
public import Minimality.TriFacetsEdge
public import Minimality.Type19
public import Minimality.Type13
public import Minimality.Type17
public import Minimality.Type27
public import Minimality.Type23
public import Minimality.Type25
public import Minimality.Type26
public import Minimality.Type12
public import Minimality.Type22
public import Minimality.Type28
public import Minimality.Type05
public import Minimality.Type08
public import Minimality.Type08Flat
public import Minimality.Type29
public import Minimality.Type16M
public import Minimality.OctAxis
public import Minimality.EdgePair
public import Minimality.Type21
public import Minimality.Forces
public import Minimality.TieForces
public import Minimality.TieRobust
public import Minimality.TieFrame
public import Minimality.TieRight
public import Minimality.Transversal
public import Minimality.Parity
public import Minimality.Chords
public import Minimality.EdgeChords
public import Minimality.UniformTilt
public import Minimality.UnimodalCert
public import Minimality.DepthSeparated
public import Minimality.ExtremeRays
public import Minimality.Global
public import Minimality.Shear
public import Minimality.ParallelFar
public import Minimality.ParallelFacets
public import Minimality.Type24
public import Minimality.Type24Corner
public import Minimality.Type24WP
public import Minimality.Type24Chain
public import Minimality.Type24Lambda
public import Minimality.Type24Circle236
public import Minimality.Type24Circle
public import Minimality.Type21Entry
public import Minimality.Type21Facets
public import Minimality.Type21Limit
public import Minimality.Type16Main
public import Minimality.LimitCert
public import Minimality.RobustEdge
public import Minimality.Type16Limit
public import Minimality.Type21Sector
public import Minimality.Type29Facets

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

All results depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
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
given general position at the line of their planes: `Minimality.TriGenTieR` (no
segment parallel to it, and the two far vertices at different depths along it,
or their tie settled by a top or bottom vertex, or, at the tie, the shared vertex
off the tied depth and no right angle at the far vertices: Lemma T at the tie,
robust form, codimension 2; weaker than `Minimality.TriGenFar`), or
`Minimality.TriGenFarP` (segments parallel to it allowed, the far vertices at
different depths, one far end a single vertex). A parallel segment fails both
only together with a far tie (codimension 3). -/
theorem not_two_quad_facets_vertex_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hV : V.card = 7) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenTieR V Q1 Q2 v ∨ Minimality.TriGenFarP V Q1 Q2 v) : False := by
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
  · exact h.2 (Minimality.isRupert_of_facets_vertex_tieR V hgen Q1 Q2 h1V h2V h1f h2f v hint
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hT hin hsol)
  · exact h.2 (Minimality.isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hT hin)

/-- **Lemma T at a vertex** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets meeting in a single vertex `v`, with general
position at the line of their planes (`Minimality.TriGenTieR`: no segment
parallel to it, distinct depths along it at the two far ends, or a tie settled
by a top or bottom vertex or by the robust form; weaker than
`Minimality.TriGenFar`; or `Minimality.TriGenFarP`: parallel segments allowed,
distinct far depths, one far end a single vertex), never have every
other point strictly inside the shadow triangle of `v` and two further points
`xa`, `xb` of the facets. The interior condition is barycentric, stated with any
facet functionals `f1`, `f2` (it does not depend on their scaling). -/
theorem not_facets_vertex_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1c : 1 < Q1.card) (h2c : 1 < Q2.card) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenTieR V Q1 Q2 v ∨ Minimality.TriGenFarP V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  rcases hT with hT | hT
  · exact h.2 (Minimality.isRupert_of_facets_vertex_tieR V hgen Q1 Q2 h1V h2V h1f h2f v hint
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

/-- Seven labelled points of a nopert: no three are collinear (else the middle
one is in the hull of the other six, which is Rupert). -/
theorem noThreeCollinear_seven (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) : Minimality.NoThreeCollinear (Finset.univ.image x) :=
  Minimality.noThreeCollinear_of_not_isRupert (by rw [Finset.card_image_of_injective _ hx]; simp)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1) h.2

/-- **Type 10, the capped frustum** (Theorem E of `FEWER-FACES-PROOFS.md` §7): a
nopert does not have seven points labelled so that `1245`, `1346`, `2356` (side
quadrilaterals) and `023` (a cap triangle) are facets (given by functionals
negative off them); general position here is `Minimality.EdgeTieR` along `14` (no
other segment parallel to it; at the far ends distinct depths, a settled tie, or no right angle)
and `Minimality.TriGenTri` at the line of the planes of `023` and `1245`, with
`Minimality.TriGenFar` there only in the special position where the deciding
number is 1 (Lemma T′). -/
theorem not_type10_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hZ1 : Minimality.EdgeTieR (Finset.univ.image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))
    (hT2 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
        Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) ∧
      (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
          (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2))) : False :=
  h.2 (Minimality.isRupert_type10 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fC fD hA hB hC hD hZ1 hT2)

/-- **Type 19** (Theorem F of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0235`, `1356` (quadrilaterals), `046` and `346`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeTie` along `35` (no other segment parallel to it; at the far
ends distinct depths or a settled tie) and `Minimality.TriGenTri` at the line of
the planes of `0235` and `046`, with `Minimality.TriGenFar` there only in the
special position where the deciding number is 1 (Lemma T′). -/
theorem not_type19_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : Minimality.EdgeTieR (Finset.univ.image x)
      (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x)
      (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) ∧
      (fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
          (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))) : False :=
  h.2 (Minimality.isRupert_type19 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 13** (Theorem G of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0145`, `2456` (quadrilaterals), `123` and `126`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeTie` along `45` (no other segment parallel to it; at the far
ends distinct depths or a settled tie) and `Minimality.TriGenTri` at the line of
the planes of `0145` and `123`, with `Minimality.TriGenFar` there only in the
special position where the deciding number is 1 (Lemma T′). -/
theorem not_type13_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : Minimality.EdgeTieR (Finset.univ.image x)
      (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x)
      (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))
    (hT2 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1)) ∧
      (fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
          (({1, 2, 3} : Finset (Fin 7)).image x) (x 1))) : False :=
  h.2 (Minimality.isRupert_type13 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 17** (Theorem H of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246`, `2345` (quadrilaterals), `136` and `034`
are facets (given by functionals negative off them); general position here is
`Minimality.TriGenFar` at the lines of the planes of `136` and `2345` and of
`0246` and `136`. A view whose hypothesis is
`Minimality.TriGenTri` (it has a triangle face) allows the far ends to tie, unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type17_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fE : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hT1 : (Minimality.TriGenTri (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3)) ∧
      (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
          (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type17 x hx (noThreeCollinear_seven x h hx)
    fA fB fD fE hA hB hD hE hT1 hT2)

/-- **Type 27** (Theorem I of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `2356` (a quadrilateral), `025`, `016`, `046`,
`045`, `012` and `456` are facets (given by functionals negative off them);
general position here is `Minimality.EdgePar` along `25` (no other segment
parallel to it) and `Minimality.TriGenTri` at the lines of the planes of `016`
and `2356` and of `025` and `046`, with `Minimality.TriGenFar` at the latter
only in the special position `fG x2 / fG x5 = 1` (where Lemma T′ is used). At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenTri` (it has a triangle face) the far ends may tie unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type27_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fB fD fE fG fH fI fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hB : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) < 0))
    (hJ : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 2) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 2) (x 5))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) ∧
      (fG (x 2) / fG (x 5) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
          (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))) : False :=
  h.2 (Minimality.isRupert_type27 x hx (noThreeCollinear_seven x h hx)
    fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ hZ1 hT1 hT2)

/-- **Type 23** (Theorem J of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0345` (a quadrilateral), `014`, `125`, `156` and
`456` are facets (given by functionals negative off them); general position here
is `Minimality.EdgePar` along `04` (no other segment parallel to it),
`Minimality.TriGenTri` at the lines of the planes of `014` and `156` and of
`0345` and `125`, with `Minimality.TriGenFar` at the former only in the special
position `fA x6 / fA x1 + fD x6 / fD x5 = 1` (where Lemma T′ is used). At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenTri` (it has a triangle face) the far ends may tie unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type23_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fD fE fH fK : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
      (({0, 3, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT1 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1)) ∧
      (fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
          (({1, 5, 6} : Finset (Fin 7)).image x) (x 1)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5)) : False :=
  h.2 (Minimality.isRupert_type23 x hx (noThreeCollinear_seven x h hx)
    fA fD fE fH fK hA hD hE hH hK hZ1 hT1 hT2)

/-- **Type 25** (Theorem K of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246` (a quadrilateral), `013`, `136`, `056`,
`035`, `014` and `126` are facets (given by functionals negative off them);
general position here is `Minimality.EdgePar` along `13` (no other segment
parallel to it) and `Minimality.TriGenTri` at the lines of the planes of `013`
and `0246` and of `013` and `056`. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenTri` (it has a triangle face) the far ends may tie unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type25_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fD fF fG fH fE fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 5, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hI : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fI (x i) < 0))
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 1) (x 3) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 1) (x 3))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type25 x hx (noThreeCollinear_seven x h hx)
    fA fD fF fG fH fE fI hA hD hF hG hH hE hI hZ1 hT1 hT2)

/-- **Type 26** (Theorem L of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246` (a quadrilateral), `034`, `235`, `136`,
`013`, `016`, `245` and `345` are facets (given by functionals negative off
them); general position here is `Minimality.EdgePar` along `04` (no other
segment parallel to it) and `Minimality.TriGenTri` at the lines of the planes of
`0246` and `235` and of `0246` and `136`. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenTri` (it has a triangle face) the far ends may tie unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type26_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fT fG fH fU fW fY fZ : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hT : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hU : ∀ i, (i ∈ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) = 0) ∧
      (i ∉ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) < 0))
    (hW : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) < 0))
    (hY : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) < 0))
    (hZ : ∀ i, (i ∈ ({3, 4, 5} : Finset (Fin 7)) → fZ (x i) = 0) ∧
      (i ∉ ({3, 4, 5} : Finset (Fin 7)) → fZ (x i) < 0))
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({0, 3, 4} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2))
    (hT6 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type26 x hx (noThreeCollinear_seven x h hx)
    fA fT fG fH fU fW fY fZ hA hT hG hH hU hW hY hZ hZ1 hT2 hT6)

/-- **Type 12** (Theorem M of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0135`, `0346` (quadrilaterals), `024`, `236` and
`246` are facets (given by functionals negative off them); general position here
is `Minimality.TriGenFar` at the lines of the planes of `0135` and `024` and of
`024` and `236`. A view whose hypothesis is
`Minimality.TriGenTri` (it has a triangle face) allows the far ends to tie, unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type12_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fG fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hJ : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hT1 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0)) ∧
      (fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
          (({0, 2, 4} : Finset (Fin 7)).image x) (x 0)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
      (({2, 3, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
      (({2, 3, 6} : Finset (Fin 7)).image x) (x 2)) : False :=
  h.2 (Minimality.isRupert_type12 x hx (noThreeCollinear_seven x h hx)
    fA fB fD fG fJ hA hB hD hG hJ hT1 hT2)

/-- **Type 22** (Theorem N of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0134` (a quadrilateral), `125`, `246`, `146` and
`256` are facets (given by functionals negative off them); general position here
is `Minimality.TriGenFar` at the lines of the planes of `125` and `246` and of
`0134` and `246`. A view whose hypothesis is
`Minimality.TriGenTri` (it has a triangle face) allows the far ends to tie, unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type22_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fD fG fN fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hN : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) < 0))
    (hI : ∀ i, (i ∈ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) < 0))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) ∧
      (fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
          (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))) : False :=
  h.2 (Minimality.isRupert_type22 x hx (noThreeCollinear_seven x h hx)
    fA fD fG fN fI hA hD hG hN hI hT1 hT2)

/-- **Type 28** (Theorem O of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0245` (a quadrilateral), `036`, `146`, `023`,
`015` and `145` are facets (given by functionals negative off them); general
position here is `Minimality.TriGenFar` at the lines of the planes of `0245` and
`146` and of `0245` and `036`. A view whose hypothesis is
`Minimality.TriGenTri` (it has a triangle face) allows the far ends to tie, unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type28_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fD fG fH fF fM : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hM : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) < 0))
    (hT1 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4)) ∧
      (fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
          (({1, 4, 6} : Finset (Fin 7)).image x) (x 4)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({0, 3, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({0, 3, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type28 x hx (noThreeCollinear_seven x h hx)
    fA fD fG fH fF fM hA hD hG hH hF hM hT1 hT2)

/-- **Type 05** (Theorem B′ of `FEWER-FACES-PROOFS.md`, here by Lemma T): a nopert
does not have seven points labelled so that `0123`, `0145` (quadrilaterals),
`246`, `456` and `234` are facets (given by functionals negative off them);
general position here is `Minimality.TriGenFar` at the lines of the planes of
`0123` and `246` and of `0145` and `246`. A view whose hypothesis is
`Minimality.TriGenTri` (it has a triangle face) allows the far ends to tie, unless
they also tie with the shared vertex (Lemma T at the tie). -/
theorem not_type05_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fG fK fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) < 0))
    (hT1 : (Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2)) ∧
      (fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
          (({2, 4, 6} : Finset (Fin 7)).image x) (x 2)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) : False :=
  h.2 (Minimality.isRupert_type05_facets x hx (noThreeCollinear_seven x h hx)
    fA fB fG fK fH hA hB hG hK hH hT1 hT2)

/-- **Type 08** (Theorem J of `FEWER-FACES-PROOFS.md` §10, via the octahedron
`K − 2`): a nopert does not have seven points labelled so that `0123`, `0245`,
`2356` (quadrilaterals), `014`, `136`, `146` and `456` are facets (given by
functionals negative off them); then `x 2` caps the octahedron of the other six
(opposite pairs `(0, 6)`, `(3, 4)`, `(5, 1)`).  General position here: that
octahedron has no planar equator (no four of `1, 3, 4, 5`, of `0, 1, 5, 6`, of
`0, 3, 4, 6` coplanar), `Minimality.GenPos` (no two segments parallel or
orthogonal), `Minimality.NoPlaneParallel` (no plane through three of the points
parallel to the segment of two others), and `Minimality.NoHDNAt` (no horizontal
double normal at the view along any segment, the exclusion of Theorem J). -/
theorem not_type08_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (heq₁ : Minimality.det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) ≠ 0)
    (heq₂ : Minimality.det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) ≠ 0)
    (heq₃ : Minimality.det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) ≠ 0)
    (hgen : Minimality.GenPos (Finset.univ.image x))
    (hpar : Minimality.NoPlaneParallel (Finset.univ.image x))
    (hnd : ∀ v ∈ Finset.univ.image x, ∀ w ∈ Finset.univ.image x, v ≠ w →
      Minimality.NoHDNAt ((Finset.univ.image x).erase w) (w - v)) : False :=
  h.2 (Minimality.isRupert_type08_facets x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
    heq₁ heq₂ heq₃ hgen hpar hnd)

/-- **Type 08, codimension 2** (Theorem 10.1′ of `FEWER-FACES-PROOFS.md` §10 addendum,
Lemmas C, H, K, X in Lean form): as `not_type08_of_isNopert`, without general position
and without excluding horizontal double normals at the edge views.  The octahedron
`x 0, …, x 6` without `x 2` (pairs `(0, 6)`, `(3, 4)`, `(5, 1)`) may have one planar
equator, and `Minimality.Type08GenAll` holds: in each of the six labellings `(a, b, c)` of
its pairs, not both far-end ties at the view along `x 2 b`, at each tie the generic
conditions of Lemma X (`Minimality.RouteT`, `RouteT'`; which route applies is derived), no
touching (a triple or, at a planar equator, a quadruple depth tie at a named view;
codimension 2), and along the face circles of the named crossings (or, for the closings
with one circle, the five-corner rim along the other face, Lemma H: strictly unimodal or
with a depth-separated pair, `Minimality.UniOrSep`) depth ties and horizontal double
normals occur only at isolated views (`Minimality.NoBadNormal`); for the closings `K_c`
(N2) and `K_b` (T4) the two-peaked five-corner rim of `R_d` (`Minimality.RdCond`, Lemma R0
and Theorem R of A.10) is a further alternative, and for `K_d` (T4), whose `R_d` is empty,
on its type-(d) surface only the absence of ties is asked. -/
theorem not_type08_of_isNopert' (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hflat : ¬ (Minimality.det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) = 0 ∧
        Minimality.det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) = 0) ∧
      ¬ (Minimality.det3 (x 5 - x 3) (x 4 - x 3) (x 1 - x 3) = 0 ∧
        Minimality.det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) = 0) ∧
      ¬ (Minimality.det3 (x 5 - x 0) (x 6 - x 0) (x 1 - x 0) = 0 ∧
        Minimality.det3 (x 3 - x 0) (x 6 - x 0) (x 4 - x 0) = 0))
    (hgen : Minimality.Type08GenAll (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2)) : False :=
  h.2 (Minimality.isRupert_type08_flat_facets x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
    hflat hgen)

/-- **Type 24 outside `C̄ ∪ Σ_B`** (Corollary 15.8 of `FEWER-FACES-PROOFS.md` §15): a nopert
does not have seven points labelled so that `012`, `016`, `126` (the cap at `1`) and `236`,
`046`, `025` (the side faces) are facets (given by functionals negative off them), unless
it lies in `C̄ = {ω3, ω4, ω5 > 0, Δ ≥ 0}` or in `Σ_B`.  The coefficients
`ω3 = Minimality.omega3 x`, `ω4`, `ω5` of the side faces and `Δ = Minimality.Delta24 x` are
read off the oblique coordinates at `1` (frame `x 0 − x 1`, `x 2 − x 1`, `x 6 − x 1`).  Outside
`C̄` either some `ω ≤ 0` or some product `ω_g ω_h < 1` (region W: Rupert with no exclusion,
the window triangle), or `Minimality.RegionB24 x` holds; there the hypothesis is that one of
the three side crossings is available and free (`Minimality.S6Free`, `S2Free`, `S0Free`:
product `> 1`, distinct depths of `0, 2, 6` at its view, no horizontal double normal of
their triangle there). -/
theorem not_type24_outside_Cbar_of_isNopert (x : Fin 7 → ℝ³)
    (h : IsNopert (Finset.univ.image x))
    (fA fB fC fD fE fF : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hCbar : ¬ (0 < Minimality.omega3 x ∧ 0 < Minimality.omega4 x ∧ 0 < Minimality.omega5 x ∧
      0 ≤ Minimality.Delta24 x))
    (hSigma : Minimality.RegionB24 x →
      Minimality.S6Free x ∨ Minimality.S2Free x ∨ Minimality.S0Free x) : False :=
  h.2 (Minimality.isRupert_type24_outside_Cbar
    (Minimality.Type24.ofAffine x fA fB fC fD fE fF hA hB hC hD hE hF) hCbar hSigma)

/-- **Type 21** (Theorem 16.26 of `FEWER-FACES-PROOFS.md` §16, the tier cover): a nopert does
not have seven points labelled so that `014`, `015`, `0256`, `046`, `134`, `135`, `2346`, `235`
are facets (given by functionals negative off them), off the special positions:
`Minimality.NoPlaneParallel` (no plane through three of the points parallel to the segment of
two others; this contains every tie of a Gale comparison used), `Minimality.GenPosTie` (no two
segments parallel, and at the view along each segment at most one pair of points at equal depth:
both of codimension 2; depth ties at the edge views are allowed through Lemma E with ties, the
robust quad lift of tiers Q/H, planar and triangle closings, and the robust pentagon of `Y`), no
horizontal double normal at the view along any segment, the five planar equators
`{4, 5, 1, 6}`, `{0, 3, 1, 6}`, `{0, 3, 4, 5}`, `{0, 3, 1, 2}`, `{4, 5, 1, 2}` of `K − 2` and
`K − 6` (`hEq`), at the four vertex crossings `0: 014/0256`, `4: 014/2346`, `5: 135/0256`,
`3: 135/2346` the special positions of the test `T1` (`Minimality.T1View`: the antipode off the
far side, no depth ties on its rim other than those allowed by Theorem 18.3 (`Minimality.QuadTie`:
no three equal depths, no level rim edge inside a monotone run), no horizontal double normal),
in the four labellings those of the two vertex tests of F2 (`Minimality.F2Views`, with the same
ties allowed).  Every type-21 shape has one of the tiers Q, H, R,
F1, F2 (Theorem 16.13 for the cap-face class, Theorems 16.18, 16.20, 16.23 with Lemma 16.24 for
the normal form `(+, −, +)` reached by `σ1`, `σ2` and the reflection of the Gale diagram), or
lies on the switch surface `δ_014(2) = δ_014(5)` and has the certificate of Theorem 16.30 at the
edge `25` (Lemma E with ties and the uniform tilt of Lemma 16.27; three far corners at one
depth there are in `GenPosTie`, its horizontal double normals in the edge-view exclusion). -/
theorem not_type21_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hpp : Minimality.NoPlaneParallel (Finset.univ.image x))
    (hgen : Minimality.GenPosTie (Finset.univ.image x))
    (hnd : ∀ v ∈ Finset.univ.image x, ∀ w ∈ Finset.univ.image x, v ≠ w →
      Minimality.NoHDNAt ((Finset.univ.image x).erase w) (w - v))
    (hEq : Minimality.det3 (x 5 - x 4) (x 1 - x 4) (x 6 - x 4) ≠ 0 ∧
      Minimality.det3 (x 3 - x 0) (x 1 - x 0) (x 6 - x 0) ≠ 0 ∧
      Minimality.det3 (x 3 - x 0) (x 4 - x 0) (x 5 - x 0) ≠ 0 ∧
      Minimality.det3 (x 0 - x 3) (x 1 - x 3) (x 2 - x 3) ≠ 0 ∧
      Minimality.det3 (x 4 - x 5) (x 1 - x 5) (x 2 - x 5) ≠ 0)
    (hT1 : Minimality.T1View (Finset.univ.image x) fA fC (x 0) (x 3) (x 4) (x 5) ∧
      Minimality.T1View (Finset.univ.image x) fA fG (x 4) (x 5) (x 0) (x 3) ∧
      Minimality.T1View (Finset.univ.image x) fF fC (x 5) (x 4) (x 3) (x 0) ∧
      Minimality.T1View (Finset.univ.image x) fF fG (x 3) (x 0) (x 5) (x 4))
    (hF2 : Minimality.F2Views (Finset.univ.image x) (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) (x 2) ∧
      Minimality.F2Views (Finset.univ.image x) (x 4) (x 5) (x 0) (x 3) (x 1) (x 6) (x 2) ∧
      Minimality.F2Views (Finset.univ.image x) (x 5) (x 4) (x 3) (x 0) (x 1) (x 2) (x 6) ∧
      Minimality.F2Views (Finset.univ.image x) (x 3) (x 0) (x 5) (x 4) (x 1) (x 2) (x 6)) :
    False :=
  h.2 (Minimality.isRupert_type21_facets x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
    hpp hgen hnd hEq hT1 hF2)

/-- **Type 21 outside codimension 2, except horizontal double normals at its one-circle views**
(§18.6 step 2 and §22.2 of `FEWER-FACES-PROOFS.md`): a nopert does not have seven points labelled
so that `014`, `015`, `0256`, `046`, `134`, `135`, `2346`, `235` are facets (given by functionals
negative off them), unless one of the following holds.
* A horizontal double normal of a closing at the view along a segment other than the six edges
  `01`, `04`, `14`, `15`, `13`, `35` between two triangles (`hnd`), or along the line of one of the
  facet pairs `014/0256`, `014/2346`, `135/0256`, `135/2346` (`Minimality.NoHDNAff`): views with a
  quadrilateral face, whose closings may be realized on one face circle only (§22.3–22.10, not
  formalized).
* A horizontal double normal at the view along one of the six two-triangle edges, or along the
  line of `046/134`, `046/015`, `235/134`, `235/015`, together with a failure of (G1) there
  (`Minimality.HDNOrG1Edge`, `Minimality.HDNOrG1Aff`: `Minimality.G1Edge`, `Minimality.G1Vtx`, a
  second pair of points over one point, or a point over a support line off the two triangles):
  codimension 2.  Every closing at two triangles is realized on both face circles, so
  Proposition 22.2 (`Minimality.isRupert_of_tiltHides`) tilts it to a generic unimodal view.
* Two ties at the named views that are not one equation (`Minimality.OneTie21` fails):
  codimension 2.
No general position, no sign condition or Gale equality of the tier cover, no planar equator, no
switch surface.  Every type-21 shape is a limit of shapes off the special positions of the cover
with the same tie; each of these has a rim certificate at a named view (Theorem 16.26), a
subsequence carries one labelled certificate, and it passes to the limit (Lemma 18.2: the rim only
loses corners; Theorems 18.1, 18.3, and Proposition 22.2 at the two-triangle views). -/
theorem not_type21_of_isNopert_codim2 (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hnd : ∀ i j : Fin 7, i ≠ j →
      ({i, j} : Finset (Fin 7)) ∉ ({{0, 1}, {0, 4}, {1, 4}, {1, 5}, {1, 3}, {3, 5}} :
        Finset (Finset (Fin 7))) →
      Minimality.NoHDNAt ((Finset.univ.image x).erase (x j)) (x j - x i))
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hV : Minimality.NoHDNAff (Finset.univ.image x) fA fC ∧
      Minimality.NoHDNAff (Finset.univ.image x) fA fG ∧
      Minimality.NoHDNAff (Finset.univ.image x) fF fC ∧
      Minimality.NoHDNAff (Finset.univ.image x) fF fG ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : Minimality.OneTie21 x) : False :=
  h.2 (Minimality.isRupert_type21_limit_facets_sec x hx fA fB fC fD fE fF fG fH hA hB hC hD hE
    hF hG hH hnd hEd hV htie)

/-- **Type 16** (Theorem 19.6 of `FEWER-FACES-PROOFS.md` §19, the cover): a nopert does not
have seven points labelled so that `0235`, `1356` (quadrilaterals), `024`, `036`, `046`, `145`,
`146`, `245` are facets (given by functionals negative off them), off the special positions:
`Minimality.GenPosTie` (no two segments parallel, at most one tie at the view along each
segment: codimension 2; every edge-view test allows single ties: Lemma E with ties in the cover
of Theorem 19.2 and Proposition 14.3, robust rims in Lemmas 19.3–19.5),
`Minimality.NoPlaneParallel` (no plane through three of the points parallel
to the segment of two others; this contains the equalities in the sign conditions of the
route), no horizontal double normal at the view along any segment, the coplanarities of
`0, 1, 3, 4` and of `2, 3, 4, 6`, the lines `036 ∩ 146` and `036 ∩ 024` not parallel to the
planes `245`, `145` (`Minimality.LineAff16`), and at the six vertex views `046/145`, `036/146`,
`0235/046`, `046/245`, `036/024`, `1356/046` at most one depth tie and no horizontal double
normal (`Minimality.ViewAff16`).  Off `R1 ∪ R2` the pair at `06` certifies it (Proposition 14.3); in
`R1` a Lemma E edge pair or a triangle or planar closing (Theorem 19.2), or on its residual `Ω`
the pairs of Lemmas 19.3 and 19.4 or the triple of Lemma 19.5; in `R2` the same after
`σ = (06)(12)`. -/
theorem not_type16_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hgen : Minimality.GenPosTie (Finset.univ.image x))
    (hpp : Minimality.NoPlaneParallel (Finset.univ.image x))
    (hnd : ∀ v ∈ Finset.univ.image x, ∀ w ∈ Finset.univ.image x, v ≠ w →
      Minimality.NoHDNAt ((Finset.univ.image x).erase w) (w - v))
    (hcop : Minimality.det3 (x 0 - x 3) (x 1 - x 3) (x 4 - x 3) ≠ 0 ∧
      Minimality.det3 (x 2 - x 3) (x 4 - x 3) (x 6 - x 3) ≠ 0)
    (hL : Minimality.LineAff16 fD fG (x 2) (x 4) (x 5) ∧
      Minimality.LineAff16 fD fC (x 1) (x 4) (x 5))
    (hV : Minimality.ViewAff16 (Finset.univ.image x) fE fF ∧
      Minimality.ViewAff16 (Finset.univ.image x) fD fG ∧
      Minimality.ViewAff16 (Finset.univ.image x) fA fE ∧
      Minimality.ViewAff16 (Finset.univ.image x) fE fH ∧
      Minimality.ViewAff16 (Finset.univ.image x) fD fC ∧
      Minimality.ViewAff16 (Finset.univ.image x) fB fE) : False :=
  h.2 (Minimality.isRupert_type16_facets x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
    hgen hpp hnd hcop.1 hcop.2 hL hV)

/-- **Type 16 outside codimension 2, except horizontal double normals at its one-circle views**
(Theorem 19.8 with §18.6 step 2 and §22.2 of `FEWER-FACES-PROOFS.md`): a nopert does not have
seven points labelled so that `0235`, `1356` (quadrilaterals), `024`, `036`, `046`, `145`,
`146`, `245` are facets (given by functionals negative off them), unless one of the following
holds.
* A horizontal double normal of a closing at the view along a segment other than the six edges
  `04`, `06`, `14`, `24`, `45`, `46` between two triangles (`hnd`), or along the line of
  `0235/046` or `1356/046` (`Minimality.NoHDNAff`): views with a quadrilateral face, whose
  closings may be realized on one face circle only (§22.3–22.10, not formalized).
* A horizontal double normal at the view along one of the six two-triangle edges, or along the
  line of `046/145`, `036/146`, `046/245`, `036/024`, together with a failure of (G1) there
  (`Minimality.HDNOrG1Edge`, `Minimality.HDNOrG1Aff`: `Minimality.G1Edge`, `Minimality.G1Vtx`, a
  second pair of points over one point, or a point over a support line off the two triangles):
  codimension 2.  Every closing at two triangles is realized on both face circles, so
  Proposition 22.2 (`Minimality.isRupert_of_tiltHides`) tilts it to a generic unimodal view.
* Two ties at the named views that are not one equation (`Minimality.OneTie16` fails; the tie of
  `s, t` along `ij` and the tie of `i, j` along `st` count once): codimension 2.
No general position, no sign condition of the route, no (G1) elsewhere.  Every type-16 shape is a
limit of shapes off the special positions of the cover with the same tie; each of these has a rim
certificate at a named view (Theorem 19.6), a subsequence carries one labelled certificate, and it
passes to the limit (Lemma 18.2: the rim only loses corners; Theorems 18.1, 18.3, and
Proposition 22.2 at the two-triangle views). -/
theorem not_type16_of_isNopert_codim2 (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hnd : ∀ i j : Fin 7, i ≠ j →
      ({i, j} : Finset (Fin 7)) ∉ ({{0, 4}, {0, 6}, {1, 4}, {2, 4}, {4, 5}, {4, 6}} :
        Finset (Finset (Fin 7))) →
      Minimality.NoHDNAt ((Finset.univ.image x).erase (x j)) (x j - x i))
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 4) (x 2) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 2) (x 4) (x 0) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 4) (x 5) (x 1) (x 2) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 4) (x 6) (x 0) (x 1))
    (hV : Minimality.HDNOrG1Aff (Finset.univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      Minimality.NoHDNAff (Finset.univ.image x) fA fE ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      Minimality.NoHDNAff (Finset.univ.image x) fB fE)
    (htie : Minimality.OneTie16 x) : False :=
  h.2 (Minimality.isRupert_type16_limit_facets_sec x hx fA fB fC fD fE fF fG fH hA hB hC hD hE
    hF hG hH hnd hEd hV htie)

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

end
