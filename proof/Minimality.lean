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
given general position at the line of their planes (`Minimality.TriGenFar`: no
segment parallel to it, distinct depths along it at the two far vertices). -/
theorem not_two_quad_facets_vertex_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hV : V.card = 7) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenFar V Q1 Q2 v) : False :=
  have hsol := (not_coplanar_iff_interior_convexHull_nonempty _).mp h.1
  h.2 (Minimality.isRupert_of_two_quad_facets_vertex_solid V hV hsol
    (Minimality.noThreeCollinear_of_not_isRupert hV hsol h.2) Q1 Q2 h1V h2V h1c h2c h1f h2f v
    hint hT)

/-- **Lemma T at a vertex** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets meeting in a single vertex `v`, with general
position at the line of their planes (`Minimality.TriGenFar`: no segment
parallel to it, distinct depths along it at the two far ends), never have every
other point strictly inside the shadow triangle of `v` and two further points
`xa`, `xb` of the facets. The interior condition is barycentric, stated with any
facet functionals `f1`, `f2` (it does not depend on their scaling). -/
theorem not_facets_vertex_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1c : 1 < Q1.card) (h2c : 1 < Q2.card) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGenFar V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False :=
  h.2 (Minimality.isRupert_of_facets_vertex V hgen Q1 Q2 h1V h2V h1f h2f v hint
    (Finset.exists_mem_ne h1c v) (Finset.exists_mem_ne h2c v) hT hin)

/-- **Lemma T over an edge** (`FEWER-FACES-PROOFS.md` §7): in a nopert with no three
points collinear, two facets sharing exactly the edge `v w`, with general
position along it (`Minimality.EdgeFar`: no other segment parallel to it,
distinct depths along it at the two far ends), never have every
other point strictly inside the shadow triangle of the edge and two further
points `xa ∈ Q1 \ Q2`, `xb ∈ Q2 \ Q1` (barycentric form with any facet
functionals `f1`, `f2`). -/
theorem not_facets_edge_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.NoThreeCollinear V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1f : Minimality.IsFacet V Q1) (h2f : Minimality.IsFacet V Q2) (v w : ℝ³) (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w})
    (hZ : Minimality.EdgeFar V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  exact h.2 (Minimality.isRupert_of_facets_edge V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
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
negative off them); general position here is `Minimality.EdgeFar` along `14` and
`Minimality.TriGenFar` at the line of the planes of `023` and `1245`. -/
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
    (hZ1 : Minimality.EdgeFar (Finset.univ.image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))
    (hT2 : Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) : False :=
  h.2 (Minimality.isRupert_type10 x hx (noThreeCollinear_seven x h hx)
    fA fB fC fD hA hB hC hD hZ1 hT2)

/-- **Type 19** (Theorem F of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0235`, `1356` (quadrilaterals), `046` and `346`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeFar` along `35` and `Minimality.TriGenFar` at the line of the
planes of `0235` and `046`. -/
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
    (hZ1 : Minimality.EdgeFar (Finset.univ.image x)
      (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type19 x hx (noThreeCollinear_seven x h hx)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 13** (Theorem G of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0145`, `2456` (quadrilaterals), `123` and `126`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeFar` along `45` and `Minimality.TriGenFar` at the line of the
planes of `0145` and `123`. -/
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
    (hZ1 : Minimality.EdgeFar (Finset.univ.image x)
      (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))
    (hT2 : Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 3} : Finset (Fin 7)).image x) (x 1)) : False :=
  h.2 (Minimality.isRupert_type13 x hx (noThreeCollinear_seven x h hx)
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
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∧
      (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
          (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 2) (x 5))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∧
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) ∧
      (fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
          (({1, 5, 6} : Finset (Fin 7)).image x) (x 1)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 1) (x 3))
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2))
    (hT6 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
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
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0) ∧
      (fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
          (({0, 2, 4} : Finset (Fin 7)).image x) (x 0)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
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
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∧
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
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∧
      (fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
          (({1, 4, 6} : Finset (Fin 7)).image x) (x 4)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
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
    (hT1 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∧
      (fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
          (({2, 4, 6} : Finset (Fin 7)).image x) (x 2)))
    (hT2 : Minimality.TriGenTri (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) : False :=
  h.2 (Minimality.isRupert_type05_facets x hx (noThreeCollinear_seven x h hx)
    fA fB fG fK fH hA hB hG hK hH hT1 hT2)

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
