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
a 7-point nopert in general position has no two quadrilateral facets meeting in a
single vertex, given general position at the line of their planes
(`Minimality.TriGen`: no segment parallel to it, distinct depths along it). -/
theorem not_two_quad_facets_vertex_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hV : V.card = 7) (hgen : Minimality.GenPos V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGen V Q1 Q2 v) : False :=
  h.2 (Minimality.isRupert_of_two_quad_facets_vertex_solid V hV
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1) hgen Q1 Q2 h1V h2V h1c h2c h1f h2f
    v hint hT)

/-- **Lemma T at a vertex** (`FEWER-FACES-PROOFS.md` §7): in a nopert in general
position, two facets meeting in a single vertex `v`, with general position at
the line of their planes (`Minimality.TriGen`), never have every other point
strictly inside the shadow triangle of `v` and two further points `xa`, `xb` of
the facets.  The interior condition is barycentric, stated with any facet
functionals `f1`, `f2` (it does not depend on their scaling). -/
theorem not_facets_vertex_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.GenPos V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1c : 1 < Q1.card) (h2c : 1 < Q2.card) (h1f : Minimality.IsFacet V Q1)
    (h2f : Minimality.IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : Minimality.TriGen V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False :=
  h.2 (Minimality.isRupert_of_facets_vertex V hgen Q1 Q2 h1V h2V h1f h2f v hint
    (Finset.exists_mem_ne h1c v) (Finset.exists_mem_ne h2c v) hT hin)

/-- **Lemma T over an edge** (`FEWER-FACES-PROOFS.md` §7): in a nopert in
general position, two facets sharing exactly the edge `v w`, with distinct
depths along it, never have every other point strictly inside the shadow
triangle of the edge and two further points `xa ∈ Q1 \ Q2`, `xb ∈ Q2 \ Q1`
(barycentric form with any facet functionals `f1`, `f2`). -/
theorem not_facets_edge_triShadow_of_isNopert (V : Finset ℝ³) (h : IsNopert V)
    (hgen : Minimality.GenPos V) (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h1f : Minimality.IsFacet V Q1) (h2f : Minimality.IsFacet V Q2) (v w : ℝ³) (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w})
    (hZ : Set.InjOn (fun p : ℝ³ => inner ℝ p (w - v)) (V : Set ℝ³))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : False := by
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  exact h.2 (Minimality.isRupert_of_facets_edge V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint
    ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hZ ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩)

/-- **Type 10, the capped frustum** (Theorem E of `FEWER-FACES-PROOFS.md` §7):
a nopert in general position does not have seven points labelled so that
`1245`, `1346`, `2356` (side quadrilaterals) and `023` (a cap triangle) are
facets (given by functionals negative off them), unless `x0` lies over the
chord `23` in the view along `14`; general position includes distinct depths
along `14` and `Minimality.TriGen` at the line of the planes of `023` and
`1245`. -/
theorem not_type10_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
    (fA fB fC fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hs : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 4 - x 1)) (Finset.univ.image x : Set ℝ³))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) : False :=
  h.2 (Minimality.isRupert_type10 x hx hgen fA fB fC fD hA hB hC hD hs hZ1 hT2)

/-- **Type 19** (Theorem F of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `0235`, `1356`
(quadrilaterals), `046` and `346` are facets (given by functionals negative
off them), unless `x4` lies over the chord `06` in the view along `35`;
general position includes distinct depths along `35` and `Minimality.TriGen`
at the line of the planes of `0235` and `046`. -/
theorem not_type19_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hs : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 5 - x 3)) (Finset.univ.image x : Set ℝ³))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type19 x hx hgen fA fB fD fG hA hB hD hG hs hZ1 hT2)

/-- **Type 13** (Theorem G of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `0145`, `2456`
(quadrilaterals), `123` and `126` are facets (given by functionals negative
off them), unless `x3` lies over the chord `12` in the view along `45`;
general position includes distinct depths along `45` and `Minimality.TriGen`
at the line of the planes of `0145` and `123`. -/
theorem not_type13_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hs : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 5 - x 4)) (Finset.univ.image x : Set ℝ³))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 3} : Finset (Fin 7)).image x) (x 1)) : False :=
  h.2 (Minimality.isRupert_type13 x hx hgen fA fB fD fG hA hB hD hG hs hZ1 hT2)

/-- **Type 17** (Theorem H of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `0246`, `2345`
(quadrilaterals), `136` and `034` are facets (given by functionals negative
off them), unless `fB x0 / fB x6 + fD x0 / fD x4 = 1`; general position
includes `Minimality.TriGen` at the lines of the planes of `136` and `2345`
and of `0246` and `136`. -/
theorem not_type17_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
    (fA fB fD fE : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hs : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1)
    (hT1 : Minimality.TriGen (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type17 x hx hgen fA fB fD fE hA hB hD hE hs hT1 hT2)

/-- **Type 27** (Theorem I of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `2356` (a
quadrilateral), `025`, `016`, `046`, `045`, `012` and `456` are facets (given
by functionals negative off them), unless `fB x4 / fB x0 + fD x4 / fD x6 = 1`;
general position includes distinct depths along `25` and `Minimality.TriGen`
at the lines of the planes of `016` and `2356` and of `025` and `046`. -/
theorem not_type27_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
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
    (hs : fB (x 4) / fB (x 0) + fD (x 4) / fD (x 6) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 5 - x 2)) (Finset.univ.image x : Set ℝ³))
    (hT1 : Minimality.TriGen (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
      (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type27 x hx hgen fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ hs hZ1
    hT1 hT2)

/-- **Type 23** (Theorem J of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `0345` (a
quadrilateral), `014`, `125`, `156` and `456` are facets (given by functionals
negative off them), unless `fA x6 / fA x1 + fD x6 / fD x5 = 1`; general
position includes distinct depths along `04` and `Minimality.TriGen` at the
lines of the planes of `014` and `156` and of `0345` and `125`. -/
theorem not_type23_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
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
    (hs : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 4 - x 0)) (Finset.univ.image x : Set ℝ³))
    (hT1 : Minimality.TriGen (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
      (({1, 5, 6} : Finset (Fin 7)).image x) (x 1))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5)) : False :=
  h.2 (Minimality.isRupert_type23 x hx hgen fA fD fE fH fK hA hD hE hH hK hs hZ1 hT1 hT2)

/-- **Type 25** (Theorem K of `FEWER-FACES-PROOFS.md` §7): a nopert in general
position does not have seven points labelled so that `0246` (a
quadrilateral), `013`, `136`, `056`, `035`, `014` and `126` are facets (given by
functionals negative off them), unless `fF x5 / fF x0 + fD x5 / fD x6 = 1`;
general position includes distinct depths along `13` and `Minimality.TriGen`
at the lines of the planes of `013` and `0246` and of `013` and `056`. -/
theorem not_type25_of_isNopert (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hgen : Minimality.GenPos (Finset.univ.image x))
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
    (hs : fF (x 5) / fF (x 0) + fD (x 5) / fD (x 6) ≠ 1)
    (hZ1 : Set.InjOn (fun p : ℝ³ => inner ℝ p (x 3 - x 1)) (Finset.univ.image x : Set ℝ³))
    (hT1 : Minimality.TriGen (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hT2 : Minimality.TriGen (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type25 x hx hgen fA fD fF fG fH fE fI hA hD hF hG hH hE hI hs hZ1
    hT1 hT2)

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
