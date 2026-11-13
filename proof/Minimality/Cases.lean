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
public import Minimality.Type16Metric
public import Minimality.Type21Metric
public import Minimality.Forces
public import Minimality.TieForces
public import Minimality.TieRobust
public import Minimality.TieFrame
public import Minimality.TripleTie
public import Minimality.TieRight
public import Minimality.Chords
public import Minimality.EdgeChords
public import Minimality.UniformTilt
public import Minimality.UnimodalCert
public import Minimality.DepthSeparated
public import Minimality.Global
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
public import Minimality.RobustEdge
public import Minimality.Type16Limit
public import Minimality.Type21Sector
public import Minimality.Type29Facets
public import Minimality.ParallelEdge
public import Minimality.Type16Edge2
public import Minimality.SameView
public import Minimality.Type21Ridge
public import Minimality.Type21Vtx
public import Minimality.SpecialTypes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The non-simplicial 7-vertex types, case by case

One theorem per combinatorial type (gallery labels of `FEWER-FACES.md` §4; face lists in
`Minimality/SevenTypes.lean`): a nopert does not have seven points labelled `x 0, …, x 6`
realizing the type's faces, under the general-position hypotheses stated with each theorem.
The `_sv` versions settle the special value of Lemma T′ and ask the least. Types 02, 07, 09,
14, 18, 20 are covered by `not_two_quad_facets_vertex_of_isNopert` and types 01, 03, 04, 06,
11, 15 by `facet_card_le_four_of_isNopert` (both in `Minimality.lean`). Types 08, 16, 21
are proved outside codimension 2; types 24 and 29 are open (partial results:
`not_type24_outside_Cbar_of_isNopert`; type 29's classes K3, K4 in `Minimality/Type29.lean`).
`Minimality.lean` combines them in `anySevenVertexNopertIsSimplicial`.
-/

@[expose] public section

/-- Seven labelled points of a nopert: no three are collinear (else the middle
one is in the hull of the other six, which is Rupert). -/
theorem noThreeCollinear_seven (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) : Minimality.NoThreeCollinear (Finset.univ.image x) :=
  Minimality.noThreeCollinear_of_not_isRupert (by rw [Finset.card_image_of_injective _ hx]; simp)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1) h.2

/-- **Type 25** (Theorem K of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246` (a quadrilateral), `013`, `136`, `056`,
`035`, `014` and `126` are facets (given by functionals negative off them);
general position here is `Minimality.EdgePar` along `13` (no other segment
parallel to it) and `Minimality.TriGenPar` at the lines of the planes of `013`
and `0246` and of `013` and `056`. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenPar` (it has a triangle face) any tie of the far ends is
allowed, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x) (({1, 3, 6} : Finset (Fin 7)).image x) (x 1) (x 3) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 1) (x 3))
    (hT1 : Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type25 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fD fF fG fH fE fI hA hD hF hG hH hE hI hZ1 hT1 hT2)

/-- **Type 26** (Theorem L of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246` (a quadrilateral), `034`, `235`, `136`,
`013`, `016`, `245` and `345` are facets (given by functionals negative off
them); general position here is `Minimality.EdgePar` along `04` (no other
segment parallel to it) and `Minimality.TriGenPar` at the lines of the planes of
`0246` and `235` and of `0246` and `136`. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenPar` (it has a triangle face) any tie of the far ends is
allowed, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x) (({0, 3, 4} : Finset (Fin 7)).image x) (x 0) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({0, 3, 4} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2))
    (hT6 : Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type26 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fT fG fH fU fW fY fZ hA hT hG hH hU hW hY hZ hZ1 hT2 hT6)

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

/-- **Type 21 outside codimension 2** (§18.6 step 2 and §22 of `FEWER-FACES-PROOFS.md`): a nopert
does not have seven points labelled so that `014`, `015`, `0256`, `046`, `134`, `135`, `2346`,
`235` are facets (given by functionals negative off them), unless one of the following holds.
* A horizontal double normal at the view along the line of one of the facet pairs `014/0256`,
  `014/2346`, `135/0256`, `135/2346` together with a failure of the codimension-2 conditions there
  (`Minimality.HDNOrVtx21Aff`: §22.4's conditions `Minimality.VtxGen` — no two points over one
  point, (G1), distinct depths, at most one direction of horizontal double normals, no double
  normal perpendicular to the quadrilateral from one of its vertices — and `2` off `013`, `2` off
  `145`, `6` off `145`, `6` off `013` respectively, the boundary of Lemma 22.13 in `V`'s
  labelling).  Each line carries F1's `T1` (realized on both face circles: Proposition 22.2)
  and F2's `V` (its triangle rim by a sector rim, Proposition 22.2; its quadrilateral rim by
  §22.3–22.10, with (H4) for the middle `3` from Lemma 22.13 and the residual of Lemma 22.9 for
  the middle `6` impossible by Lemma 22.14: there `V′` would not fail, and F2's certificates
  prefer `V′`).
* A horizontal double normal at the view along `06`, `46`, `25` or `23` together with a failure of
  the codimension-2 conditions of §22.4 there (`Minimality.QGenAff21`: only the axle seen
  end-on, (G1), distinct depths, at most one direction of horizontal double normals, no double
  normal perpendicular to a face from a face vertex, the axle off the two planes of Lemma E).
  The certificates there are those of tier Q with Lemma E (the dependency of the E-good edge),
  closed by §22.3–22.8 (`Minimality.isRupert_ePair_limit_facts`), and the planar closing of
  §9 Lemma 3 (c), realized on both face circles (Proposition 22.2).
* A horizontal double normal at the view along `05` or `34` together with a failure of the
  codimension-2 conditions there (`Minimality.Q5GenAff21`: as at `06`, with the axle off the two
  planes `164`, `123` of Lemma E at `05`).  The certificates are the edge pairs of tier Q in both
  cases of §9 Lemma 3: in case (a) Lemma E comes from the dependency of the E-good edge, in case
  (b) from the dependency of `K − 2` with `6` replaced by the cap (`Minimality.lemmaE_far21`, a
  direct form of Proposition 14.2); closed by §22.3–22.8.
* A horizontal double normal at the view along the ridge `26` together with a failure of the
  codimension-2 conditions there (`Minimality.R26GenAff21`: as at `06`, with the axle off the
  planes `013`, `514` of Lemma E).  Tier R's edge pairs are closed by §22.3–22.8; its triangle
  closings (`1` hidden) by Lemma 22.3 on the two face circles (`Minimality.isRupert_ridgeTri`:
  `K_6` and `K_2` are realized on different circles, or one of them on both, and the double
  normals that persist on the two circles have different directions).
* A horizontal double normal at the view along one of the six two-triangle edges `01`, `04`,
  `14`, `15`, `13`, `35`, or along the line of `046/134`, `046/015`, `235/134`, `235/015`, together
  with a failure of (G1) there (`Minimality.HDNOrG1Edge`, `Minimality.HDNOrG1Aff`:
  `Minimality.G1Edge`, `Minimality.G1Vtx`, a second pair of points over one point, or a point
  over a support line off the two triangles): codimension 2.  Every closing at two triangles is
  realized on both face circles, so Proposition 22.2 (`Minimality.isRupert_of_tiltHides`) tilts
  it to a generic unimodal view.
* Two ties at the named views that are not one equation (`Minimality.OneTie21` fails):
  codimension 2.
Nothing is asked at the eight non-edge segments `02`, `03`, `12`, `16`, `24`, `36`, `45`, `56`:
no certificate of the cover uses their views (`Minimality.Edge21`).  No general position, no sign
condition or Gale equality of the tier cover, no planar equator, no switch surface (a
`NoPlaneParallel` position of the approximants, `Minimality.IsCap21.not_switch`).  Every type-21
shape is a limit of shapes off the special positions of the cover with the same tie; each of
these has a rim certificate at a named view (Theorem 16.26), with the data of tiers Q and R at
the seven edges with a quadrilateral and of `T1`, `V` at the four vertex lines with a
quadrilateral; a subsequence carries one labelled certificate, and it passes to the limit
(Lemma 18.2: the rim only loses corners; Theorems 18.1, 18.3, Proposition 22.2 at the
two-circle views, §22.3–22.8 at the edges with a quadrilateral, and §22.2–22.14 at the vertex
lines with a quadrilateral).  No plain horizontal-double-normal hypothesis is left. -/
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
    (hQ : (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 0) ∨
        Minimality.QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 4) ∨
        Minimality.QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 5) ∨
        Minimality.QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 3) ∨
        Minimality.QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 0) ∨
        Minimality.Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 3 - x 4) ∨
        Minimality.Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 6) ∨
      Minimality.R26GenAff21 x fC fG)
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : Minimality.HDNOrVtx21Aff x fC fA {0, 2, 5, 6} {0, 1, 4} 0 1 3 2 ∧
      Minimality.HDNOrVtx21Aff x fG fA {2, 3, 4, 6} {0, 1, 4} 4 1 5 2 ∧
      Minimality.HDNOrVtx21Aff x fC fF {0, 2, 5, 6} {1, 3, 5} 5 1 4 6 ∧
      Minimality.HDNOrVtx21Aff x fG fF {2, 3, 4, 6} {1, 3, 5} 3 1 0 6)
    (hV : Minimality.HDNOrG1Aff (Finset.univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : Minimality.OneTie21 x) : False :=
  h.2 (Minimality.isRupert_type21_limit_facets_codim2 x hx fA fB fC fD fE fF fG fH hA hB hC hD
    hE hF hG hH hQ h5 h26 hEd hVq hV htie)

/-! ### The special value of Lemma T′ settled (types 05, 10, 12, 13, 17, 19, 22, 23, 27, 28)

Each of these types is decided by a number `s` (`FEWER-FACES-PROOFS.md` §7, Theorems E–O and
type 05). At `s = 1` three faces are edge-on in one view, and the statements above ask a
condition there that excludes a single tie (`EdgeFar` along the forced parallel edge for
05, 10, 13, 17, 19, 23, 27; `TriGenFar` for 12, 22, 28), on top of their general position at
the views that coincide there. The statements below ask their general position only off
`s = 1`, and nothing at `s = 1`: every tie, and any segment parallel to the view, is settled
by a reading of Lemma T′ at one of the three corners (`FEWER-FACES-PROOFS.md` Theorems 23.18
and 24.13) or, at the triple tie of the three corners, by the level triangle in the sector
tilts at the view (Proposition 26.8, Lemma 24.14 with Corollary 24.15;
`Minimality/SpecialValue.lean`, `Minimality/SpecialTriple.lean`). Types 17, 19, 28 take one
more facet (`036`, `026`, `016`), which shows that the tied corners do not span a face. They
imply the statements above. -/

/-- **Type 05, the special value settled**: as `not_type05_of_isNopert`, with
`Minimality.TriGenPar` (or `Minimality.TriGenFarP`) at the two views asked only where the
deciding number `fG x5 / fG x0 + fA x5 / fA x4` is not 1, and nothing asked where it is 1. -/
theorem not_type05_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hT1 : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) : False :=
  h.2 (Minimality.isRupert_type05_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fG fK fH hA hB hG hK hH hT1 hT2)

/-- **Type 10, the special value settled**: as `not_type10_of_isNopert`, its general position
asked only where `fB x0 / fB x2 + fA x0 / fA x3` is not 1, and nothing asked where it is 1. -/
theorem not_type10_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hZ1 : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
      Minimality.EdgeTieR (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))
    (hT2 : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) : False :=
  h.2 (Minimality.isRupert_type10_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fC fD hA hB hC hD hZ1 hT2)

/-- **Type 13, the special value settled**: as `not_type13_of_isNopert`, its general position
asked only where `fB x3 / fB x1 + fA x3 / fA x2` is not 1, and nothing asked where it is 1. -/
theorem not_type13_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hZ1 : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) ≠ 1 →
      Minimality.EdgeTieR (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))
    (hT2 : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1)) : False :=
  h.2 (Minimality.isRupert_type13_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 17, the special value settled**: as `not_type17_of_isNopert`, its general position
asked only where `fB x0 / fB x6 + fD x0 / fD x4` is not 1, and nothing asked where it is 1;
`036` is one more facet. -/
theorem not_type17_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fE fF : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hT1 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3))
    (hT2 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type17_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fD fE fF hA hB hD hE hF hT1 hT2)

/-- **Type 19, the special value settled**: as `not_type19_of_isNopert`, its general position
asked only where `fB x4 / fB x0 + fA x4 / fA x6` is not 1, and nothing asked where it is 1;
`026` is one more facet. -/
theorem not_type19_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fD fG fE : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 2, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 2, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hZ1 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      Minimality.EdgeTieR (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type19_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG fE hA hB hD hG hE hZ1 hT2)

/-- **Type 23, the special value settled**: as `not_type23_of_isNopert`, its general position
asked only where `fA x6 / fA x1 + fD x6 / fD x5` is not 1, and nothing asked where it is 1. -/
theorem not_type23_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hZ1 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      Minimality.EdgePar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 4) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({0, 3, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT1 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1))
    (hT2 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 5} : Finset (Fin 7)).image x) (x 5) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 5} : Finset (Fin 7)).image x) (x 5)) : False :=
  h.2 (Minimality.isRupert_type23_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fD fE fH fK hA hD hE hH hK hZ1 hT1 hT2)

/-- **Type 27, the special value settled**: as `not_type27_of_isNopert`, its general position
asked only where `fG x2 / fG x5` is not 1, and nothing asked where it is 1. -/
theorem not_type27_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hZ1 : fG (x 2) / fG (x 5) ≠ 1 →
      Minimality.EdgePar (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x) (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 2) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 2) (x 5))
    (hT1 : fG (x 2) / fG (x 5) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : fG (x 2) / fG (x 5) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type27_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ hZ1 hT1 hT2)

/-- **Type 12, the special value settled**: as `not_type12_of_isNopert`, its general position
asked only where `fD x6 / fD x3 + fA x6 / fA x2` is not 1, and nothing asked where it is 1. -/
theorem not_type12_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hT1 : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0))
    (hT2 : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
        (({2, 3, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
        (({2, 3, 6} : Finset (Fin 7)).image x) (x 2)) : False :=
  h.2 (Minimality.isRupert_type12_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fD fG fJ hA hB hD hG hJ hT1 hT2)

/-- **Type 22, the special value settled**: as `not_type22_of_isNopert`, its general position
asked only where `fG x5 / fG x1 + fA x5 / fA x2` is not 1, and nothing asked where it is 1. -/
theorem not_type22_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hT1 : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) : False :=
  h.2 (Minimality.isRupert_type22_sv x hx (noThreeCollinear_seven x h hx)
    fA fD fG fN fI hA hD hG hN hI hT1 hT2)

/-- **Type 28, the special value settled**: as `not_type28_of_isNopert`, its general position
asked only where `fG x3 / fG x0 + fA x3 / fA x6` is not 1, and nothing asked where it is 1;
`016` is one more facet. -/
theorem not_type28_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fD fG fH fF fM fE : ℝ³ →ᵃ[ℝ] ℝ)
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
    (hE : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hT1 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hT2 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type28_sv x hx (noThreeCollinear_seven x h hx)
    fA fD fG fH fF fM fE hA hD hG hH hF hM hE hT1 hT2)

end
