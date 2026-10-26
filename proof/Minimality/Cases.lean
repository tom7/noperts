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
public import Minimality.TripleTie
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
public import Minimality.ParallelEdge
public import Minimality.Type16Edge2
public import Minimality.SameView
public import Minimality.Type21Ridge
public import Minimality.Type21Vtx
public import Minimality.SpecialTypes

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

/-- **Type 10, the capped frustum** (Theorem E of `FEWER-FACES-PROOFS.md` §7): a
nopert does not have seven points labelled so that `1245`, `1346`, `2356` (side
quadrilaterals) and `023` (a cap triangle) are facets (given by functionals
negative off them); general position here is `Minimality.EdgeTieR` along `14` (no
other segment parallel to it; at the far ends distinct depths, a settled tie, or no right angle)
and `Minimality.TriGenPar` at the line of the planes of `023` and `1245`; where the
deciding number `fB x0 / fB x2 + fA x0 / fA x3` is 1, `Minimality.EdgeFar` along `14`. At the special value
the edge `14` is parallel to the line of that view (`Minimality.type10_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `14` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. -/
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
    (hT2 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
        Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) ∧
      (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
          (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))) : False :=
  h.2 (Minimality.isRupert_type10 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fC fD hA hB hC hD hZ1 hT2)

/-- **Type 19** (Theorem F of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0235`, `1356` (quadrilaterals), `046` and `346`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeTie` along `35` (no other segment parallel to it; at the far
ends distinct depths or a settled tie) and `Minimality.TriGenPar` at the line of
the planes of `0235` and `046`; where the deciding number `fB x4 / fB x0 + fA x4 / fA x6`
is 1, `Minimality.EdgeFar` along `35`. At the special value
the edge `35` is parallel to the line of that view (`Minimality.type19_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `35` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. -/
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
    (hT2 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) ∧
      (fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
          (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))) : False :=
  h.2 (Minimality.isRupert_type19 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 13** (Theorem G of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0145`, `2456` (quadrilaterals), `123` and `126`
are facets (given by functionals negative off them); general position here is
`Minimality.EdgeTie` along `45` (no other segment parallel to it; at the far
ends distinct depths or a settled tie) and `Minimality.TriGenPar` at the line of
the planes of `0145` and `123`; where the deciding number `fB x3 / fB x1 + fA x3 / fA x2`
is 1, `Minimality.EdgeFar` along `45`. At the special value
the edge `45` is parallel to the line of that view (`Minimality.type13_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `45` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. -/
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
    (hT2 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1)) ∧
      (fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
          (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))) : False :=
  h.2 (Minimality.isRupert_type13 x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2)

/-- **Type 17** (Theorem H of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0246`, `2345` (quadrilaterals), `136` and `034`
are facets (given by functionals negative off them); general position here is
`Minimality.TriGenPar` (or `Minimality.TriGenFarP`) at the lines of the planes of
`136` and `2345` and of `0246` and `136`, and where the deciding number
`fB x0 / fB x6 + fD x0 / fD x4` of the first is 1, `Minimality.EdgeFar` along `24`.
A view whose hypothesis is `Minimality.TriGenPar` (it has a triangle face) allows any tie of the
far ends, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). At the special value
the edge `24` is parallel to the line of the first view (`Minimality.type17_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `24` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. -/
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
    (hT1 : (Minimality.TriGenPar (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3)) ∧
      (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
          (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 2) (x 4)))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) : False :=
  h.2 (Minimality.isRupert_type17 x hx (noThreeCollinear_seven x h hx)
    fA fB fD fE hA hB hD hE hT1 hT2)

/-- **Type 27** (Theorem I of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `2356` (a quadrilateral), `025`, `016`, `046`,
`045`, `012` and `456` are facets (given by functionals negative off them);
general position here is `Minimality.EdgePar` along `25` (no other segment
parallel to it) and `Minimality.TriGenPar` at the lines of the planes of `016`
and `2356` and of `025` and `046`, and `Minimality.EdgeFar` along `25` where
`fG x2 / fG x5 = 1`. At the special value
the edge `25` is parallel to the line of the second view (`Minimality.type27_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `25` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenPar` (it has a triangle face) any tie of the far ends is
allowed, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hT1 : Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) ∧
      (fG (x 2) / fG (x 5) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
          (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 2) (x 5))) : False :=
  h.2 (Minimality.isRupert_type27 x hx (noThreeCollinear_seven x h hx)
    fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ hZ1 hT1 hT2)

/-- **Type 23** (Theorem J of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0345` (a quadrilateral), `014`, `125`, `156` and
`456` are facets (given by functionals negative off them); general position here
is `Minimality.EdgePar` along `04` (no other segment parallel to it),
`Minimality.TriGenPar` at the lines of the planes of `014` and `156` and of
`0345` and `125`, and `Minimality.EdgeFar` along `04` where
`fA x6 / fA x1 + fD x6 / fD x5 = 1`. At the special value
the edge `04` is parallel to the line of the first view (`Minimality.type23_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `04` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. At the edge view
a triangle face settles any tie of the far ends, and at a view whose hypothesis
is `Minimality.TriGenPar` (it has a triangle face) any tie of the far ends is
allowed, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hT1 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1)) ∧
      (fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
          (({0, 3, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 4)))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5)) : False :=
  h.2 (Minimality.isRupert_type23 x hx (noThreeCollinear_seven x h hx)
    fA fD fE fH fK hA hD hE hH hK hZ1 hT1 hT2)

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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 1) (x 3) ∨
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
    (hZ1 : Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4) ∨
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
    fA fT fG fH fU fW fY fZ hA hT hG hH hU hW hY hZ hZ1 hT2 hT6)

/-- **Type 12** (Theorem M of `FEWER-FACES-PROOFS.md` §7): a nopert does not have
seven points labelled so that `0135`, `0346` (quadrilaterals), `024`, `236` and
`246` are facets (given by functionals negative off them); general position here
is `Minimality.TriGenFar` at the lines of the planes of `0135` and `024` and of
`024` and `236`. A view whose hypothesis is
`Minimality.TriGenPar` (it has a triangle face) allows any tie of the far
ends, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hT1 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0)) ∧
      (fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
          (({0, 2, 4} : Finset (Fin 7)).image x) (x 0)))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
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
`Minimality.TriGenPar` (it has a triangle face) allows any tie of the far
ends, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hT1 : Minimality.TriGenPar (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
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
`Minimality.TriGenPar` (it has a triangle face) allows any tie of the far
ends, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). -/
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
    (hT1 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4)) ∧
      (fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 →
        Minimality.TriGenFar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
          (({1, 4, 6} : Finset (Fin 7)).image x) (x 4)))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({0, 3, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({0, 3, 6} : Finset (Fin 7)).image x) (x 0)) : False :=
  h.2 (Minimality.isRupert_type28 x hx (noThreeCollinear_seven x h hx)
    fA fD fG fH fF fM hA hD hG hH hF hM hT1 hT2)

/-- **Type 05** (Theorem B′ of `FEWER-FACES-PROOFS.md`, here by Lemma T): a nopert
does not have seven points labelled so that `0123`, `0145` (quadrilaterals),
`246`, `456` and `234` are facets (given by functionals negative off them);
general position here is `Minimality.TriGenPar` (or `Minimality.TriGenFarP`) at the
lines of the planes of `0123` and `246` and of `0145` and `246`, and where the deciding
number `fG x5 / fG x0 + fA x5 / fA x4` of the first is 1, `Minimality.EdgeFar` along `01`.
A view whose hypothesis is `Minimality.TriGenPar` (it has a triangle face) allows any tie of the
far ends, the triple tie with the shared vertex included (Lemma T at the tie and
Theorem 24.5 (a), (b): the triangle face is one-sided). At the special value
the edge `01` is parallel to the line of the first view (`Minimality.type05_special_parallel`),
so `Minimality.TriGenFar` cannot hold there; instead `Minimality.EdgeFar` along `01` is asked
(Lemma T′ over that edge, `FEWER-FACES-PROOFS.md` §23 item (ii)), which fails at the special
value only on a set of codimension 2. -/
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
    (hT1 : (Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2)) ∧
      (fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 →
        Minimality.EdgeFar (Finset.univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
          (({0, 1, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 1)))
    (hT2 : Minimality.TriGenPar (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
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

/-- **Type 16 outside codimension 2** (Theorem 19.8 with §18.6 step 2 and §22 of
`FEWER-FACES-PROOFS.md`): a nopert does not have
seven points labelled so that `0235`, `1356` (quadrilaterals), `024`, `036`, `046`, `145`,
`146`, `245` are facets (given by functionals negative off them), unless one of the following
holds.
* A horizontal double normal at the view along `35`, the edge of the two quadrilaterals,
  together with a failure of the codimension-2 conditions there (`Minimality.Gen35Aff`:
  `Minimality.EdgeGen` for `1356`, `0235`; `3`, `5` off the planes `124`, `014`, `246` of
  Lemma E; the shape and its `σ`-image off the boundary of Lemma 19.3's region,
  `Minimality.Off193`).  Its edge pairs are closed by §22.3–22.8, its triangle closings by
  Proposition 22.2, and Lemma 19.3's `T1` (no Lemma E) by §22.12: in its residual `T2` is
  unimodal and is closed at its own view (below).
  Nothing is asked at the eleven segments `01`, `04`, `05`, `12`, `13`, `23`, `26`, `34`, `45`,
  `46`, `56`: no certificate of the cover uses their views.
* A horizontal double normal at the view along one of the six quadrilateral-triangle edges
  together with a failure of the codimension-2 conditions of §22.4 there
  (`Minimality.EdgeGenAff`: only the axle seen end-on, (G1), distinct depths, at most one
  direction of horizontal double normals, no double normal perpendicular to a face from a face
  vertex, the axle off the plane of Lemma E).  Edge pairs are closed by §22.3–22.8
  (`Minimality.isRupert_edgeClosing`: slides along the face circles, classes c and d, Theorem R),
  the other certificates there are realized on both face circles (Proposition 22.2).
* A horizontal double normal at the view along the line of `0235/046` or `1356/046` together with
  a failure of the codimension-2 conditions of §22.4 there (`Minimality.HDNOrVtxGenAff`,
  `Minimality.VtxGen`: no two points over one point, (G1), distinct depths, at most one direction
  of horizontal double normals, no double normal perpendicular to the quadrilateral from one of
  its vertices).  The certificate there, Lemma 19.5's `T_a`, is realized on the quadrilateral's
  circle only; it is closed by Lemma 22.3, Lemma 22.4 (class `c`), and Lemma 22.9 with
  Theorem 22.8 or Lemma 22.10 (class `d`; `Minimality.isRupert_vtx_limit`).
* A horizontal double normal at the view along one of the two-triangle edges `06`, `14`, `24`, or
  along the line of `046/145`, `036/146`, `046/245`, `036/024`, together with a failure of (G1)
  there
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
    (h35 : Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 3) ∨ Minimality.Gen35Aff x fA fB)
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 2) (x 4) (x 0) (x 5))
    (hQ : (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 0) ∨
        Minimality.EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 1 - x 6) ∨
        Minimality.EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 1) ∨
        Minimality.EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 2) ∨
        Minimality.EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 3 - x 0) ∨
        Minimality.EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 3) ∨
        Minimality.EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4))
    (hV : Minimality.HDNOrG1Aff (Finset.univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      Minimality.HDNOrVtxGenAff (Finset.univ.image x) fA fE
        (({0, 2, 3, 5} : Finset (Fin 7)).image x) (({0, 4, 6} : Finset (Fin 7)).image x) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      Minimality.HDNOrVtxGenAff (Finset.univ.image x) fB fE
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (({0, 4, 6} : Finset (Fin 7)).image x))
    (htie : Minimality.OneTie16 x) : False :=
  h.2 (Minimality.isRupert_type16_limit_facets_edge x hx fA fB fC fD fE fF fG fH hA hB hC hD hE
    hF hG hH h35 hEd hQ hV htie)


/-! ### The special value of Lemma T′ settled (types 05, 10, 12, 13, 17, 19, 22, 23, 27, 28)

Each of these types is decided by a number `s` (`FEWER-FACES-PROOFS.md` §7, Theorems E–O and
type 05). At `s = 1` three faces are edge-on in one view, and the statements above ask a
condition there that excludes a single tie (`EdgeFar` along the forced parallel edge for
05, 10, 13, 17, 19, 23, 27; `TriGenFar` for 12, 22, 28), on top of their general position at
the views that coincide there. The statements below ask their general position only off
`s = 1`, and at `s = 1` only that the three corners of the shadow triangle are not at one
depth (`Minimality.SpecTriple`, `Minimality.ViewTriple`): every other tie, and any segment
parallel to the view, is settled by a reading of Lemma T′ at one of the three corners
(`FEWER-FACES-PROOFS.md` Theorems 23.18 and 24.13; `Minimality/SpecialValue.lean`). They
imply the statements above. -/

/-- **Type 05, the special value settled**: as `not_type05_of_isNopert`, with
`Minimality.TriGenPar` (or `Minimality.TriGenFarP`) at the two views asked only where the
deciding number `fG x5 / fG x0 + fA x5 / fA x4` is not 1, and where it is 1 only no triple
tie of `x2`, `x4` and `x0` or `x1` along `01`. -/
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
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hS : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 →
      ¬ Minimality.SpecTriple (x 0) (x 1) (x 2) (x 4)) : False :=
  h.2 (Minimality.isRupert_type05_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fG fK fH hA hB hG hK hH hT1 hT2 hS)

/-- **Type 10, the special value settled**: as `not_type10_of_isNopert`, its general
position asked only where `fB x0 / fB x2 + fA x0 / fA x3` is not 1, and where it is 1 only
no triple tie of `x2`, `x3` and `x1` or `x4` along `14`. -/
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
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2))
    (hS : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 →
      ¬ Minimality.SpecTriple (x 1) (x 4) (x 2) (x 3)) : False :=
  h.2 (Minimality.isRupert_type10_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fC fD hA hB hC hD hZ1 hT2 hS)

/-- **Type 13, the special value settled**: as `not_type13_of_isNopert`, its general
position asked only where `fB x3 / fB x1 + fA x3 / fA x2` is not 1, and where it is 1 only
no triple tie of `x1`, `x2` and `x4` or `x5` along `45`. -/
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
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1))
    (hS : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1 →
      ¬ Minimality.SpecTriple (x 4) (x 5) (x 1) (x 2)) : False :=
  h.2 (Minimality.isRupert_type13_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2 hS)

/-- **Type 17, the special value settled**: as `not_type17_of_isNopert`, its general
position asked only where `fB x0 / fB x6 + fD x0 / fD x4` is not 1, and where it is 1 only
no triple tie of `x6`, `x3` and `x2` or `x4` along `24`. -/
theorem not_type17_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hT1 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3))
    (hT2 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6))
    (hS : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 →
      ¬ Minimality.SpecTriple (x 2) (x 4) (x 6) (x 3)) : False :=
  h.2 (Minimality.isRupert_type17_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fD fE hA hB hD hE hT1 hT2 hS)

/-- **Type 19, the special value settled**: as `not_type19_of_isNopert`, its general
position asked only where `fB x4 / fB x0 + fA x4 / fA x6` is not 1, and where it is 1 only
no triple tie of `x0`, `x6` and `x3` or `x5` along `35`. -/
theorem not_type19_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hZ1 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      Minimality.EdgeTieR (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) ∨
      Minimality.EdgeFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1 →
      ¬ Minimality.SpecTriple (x 3) (x 5) (x 0) (x 6)) : False :=
  h.2 (Minimality.isRupert_type19_sv x hx (noThreeCollinear_seven x h hx)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp h.1)
    fA fB fD fG hA hB hD hG hZ1 hT2 hS)

/-- **Type 23, the special value settled**: as `not_type23_of_isNopert`, its general
position asked only where `fA x6 / fA x1 + fD x6 / fD x5` is not 1, and where it is 1 only
no triple tie of `x1`, `x5` and `x0` or `x4` along `04`. -/
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
      Minimality.EdgePar (Finset.univ.image x) (x 0) (x 4) ∨
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
        (({1, 2, 5} : Finset (Fin 7)).image x) (x 5))
    (hS : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1 →
      ¬ Minimality.SpecTriple (x 0) (x 4) (x 1) (x 5)) : False :=
  h.2 (Minimality.isRupert_type23_sv x hx (noThreeCollinear_seven x h hx)
    fA fD fE fH fK hA hD hE hH hK hZ1 hT1 hT2 hS)

/-- **Type 27, the special value settled**: as `not_type27_of_isNopert`, its general
position asked only where `fG x2 / fG x5` is not 1, and where it is 1 only no triple tie of
`x0`, `x6` and `x2` or `x5` along `25`. -/
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
      Minimality.EdgePar (Finset.univ.image x) (x 2) (x 5) ∨
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
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fG (x 2) / fG (x 5) = 1 → ¬ Minimality.SpecTriple (x 2) (x 5) (x 0) (x 6)) : False :=
  h.2 (Minimality.isRupert_type27_sv x hx (noThreeCollinear_seven x h hx)
    fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ hZ1 hT1 hT2 hS)

/-- **Type 12, the special value settled**: as `not_type12_of_isNopert`, its general
position asked only where `fD x6 / fD x3 + fA x6 / fA x2` is not 1, and where it is 1 only
no triple tie of `x0`, `x3`, `x2` in the view along the planes of `0135` and `024`. -/
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
        (({2, 3, 6} : Finset (Fin 7)).image x) (x 2))
    (hS : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 →
      ¬ Minimality.ViewTriple fA fD (x 0) (x 3) (x 2)) : False :=
  h.2 (Minimality.isRupert_type12_sv x hx (noThreeCollinear_seven x h hx)
    fA fB fD fG fJ hA hB hD hG hJ hT1 hT2 hS)

/-- **Type 22, the special value settled**: as `not_type22_of_isNopert`, its general
position asked only where `fG x5 / fG x1 + fA x5 / fA x2` is not 1, and where it is 1 only
no triple tie of `x4`, `x1`, `x2` in the view along the planes of `0134` and `246`. -/
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
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hS : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1 →
      ¬ Minimality.ViewTriple fA fG (x 4) (x 1) (x 2)) : False :=
  h.2 (Minimality.isRupert_type22_sv x hx (noThreeCollinear_seven x h hx)
    fA fD fG fN fI hA hD hG hN hI hT1 hT2 hS)

/-- **Type 28, the special value settled**: as `not_type28_of_isNopert`, its general
position asked only where `fG x3 / fG x0 + fA x3 / fA x6` is not 1, and where it is 1 only
no triple tie of `x4`, `x0`, `x6` in the view along the planes of `0245` and `146`. -/
theorem not_type28_of_isNopert_sv (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
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
    (hT1 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hT2 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      Minimality.TriGenPar (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0) ∨
      Minimality.TriGenFarP (Finset.univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 →
      ¬ Minimality.ViewTriple fA fG (x 4) (x 0) (x 6)) : False :=
  h.2 (Minimality.isRupert_type28_sv x hx (noThreeCollinear_seven x h hx)
    fA fD fG fH fF fM hA hD hG hH hF hM hT1 hT2 hS)

end
