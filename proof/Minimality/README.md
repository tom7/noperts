# Minimality: overview of the Rupert theorems for small polyhedra

The entry point is [`../Minimality.lean`](../Minimality.lean): it states, for
non-expert readers, that every nopert (`IsNopert`, in
[`../Nopert.lean`](../Nopert.lean)) has at least 7 points, that a nopert with
exactly 7 points has no face with 5 or more of them, and the sharp statements
about flat point sets.  The idea of the proof is explained in
[`minimality.md`](../../minimality.md) (section "A bit more detail",
steps 1–6).

This file maps that outline to the Lean files: it lists the parts L1–L11 of
the proof, the numbered statements that comments in the Lean files cite
(Lemma 1, Theorem 5, Lemma 7.1, Theorem 9.9, …) with the declarations that
prove them, and the modules.  The names in `Minimality/` are in the namespace
`Minimality`; the entry point's statements are at the root.
Everything is proved against `IsRupert` from `MainTheorem.lean`;
`V : Finset ℝ³` is the point set (it may contain non-extreme points).  Every
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Parts and numbered statements

**L1. First order suffices** (step 1 of `minimality.md`; `FirstOrder.lean`)
* Lemma 1 — `isRupert_of_firstOrderInward`: a strictly inward first-order
  motion `(ω, τ)` gives a passage.  Frame-free form with local certificates:
  `isRupert_of_tiltCert` (`Tilt.lean`).

**L2–L5. Planar silhouettes** (step 2)
* L2, the screen motion of a plane — `screenVel_of_depth_eq`,
  `exists_motion_of_admissible` (`Coplanar.lean`): on a plane, the screen
  velocity is an affine field `M p + b`, and every *admissible* `M`
  (`⟪û, M û⟫ = 0` for the iso-depth direction `û`) is realized.
* L3, double normals (`DoubleNormal.lean`) — Lemma 3:
  `exists_admissible_inward_field`: if `û` is not a double-normal direction of
  a convex polygon, some admissible field points strictly inward at every
  corner.  Lemma 3.0: `isDoubleNormalDir_convexHull_cases`, there are
  finitely many double-normal directions.
* L4, from the plane to its shadow — `isDoubleNormalDir_proj_iff'`.
* Theorem 5 (coplanar-silhouette theorem) —
  `isRupert_of_admissibleViews_nonempty` (`Crossing.lean`): if, for a planar
  non-collinear `W ⊆ V`, some view projects every other point of `V` into the
  relative interior of `conv W`, then `V` is Rupert.  Crossing form
  `isRupert_of_crossing`; the waist lemma `isRupert_of_waist` and bipyramids
  `isRupert_bipyramid` (`Pyramid.lean`).
* Cor. 5.3 — `isRupert_of_pyramid`: pyramids.
* Cor. 5.4 (bipyramid lemma) — `isRupert_of_segment_crossing`: a segment
  `DE` crossing `relint conv W`.
* Cor. 5.6 — `isRupert_of_card_le_five`: at most 5 vertices.
* Cor. 5.7 — `isRupert_bicappedTetrahedron`: bicapped tetrahedra (T7).

**L6. The seven combinatorial types of 6-vertex polyhedra**

| type | faces | description | Lean |
|---|---|---|---|
| T1 | 2 △ + 3 □ | triangular prism | `isRupert_frustum`, `isRupert_parallelPrism`, `isRupert_translationPrism_all`, `isRupert_of_all_partners` |
| T2 | 1 ⬠ + 5 △ | pentagonal pyramid | `isRupert_of_pyramid` |
| T3 | 2 □ + 4 △ | tetragonal antiwedge | `IsT3`, `isRupert_T3` |
| T4 | 1 □ + 6 △ | octahedron with two adjacent faces coplanar | `IsT4`, `isRupert_T4` |
| T5 | 1 □ + 6 △ | square pyramid with a cap on one lateral face | `IsCappedSquarePyramid`, `isRupert_cappedSquarePyramid_all` |
| T6 | 8 △ | octahedron | `IsOctahedron`, `isRupert_octahedron` |
| T7 | 8 △ | bicapped tetrahedron | `IsBicappedTetrahedron`, `isRupert_bicappedTetrahedron` |

The coplanar-silhouette theorem covers T2, T7, most of T1 and most of T5
(`SixVertices.lean`); L7–L9 cover the rest.  The proof never computes these
types: L10 reads the facets it needs off the coordinates.

**L7. Unimodal silhouettes** (step 3; `Unimodal.lean`, which also states the
genericity conditions (G1), (G2) and the balance conditions (E1)–(E3))
* Lemma 7.1 — `exists_forces_of_not_firstOrderInward`: if no first-order
  motion is strictly inward, there are balanced corner forces.
* Theorem 7.3 — `hasHorizontalDoubleNormal_of_forces` (polygon form) and
  `isRupert_of_unimodalView`: at a unimodal silhouette, balanced forces give
  a horizontal double normal; so without one there is a passage.  The steps
  1–5 of its proof are listed in `CycSeq.lean`.
* Lemma 7.4 — `exists_badPlanes`: horizontal double normals occur only on
  finitely many great circles of views (`BadViews.lean`).
* Theorem 7.5 — `isRupert_of_genericUnimodalView`: a generic unimodal view
  gives a passage; robust forms `isRupert_of_eventually_unimodal`,
  `isRupert_of_open_unimodal`.
* Theorem 7.7 — `isRupert_translationPrism` (`Prism.lean`): translation
  prisms, except right prisms over non-obtuse triangles.
* Cor. 7.8 (Condition A) — `isRupert_octahedron_conditionA`
  (`Octahedron.lean`): octahedra in which the projections of two diagonals
  onto the third overlap in more than a point.

**L8. Tilting off degenerate views** (step 4; `Tilt.lean`)
* Lemma 8.0 — `eventually_tilted_cycle`: the silhouette at the views
  `u₀ + εv` just off a degenerate view `u₀`, from signs of determinants.
* Cor. 8.0′ — `isRupert_of_tilted_unimodal`: if that silhouette is robustly
  unimodal, there is a passage.
* Theorem 8.1 — `isRupert_rightPrism` (`RightPrism.lean`): right prisms over
  any strictly convex polygon; with Theorem 7.7,
  `isRupert_translationPrism_all`.
* Theorem 8.2 — `isRupert_cappedSquarePyramid_all` (`L8Shapes.lean`): every T5.
* Theorem 8.3 — `isRupert_T4` (`L8T4.lean`): every T4.
* Theorem 8.4 — `isRupert_T3` (`L8T3.lean`): every T3.

**L9. Octahedra** (step 5, the hardest case; overview in `OctahedronAll.lean`)
* Theorem 9.9 — `isRupert_octahedron`: every convex octahedron (T6).
* Lemma 9.3 — `isRupert_quad_edge` (`Oct9Quad.lean`): a *quad edge* (an edge
  whose view hides the antipodal vertex) that is neither *bad* nor *touching*
  gives a passage.
* Lemma 9.4 — `isRupert_of_touching_pair` (`Oct9Axis.lean`): two touching
  quad edges give a passage at an axis view.  Planar equators:
  `isRupert_planar_equator` (Cor. 5.4).
* §9.4, the Gale diagram, as affine dependencies (`Oct9Gale.lean`):
  Lemma 9.6 — `facet_lt_of_dep` (a dependency applied to a facet, which
  decides which vertex an edge view hides); Lemma 9.8 — `arc_lemma` (the
  choice of the pair of edges).
* §9.5, the generic case — `isRupert_octahedron_generic`.
* §9.6, two parallel opposite faces — `isRupert_octahedron_parallel`
  (`Oct9Par.lean`), using Lemma 9.11 — `isRupert_weak_edge` (`Oct9Weak.lean`)
  for weak quad edges, and Cor. 8.0′ in either orientation
  (`isRupert_of_tilted_unimodal_σ`).

**L10. The classification step** (step 5; `SixGale.lean`, `SixClass.lean`)
* Theorem 10.0 — `isRupert_of_card_le_six`: at most 6 points with a solid hull
  are Rupert.
* Setting (S) — `Six V`: six points in convex position, no five coplanar.
* §10.1 — dependencies and Gale signs; facets and independent tetrahedra from
  Gale signs: `isFacetTriangle_of_gale`, `isFacet_quad_of_gale`,
  `affineIndependent_of_gale`.
* Lemma 10.1 — `exists_split_of_no_partner`: a point without an O-partner
  gives a 2+4 Radon split.
* Prop. 10.2 — `isRupert_of_all_partners`: three O-pairs make a prism
  (frustum, parallel or translation prism).
* Lemma 10.3 — `isRupert_split_coplanar`: a split with coplanar `W` is a
  segment crossing.
* Theorem 10.4 — `NF.isRupert`: the case table (T3–T7) of a split in normal
  form `NF`.

**L11. Seven points with a face of five or six** (`FaceChain.lean`,
`FaceFive.lean`; Theorem A of the notes `FEWER-FACES-PROOFS.md`)
* Theorem A — `isRupert_of_card_seven_of_facet`: seven points with a solid
  hull, at least five (not all) on a facet (`IsFacet`), are Rupert.  At the
  entry point, `facet_card_le_four_of_isNopert`.
* The lower chain of a face seen edge-on — `exists_lowerChain'`,
  `cross2_pos_of_consecutive'` (`FaceChain.lean`; `ConvPos`: strict convex
  position).
* The edge-on lemma — `isRupert_edgeOn`, `isRupert_edgeOn_dir`: the face's
  lower chain followed by the deepest point below, at the views `u + ε ez`.
* The cycle lemma — `isRupert_cycle_edgeOn`: the same with a general tilt,
  lexicographic depth ties, and vertical end edges.
* Case I (the two points below at different heights) — `isRupert_caseI`: a
  view in the face's plane hides the higher one.
* Case II (equal heights) — `isRupert_caseII_view` (the view along the two
  points, one hidden behind the other), `isRupert_caseII_fallback` (Theorem 5
  through the waist lemma, with an explicit witness `fallback_witness`).

**L13. The triangle-shadow lemma** (`TriShadow.lean`; Lemma T of
`FEWER-FACES-PROOFS.md` §7)
* `isRupert_triShadow`: in the oblique frame of L12 (view `ez`, apex at
  oblique coordinates `(0, 0)`), chains `C1` on the first ray and `C2` on the
  second (coordinate sequences), every point of `V` in the triangle and
  strictly inside its far side unless it is `A` or `B`, the points of each ray
  on the `s`-side of each segment of that ray's chain, and `s z_A > s z_B`:
  the tilt `-s r1 + s r2` is unimodal, so `V` is Rupert. Unimodality is
  `tri_localMax_unique` (every local maximum of `s z` lies on the concave
  chain). Its hypotheses are strict inequalities between depths (`TriSeq`),
  an open condition that survives the tilt, so depths along the cycle may tie
  (`isRupert_of_tilted_localMax`); only the far ends must differ.
* `isRupert_twoQuads_frame` (`TriQuad.lean`): two quadrilaterals sharing the
  apex, one on each ray, each convex in its `(t, z)`-plane (either
  orientation), distinct positive `t` on each, the far vertices (largest `t`
  on each ray) at distinct depths: Rupert.
  `quad_chain` gives the upper and lower chains of a convex quadrilateral seen
  from a vertex (six cases plus relabelling).
* At the entry point, `not_two_quad_facets_vertex_of_isNopert`: a 7-point
  nopert has no two quadrilateral facets meeting in a single vertex (no three
  of its points are collinear: `noThreeCollinear_of_not_isRupert`, the middle
  one would lie in the hull of the other six), given `TriGenFar` (no
  segment parallel to the line of the two planes, distinct depths along it at
  the two far vertices). This excludes types 02, 07, 09, 14, 18, 20
  in general position. Via `isRupert_of_two_quad_facets_vertex` (enumeration,
  the line `e = n1 × n2`), `isRupert_twoQuads` (rotation of `e` to `ez`),
  `isRupert_twoQuads_vertical` (oblique frame by Cramer, each quadrilateral's
  convex labelling by `convex_four` from extremality), and the frame theorem.
* At the entry point, `not_facets_vertex_triShadow_of_isNopert`: Lemma T at a
  vertex for any two facets (any number of points each) meeting in a single
  vertex `v`, with `TriGenFar` (as above): a nopert in general position never has every point
  off both facets strictly inside the shadow triangle of `v` and points `xa`,
  `xb` of the facets (barycentric form `f2 y / f2 xa + f1 y / f1 xb < 1` with the
  facet functionals). Extreme points are not needed. Via
  `isRupert_of_facets_vertex` (`TriFacets.lean`; the line `e = n1 × n2`),
  `isRupert_facets_vertex` (rotation), `isRupert_facets_vertex_vertical`
  (oblique frame by Cramer, coordinates `a = f2 / f2 p1`, `b = f1 / f1 p2`),
  `isRupert_vertex_coords` (each face's chains by gift wrapping,
  `exists_chainOK` in `HullChain.lean`), and `isRupert_vertex_frame`.
* At the entry point, `not_facets_edge_triShadow_of_isNopert`: the same for two
  facets sharing exactly an edge `v w`, viewed along it (`EdgeFar`: no other
  segment parallel to it, distinct depths along `w - v` at the two far ends).
  Via
  `isRupert_of_facets_edge`, `isRupert_facets_edge` (rotation of `w - v` to
  `ez`), `isRupert_facets_edge_vertical`, `isRupert_edge_coords` (chains from
  the upper and lower edge points, `exists_chainOK_edge`), and
  `isRupert_edge_frame` (`TriFacetsEdge.lean`).
* At the entry point, `not_type10_of_isNopert` (Theorem E, type 10, the capped
  frustum; `Type10.lean`): with the functionals of `1245, 1346, 2356, 023` and
  `s = fB x0 / fB x2 + fA x0 / fA x3`, `s < 1` gives Lemma T along the edge
  `14` and `s > 1` gives Lemma T at the vertex `2` (planes of `023`, `1245`),
  by a Cramer identity for `x6` in the frame `x4; x0, x2, x3`
  (`affine_cramer`): `fA x6 / fA x3 + fD x6 / fD x4 = 1 + r (s - 1)` with
  `r < 0`. Any facet functional's ratios equal the given ones
  (`vanish3_ratio`).
* At the entry point, `not_type19_of_isNopert` (Theorem F, type 19;
  `Type19.lean`): the same method with faces `0235, 1356, 046, 346`:
  `s = fB x4 / fB x0 + fA x4 / fA x6`; `s < 1` gives Lemma T along the edge
  `35`, `s > 1` Lemma T at `x0` (planes of `0235`, `046`), since Cramer for `x1`
  in the frame `x3; x0, x4, x6` gives `fD x1 / fD x3 + fA x1 / fA x6 = 1 + ρ (s - 1)`
  with `ρ < 0`.
* At the entry point, `not_type13_of_isNopert` (Theorem G, type 13;
  `Type13.lean`): faces `0145, 2456, 123, 126`; `s = fB x3 / fB x1 + fA x3 / fA x2`;
  `s < 1` gives Lemma T along the edge `45`, `s > 1` Lemma T at `x1` (planes of
  `0145`, `123`): with `x3 - x6` in the frame `x1 - x6, x2 - x6, x5 - x6` and
  `σ` its coefficient sum, `(t - 1)(σ - 1) = 1 - s` and `σ > 1`.
* At the entry point, `not_type17_of_isNopert` (Theorem H, type 17;
  `Type17.lean`): faces `0246, 2345, 136, 034`; two vertex views (planes of
  `136`, `2345` through `x3`; of `0246`, `136` through `x6`);
  `s = fB x0 / fB x6 + fD x0 / fD x4` and, by Cramer for `x5` in the frame
  `x4; x0, x3, x6`, `t = 1 + α (s - 1)` with `α < 0`.
* At the entry point, `not_type27_of_isNopert` (Theorem I, type 27;
  `Type27.lean`): three views (edge `25`; planes of `016`, `2356`; planes of
  `025`, `046`). In the affine frame `x0; x2, x5, x6` (`affine_coord`) the edge
  view holds at `y` iff `α_y + β_y > 0`; failing at `1` forces
  `fE x2 / fE x5 ≥ 1`, which gives the second view, failing at `4` forces
  `fG x2 / fG x5 < 1`, which gives the third.
* At the entry point, `not_type23_of_isNopert` (Theorem J, type 23;
  `Type23.lean`): three views (edge `04`; planes of `014`, `156`; planes of
  `0345`, `125`); failure of the edge view at `6` gives the second view in the
  frame `x1; x4, x5, x6`, failure at `2` the third in the frame `x5; x1, x2, x4`.
* At the entry point, `not_type25_of_isNopert` (Theorem K, type 25;
  `Type25.lean`): edge `13`, planes of `013` with `0246`, and with `056`; in
  the frame `x1; x0, x3, x6` the edge view at `y` is `α_y + γ_y < 1`; failure
  at `2` or `4` gives the second view, failure at `5` the third.
* At the entry point, `not_type26_of_isNopert` (Theorem L, type 26;
  `Type26.lean`): `type26_core` treats the case where the far end of `0246`
  in the view along `04` is `2` (then that view holds at `1`, as vertex `1` has
  degree 3, and failure at `5` gives the view along the planes of `0246`,
  `235`); the other case is the core applied to the points relabelled by the
  automorphism `0 ↔ 4, 1 ↔ 5, 2 ↔ 6`.
* At the entry point, `not_type12_of_isNopert` (Theorem M, type 12;
  `Type12.lean`): views along the planes of `0135` and `024` and of `024` and
  `236`; in the frame `x2; x0, x3, x4` their values are `1 + γ6 c` and
  `1 + γ_y c` (`y = 1, 5`) with `γ6 > 0 > γ_y`, so exactly one works unless
  `c = 0`.
* At the entry point, `not_type22_of_isNopert` (Theorem N, type 22;
  `Type22.lean`): the same structure in the frame `x4; x1, x2, x6` (views along
  the planes of `125`, `246` and of `0134`, `246`).
* At the entry point, `not_type28_of_isNopert` (Theorem O, type 28;
  `Type28.lean`): the same structure in the frame `x0; x4, x6, x2` (views along
  the planes of `0245`, `146` and of `0245`, `036`); `γ1 < 0` by eliminating
  `1 - σ1` between the faces `145` and `146`.
* At the entry point, `not_type05_of_isNopert` (`Type05.lean`): type 05 by
  Lemma T instead of Theorem B′, with the same structure (frame
  `x0; x2, x4, x6`; views along the planes of `0123`, `246` and of `0145`,
  `246`). With this, every type proved on paper (now 25 of 29, with type 08) is excluded
  at the facet level in general position.
* At the entry point, `not_type08_of_isNopert` (Theorem 10.1 of
  `FEWER-FACES-PROOFS.md` §10, type 08; `Type08Lemmas.lean`, `Type08Cases.lean`,
  `Type08T4.lean`, `Type08.lean`): not by Lemma T but by edge crossings (Theorem
  8.9 with Theorem 7.3, `isRupert_of_edgeChords_unimodal`) and the octahedron
  `K − 2`. The seven points are the octahedron of `x 0, …, x 6` without `x 2`
  (opposite pairs `(0, 6)`, `(3, 4)`, `(5, 1)`) with the cap `x 2` (`IsCap`; the
  octahedron's face `035` is built from the three quadrilaterals,
  `isRupert_type08_facets`). In the labelling of Lemma 6 (`type08_lemma6`, Gale
  signs) the proof views along the QQ edge `d b` (`isRupert_type08_normalized`):
  if the far end of `Q_bc` is `a'` (Lemma 1 (a), `far_end_Qbc_iff`), Lemma 7
  (`type08_lemma7`, the Gale chain) makes `a' → c` a quad edge of the octahedron
  that is not bad and Lemma 2 (`IsCap.middle_Qbc`) makes the cap a middle, so
  Lemma 9.3 with a middle applies (`isRupert_quad_edge_middle`); if the far ends
  are `a`, `c`, `K_d` is the face `Q_ac` (Lemma 1 (c), `IsCap.Qac_nws4`,
  `isRupert_type08_Q`); if they are `c'`, `c`, the T4 `K − a` at `d b` (Lemma 5,
  `isRupert_type08_T4`) is not bad by Lemma 9.7 (`inTri_of_dep`), Lemma 4
  (`inTri_cap_BD`, `inTri_cap_AB`, with the facts (i)–(iii) in
  `IsCap.axis_facts`) and Lemma 3 (`not_bad_of_crossing`, `not_bad_of_inTri`).
  General position: no planar equator of the octahedron, `GenPos`,
  `NoPlaneParallel` (no plane through three of the points parallel to the
  segment of two others), and `NoHDNAt` (no horizontal double normal at the
  views along the segments, the exclusion of Theorem 10.1). The same in octahedron
  form: `isRupert_type08`.
* At the entry point, `not_type08_of_isNopert'` (Theorem 10.1′ of the §10 addendum of
  `FEWER-FACES-PROOFS.md`, Lemmas C, H, K, X in Lean form; `Slide.lean`,
  `Type08Slide.lean`, `Type08Tie.lean`, `Type08Codim.lean`, `Type08Flat.lean`): type 08
  without `GenPos`, `NoPlaneParallel` and `NoHDNAt`.  The hypotheses, per labelling of
  Lemma 6, are collected in `Type08Gen` (`Type08GenAll`: all six labellings); `O` may
  have one planar equator.  Lemma C (`isRupert_of_slide`): slide the view along the great
  circle of a face through the named crossing; the face's middles lie over its side
  (Proposition 8.8 with one face), the rim is `K_v`'s, depth ties and horizontal double
  normals occur at isolated views unless a direction of a pair of rim edges with
  meeting depth intervals (Lemma 7.4 by edges, `exists_pairDir_of_hdn`, `pairDirs`) is
  normal to the face (`NoBadNormal`).  The case slides: N2 `isRupert_quad_edge_middle_slide`,
  T4 `isRupert_t4_slide`, Q `isRupert_q_slide` (in the frame `d; a, c, b`, all tests
  multiples of `E = det3 (a − d) (c − d) (b − d)`).  Lemma H for the closings with one
  circle: the five-corner rim along the other face (`isRupert_quad_edge_middle_five`,
  `isRupert_t4b_five`, `isRupert_t4d_five`; strictly unimodal, `StrictUnimodal`).
  Lemma X at the far-end ties `T` (`β₂ = 1`) and `T'` (`α₁ = 1`): the far end of the
  other face from the identity `α + β = κ_b` (`type08_T_far`, `type08_T'_far`), and the
  routes R1/R4′ (`isRupert_kb_four`), R2′/R3 (`isRupert_kd_four`), R2″ (`isRupert_r2pp`),
  R2′ with `a'` poking out (`isRupert_r2p`), R4″ (`isRupert_r4pp`), R4′ with `a` poking out
  (`isRupert_r4p`); which route applies is a hypothesis (`Type08Gen.routeT`, `routeT'`).
  Lemma G: in the T4 case `b'` is a corner (`t4_kappa_pos`), the other (G1) coincidences
  never occur in the frame.  Lemma K (`isRupert_type08_flat`): with `κ_X = 0`, `X` takes the
  role `a` (`isRupert_type08_flatA`: Lemma 7's quad edge from `(G4)`, `type08_quad_edge`;
  "not bad" from the crossing diagonals of the planar equator, `flat_cross`,
  `not_bad_of_cross`) or `b` (`isRupert_type08_flatB`: signs from `(G4)`, `flatB_signs`;
  the T4 case empty).  Not formalized: Lemma H (c) (depth-separated type (c) double
  normals with a non-unimodal five-corner rim), the open piece `R_d`, and the case
  analysis that one route of Lemma X applies at `T`, `T'`.
* Theorem P of `FEWER-FACES-PROOFS.md` §12 (type 29, partial; `Type29Lemmas.lean`,
  `Type29Lift.lean`, `Type29.lean`): `K` is the octahedron `O = K − 6` (opposite
  pairs `(0, 4)`, `(1, 3)`, `(2, 5)`) with the cap `6` on the plane `145`, beyond
  `345`, beneath the other faces (`IsCap29`). `isRupert_type29_P`: if clause C1 (an
  inner-tailed quad edge of `O` in `G = {1→4, 4→1, 1→5, 5→1, 0→3, 0→5, 2→3, 2→4}`,
  `Type29C1`), C2 (`K − 5` or `K − 4` an octahedron with an inner-tailed quad edge along
  `14`/`46` resp. `15`/`56` at which the removed vertex is a middle, `Type29C2`) or C3
  (an inner-tailed quad edge of an octahedron `K − m` with `m` hidden, `Type29C3`)
  holds, then, without planar equators, in general position (`GenPos`,
  `NoPlaneParallel`) and without horizontal double normals (`NoHDNAt`), `K` is Rupert.
  Lemma 1 (`not_bad_of_inner`), Lemma 2 (`isRupert_quad_edge_lift`), Lemma 3
  (`isRupert_type29_14`, `isRupert_type29_41` with the far-end lift
  `isRupert_lift_far`), Lemma 4 (`type29_hidden_03`, `type29_hidden_05`, by
  `quadHidden_of_beneath`). That some clause always holds is not proved, so there is
  no `not_type29_of_isNopert`.
* Theorem 5 of `FEWER-FACES-PROOFS.md` §9 (type 21, the octahedron route, conditional;
  `Type21Lemmas.lean`, `Type21Lift.lean`, `Type21.lean`): `K` is the octahedron
  `O6 = K − 2` (opposite pairs `(0, 3)`, `(4, 5)`, `(1, 6)`) with the cap `2` on the planes
  `056`, `346`, beyond `356`, beneath the other faces (`IsCap21`).  `isRupert_type21`: if
  the Gale data of `K − 2` or of `K − 6` satisfy `Type21Gale` (no planar equator, and an
  admissible `W` whose crossed pair contains a K-quad edge, or a TT edge at which the cap
  is hidden, `HiddenAt`), then, in general position (`GenPos`) and without horizontal
  double normals (`NoHDNEdges`), `K` is Rupert.  `K − 6` is the octahedron `IsCap21.O2`
  with the cap `6` (`IsCap21.sigma2`, the symmetry `σ2`).  Steps 1–2 of Theorem 9.9 as
  crossed pairs of good quad edges: `gale_crossed`, `gale_edge`.  Lemma 1 (a)
  (`IsCap21.not_hidden_04`), Lemma 2 (a) (`isRupert_type21_hidden`), Lemma 3 at the eight
  directed K-quad edges (`isRupert_type21_05`, `_50`, `_06`, `_60`, and `σ1`: `_43`,
  `_34`, `_46`, `_64`; the far ends: `isRupert_type21_50` through `O2` with
  `type21_far_not_bad_core`, `isRupert_type21_60_far` with the planar rim `2346`).  Not
  formalized: Lemma 1 in general, Lemma 4 (insertion), Theorem S.  That the hypothesis
  always holds is not proved, so there is no `not_type21_of_isNopert`.
* Theorem M′ of `FEWER-FACES-PROOFS.md` §11 and its addendum (type 16, partial;
  `Type16.lean`, `Type16M.lean`): `Type16` gives the facets `0235`, `1356` (quadrilaterals
  meeting in the edge `ℓ = 35`) and `024`, `036`, `046`, `145`, `146`, `245`.
  `isRupert_type16_M`: if one of the proved clauses holds (`Type16Clause`), then in
  general position (`GenPos`, `NoPlaneParallel`) and without horizontal double normals
  (`NoHDNAt`) `K` is Rupert.  Lemma 11.U (`isRupert_type16_35`): at the view along `35`,
  with far ends `A ∈ {0, 2}`, `B ∈ {1, 6}` (the other vertex a middle, `MidOf`), a closing
  is unimodal unless *35 is bad* (`Type16Bad35`: `4` a corner and
  `min (z 3, z 4) > max (z A, z B)`); part (b) `lemmaU_b_real` (strict, from the face
  `245` alone), in screen coordinates `frame_coords`, `det3_frame`, `lemmaU_coords`.
  Corollary 11.Ua: `type16_not_bad35_of_far`, `type16_not_bad35_of_acute`.  The
  octahedral region (`Oct16`: `123`, `124` faces of `O = K − 5`): Lemma 11.1
  (`Oct16.five_beyond`, the virtual cap `Oct16.star` on `ℓ` with `IsCap` over
  `Oct16.facets`, so `O ∪ {5*}` is type 08); S1 at `ℓ`: third quadrilateral
  (`type16_not_bad35_thirdQuad`), J's T4 case in `K*` (`type16_not_bad35_T4`, `…T4σ`, via
  `t4_not_bad'`, §10's T4 lemma with `κ_b` only nonzero), the case N2 (§10's Lemma 7 with
  `5` a middle, `middle_Qbc_of`: `isRupert_type16_N2`, `…N2σ`); S2's N2 branch
  (Lemma 11.5, `isRupert_type16_S2N2`); Proposition 11.V (`isRupert_type16_V`, `…Vσ`) from
  R1 (`type16_R1`), R2 (ii) (`type16_R2`) and Lemma 11.8 for `2 → 4`
  (`isRupert_type16_24`: the rim is the face `0235`).  Gale-form (mirror-invariant)
  wrappers end in `'`.  Not formalized: S2's T4 branch and S3 (Lemmas 11.7, 11.9, 11.10,
  T4 weak edges); that some clause always holds is open, so there is no
  `not_type16_of_isNopert`.
* §13 of `FEWER-FACES-PROOFS.md` (two-test certificates; `OctAxis.lean`), in Euclidean
  form (the metric of `ℝ³`). Theorem 13.7, the octahedral axis lemma
  (`isRupert_octAxis`): for an octahedron with an ordered axis `(a, a')`, a labelling
  `(b, b')`, `(c, c')` and the four Gale far-end inequalities
  `|[a b]| < |[a c]|`, `|[a b']| < |[a c']|`, `|[a' c']| < |[a' b]|`, `|[a' c]| < |[a' b']|`,
  the vertex crossing at `a'` (`a'bc`/`a'b'c'`, view `u₁ = axisView`, Lemma 13.5) or the
  one at `a` (`ab'c`/`abc'`) has a unimodal reduced polygon, so the octahedron is Rupert
  (Proposition 8.8 with Theorem 7.3, `isRupert_of_vertexView`), outside the special
  positions and without horizontal double normals at the two views. Each rim is a
  triangle (always unimodal) or a quadrilateral, unimodal unless its diagonals are
  depth-separated (`isRupert_axisTest_core`); both quadrilaterals failing is excluded by
  the angle lemma in shared-diagonal form (Lemma 13.2, Corollary 13.3:
  `depthSep_meet_sign`, `depthSep_det_sign`, `not_both_depthSep`) with the sign identity
  (Lemma 13.6, `axis_sign`, `axis_sign_two`, proved without the continuity step) and the
  cluster signs (Lemma 13.4, `cluster_signs`, every octahedron). The lift
  (Lemma 13.8 (i), (ii), clause AX): `isRupert_octAxis_lift` for `K = O ∪ {m}` with `m`
  hidden or a middle at the apex for both tests (`AxisExtra`). Not formalized:
  Observation 13.1, the general two-test remark, Lemma 13.8 (iii).
* §14 of `FEWER-FACES-PROOFS.md` (edge pairs, Lemma E; `EdgePair.lean`), in Euclidean form
  (depth `⟪·, u⟫` at the view `u = w − v` along the edge `vw`). Lemma E: at an edge crossing
  whose closings have the 4-corner rims `(v, a, c, b)` and `(w, a, c, b)`, if
  `[a b c v] [a b c w] ≤ 0` (the paper's (iii), or a planar closing) the two rims are not
  both depth-separated (`edgePair_not_both`, via `edgePair_param`: `0 ≤ λ ≤ 1 − s`), so one
  closing is unimodal (`edgePair_unimodal`); (ii) ⟺ (iii) (`edgePair_tri_iff`); the converse
  for depth functionals (`edgePair_converse`). Corollary 14.1 (`isRupert_edgePair`: strictly
  convex shadow, other points middles `EdgeMid` or hidden `EdgeHidden`, distinct depths, no
  horizontal double normal for either closing; one closing is `isRupert_edgePair_closing`,
  through `isRupert_quad_rim_int`) and its triangle case (`isRupert_edgeTri`). The wedge
  argument (`wedge_sep`) and Proposition 14.3 (E06): `0`, `6` strictly on opposite sides of
  `345` for every type 16 (`type16_sep06`), so the pair at `06` certifies `K` when `1`, `2`
  are strictly inside the shadow (`isRupert_type16_06`; `5` hidden too:
  `isRupert_type16_06_tri`). Not formalized: Lemma E′, Proposition 14.2, the metric part of
  the converse, Lemma V, Corollary V1, Observation 14.4.
* §15 of `FEWER-FACES-PROOFS.md` (type 24 outside `C̄ ∪ Σ_B`; `Type24.lean`). `Type24` gives the
  cap faces `012`, `016`, `126` at the vertex `1` and the side faces `236`, `046`, `025`; the
  oblique coordinates at `1` (`oblX0`, `oblX2`, `oblX6`, Cramer's rule; `Type24.rep`, the frame
  is nondegenerate by Cauchy–Binet, `Type24.det_ne`), the side coefficients
  `ω_xc = (X_x(g) + X_c(g) − 1) / X_y(g)` (`omega3`, `omega4`, `omega5`), every point beneath
  each side plane (`Type24.side236`: the face functional is `f(x 1)(1 − (X2 + X6 − ω3 X0))`),
  `Delta24`, the identity `(ω_g ω_h − 1)(ω_g ω_k − 1) − (1 + ω_g)² = ω_g Δ`
  (`omega_identity`, by `ring`) and `omega_prod_gt_one`. Theorem 15.4, the window triangle
  (`isRupert_type24_window`): if some `ω ≤ 0` or some `ω_g ω_h < 1`, `K` is Rupert with no
  exclusion, by Theorem 5 at a view `e_a + t e_b + ε e_c` in the open tangent cone at `1`
  (frame form `isRupert_window_frame`, `ε = 1 / (1 + |ω_ab|)` explicit). Lemma 15.5 with
  Theorem 15.7, case B (`isRupert_type24_S6`, `_S2`, `_S0`, `isRupert_type24_B`; frame form
  `isRupert_sideCrossing_frame`): at the side crossing `046/236` (view `view6`, oblique
  `(1 + ω4, 1 + ω3, ω3 ω4 − 1)`) the reduced polygon is the triangle `(0, 2, 6)`, `4` and `3`
  are middles over its sides, `1` and `5` are strictly inside (`L(5) = −c₅ Δ`); likewise
  `025/236` and `025/046`; a triangle test (`isRupert_vertexTri`: Proposition 8.8 with
  Theorem 7.3, the double-normal exclusion for the triangle only) with the exclusions
  explicit (`S6Free`, `S2Free`, `S0Free`: product `> 1`, distinct depths of `0, 2, 6`, no
  horizontal double normal). Corollary 15.8 (`isRupert_type24_outside_Cbar`; at the entry
  point `not_type24_outside_Cbar_of_isNopert`): outside `C̄ = {ω > 0, Δ ≥ 0}`, `K` is Rupert
  unless it is in region B (`RegionB24`) with no free side crossing (`Σ_B`). Not formalized:
  Lemma 15.2 at ties (an obtuse tie is free; distinct depths are assumed), the codimension
  of `Σ_B` (Lemmas 15.6, 15.7′), §§15.4–15.5 and region `C̄`.

**L12. The view along an edge between two quadrilaterals** (`EdgeView.lean`,
`QuadFacets.lean`; Theorems B, B′ of `FEWER-FACES-PROOFS.md` §4–5, in general
position)
* At the entry point, `not_four_quad_facets_of_isNopert`: a 7-point nopert in
  general position (`GenPos`: no two segments parallel or orthogonal) has no
  four quadrilateral facets. Via `isRupert_of_four_quad_facets`: two distinct
  facets share at most two points (`card_inter_le_two_of_facets`); a shared
  pair is a side, so no three sides meet at a vertex
  (`not_three_sides_at_vertex`) or form a triangle
  (`mem_triangle_of_three_sides`); a kernel-decided classification
  (`quad_facets_classify`) then gives the type-02 pattern, and Theorem B
  applies (`isRupert_of_type02Pattern`).
* Theorem B — `isRupert_type02`: seven points labelled as type 02, with the
  quadrilaterals 0134, 3456, 0235, 1246 as facets (supporting affine
  functions), 2 not in the hull of 0, 1, 5, 6, the edges 01 and 56 not
  parallel to 34 (G), and distinct depths along 34 (Z), are Rupert. Via
  `isRupert_type02_vertical` (edge 34 vertical) and `isRupert_type02_obl`
  (oblique frame) to `isRupert_type02_frame`.
* The cycle core — `cycles02_A?B?`: for each shape of the limit silhouette,
  the cycle in the dihedral wedge `W` has a unique local minimum or the one in
  `-W` a unique local maximum; with `isCyclicUnimodal_of_localMin_unique`
  (local extrema alternate) and the plane inequalities `plane_far`,
  `plane_mixed`.
* The tilt tests of Lemma 8.0 in oblique coordinates — `tiltSign_obl`, the
  six kinds `tiltOK_side1_off` … `tiltOK_farB`; the eight (shape, wedge) cases
  `rupert02_W_A?B?`, `rupert02_M_A?B?`.
* The chord — `sheets_on_chord`: the lower plane of 0235 and the upper plane of
  1246 both pass through 2, so 2 lies beyond the chord of the far vertices.
* Theorem B′ (type 05, the view along edge 12) — `isRupert_type05`: seven
  points labelled as type 05, with the quadrilaterals 1032, 6512, 0145 and the
  triangles 234, 246 as facets, 4 not in the hull of 0, 3, 5, 6, (G′), (Z′),
  are Rupert. The cycle core `cycles05_A?B?` replaces the second plane by the
  upper sheet (`sheet_up`, `sheet_contra`, `plane_both`); the eight frame
  lemmas of type 02 are reused unchanged (`isRupert_type05_frame`).

**Flat point sets** (`Planar.lean`)
* `isRupert_of_coplanar_of_not_collinear` — points in a plane, not all on a
  line, are Rupert.
* `not_isRupert_of_collinear` — a nonempty set of points on a line is not
  Rupert.
* `isRupert_empty` — the empty set is (vacuously) Rupert.

**Non-vacuity** (`Witnesses.lean`): explicit rational instances of every
hypothesis structure (`IsBicappedTetrahedron`, `IsCappedSquarePyramid` generic
and with `S₁S₄ ∥ S₂S₃`, `IsT4`, `IsT3` generic and with `BB' ∥ CC'`,
`IsOctahedron` with Condition A), each fed to its headline theorem (the
octahedron also to `isRupert_octahedron`).

## Modules

In import order.

| module | part | key statements |
|---|---|---|
| `Basic` | setting | `IsInwardAt`, `IsDoubleNormalDir`, `screenVel`, `isRupert_iff_shadows`, rotation invariance, `isInwardAt_iff_forall_normal` |
| `FirstOrder` | L1 | `eventually_forall_mem_interior`, `eventually_innerShadow_subset`, `isRupert_of_firstOrderInward` |
| `DoubleNormal` | L3, L4 | `exists_admissible_inward_field`, `isDoubleNormalDir_convexHull_cases`, `isDoubleNormalDir_proj_iff'` |
| `Coplanar` | L2, L5 | `exists_motion_of_admissible`, `admissibleViews`, `exists_firstOrderInward_of_plane` |
| `Pyramid` | waist lemma | `isRupert_of_waist`, `isRupert_bipyramid` |
| `Planes` | plane utilities | `exists_plane_of_coplanar`, `det4`, `sum_smul_mem_interior_convexHull` |
| `Crossing` | Theorem 5, Cor. 5.3, 5.4 | `isRupert_of_crossing`, `isRupert_of_admissibleViews_nonempty`, `isRupert_of_pyramid`, `isRupert_of_segment_crossing` |
| `FewVertices` | Cor. 5.6 | `isRupert_of_card_le_five` |
| `BicappedTetrahedron` | Cor. 5.7 | `isRupert_bicap_normalForm`, `isRupert_bicappedTetrahedron` |
| `SixVertices` | L6, coplanar cases | `isRupert_frustum`, `isRupert_parallelPrism`, `isRupert_cappedSquarePyramid` |
| `CycSeq` | Theorem 7.3, Steps 1–4 | sign-switch sequences, `forces_parallel` |
| `Polygon` | corner API | `IsCcwPolygon`, `normalConeAt`, `normalCone_decomp` |
| `Thm73` | Theorem 7.3, glue and Step 5 | `IsCyclicUnimodal`, `HasHorizontalDoubleNormal`, `IsCyclicUnimodal.noZig`, `IsCcwPolygon.hdn_of_parallel` |
| `BadViews` | Lemma 7.4 | `badDirs`, `exists_badDir_of_hdn` |
| `Perturb` | genericity | `IsCcwPolygon.mem_interior_iff`, `eventually_isCcwPolygon`, `exists_rotation_near_avoiding` |
| `Unimodal` | Lemma 7.1, Theorems 7.3, 7.5 | `exists_forces_of_not_firstOrderInward`, `isRupert_of_genericUnimodalView` |
| `Octahedron` | Cor. 7.8 | `IsOctahedron`, `isRupert_octahedron_conditionA` |
| `Prism` | Theorem 7.7 | `isRupert_translationPrism` |
| `Tilt` | Lemma 8.0, Cor. 8.0′ | `isRupert_of_tiltCert`, `eventually_tilted_cycle`, `isRupert_of_tilted_unimodal` |
| `RightPrism` | Theorem 8.1 | `isRupert_rightPrism`, `isRupert_translationPrism_all` |
| `L8Shapes` | Theorem 8.2, tools | `cmb`, `det3_cmb`, `NWS4`, `isRupert_cappedSquarePyramid_all` |
| `L8T4` | Theorem 8.3 | `IsT4`, `isRupert_T4` |
| `L8T3` | Theorem 8.4 | `IsT3`, `isRupert_T3` |
| `OctaTools` | L9 tools | `det3`/`cross` algebra, symmetries of `IsOctahedron` |
| `Oct9Axis` | L9, axis views | `isRupert_planar_equator`, `isRupert_of_touching_pair` |
| `Oct9Data` | L9, facets | `FacetFn`, `OctFacets` |
| `Oct9Quad` | Lemma 9.3 | `isRupert_quad_edge` |
| `Oct9Gale` | §9.4, §9.5 | `IsDep`, `galeD`, `not_bad_of_dep`, `facet_lt_of_dep`, `GaleData`, `arc_lemma`, `isRupert_octahedron_generic` |
| `Oct9Weak` | Lemma 9.11 | `isRupert_of_tilted_unimodal_σ`, `isRupert_weak_edge` |
| `Oct9Par` | §9.6 | `isRupert_octahedron_parallel` |
| `OctahedronAll` | Theorem 9.9 | `isRupert_octahedron` |
| `Planar` | flat sets | `isRupert_of_coplanar_of_not_collinear`, `not_isRupert_of_collinear`, `isRupert_empty` |
| `Witnesses` | non-vacuity | `witness_*`, `affineIndependent_of_det3` |
| `SixGale` | §10.1, Lemma 10.1, Prop. 10.2 | `IsDepOn`, `Six`, `GaleFrame`, `isFacetTriangle_of_gale`, `exists_split_of_no_partner`, `isRupert_of_all_partners` |
| `SixClass` | Lemma 10.3, Theorems 10.4, 10.0 | `NF`, `NF.isRupert`, `isRupert_split_coplanar`, `isRupert_of_card_le_six` |
| `FaceChain` | L11, the lower chain | `mem_convexHull_of_between`, `ConvPos`, `cross2_pos_of_consecutive'`, `exists_lowerChain'` |
| `FaceFive` | L11, Theorem A | `isRupert_edgeOn_dir`, `isRupert_cycle_edgeOn`, `isRupert_caseI`, `isRupert_caseII`, `isRupert_of_card_seven_of_facet` |
| `EdgeView` | L12, Theorems B, B′ (types 02, 05, general position) | `cycles02_A1B6`, `tiltSign_obl`, `isRupert_type02_frame`, `sheets_on_chord`, `isRupert_type02`, `cycles05_A3B6`, `isRupert_type05` |
| `QuadFacets` | L12, four quadrilateral facets | `card_inter_le_two_of_facets`, `quad_facets_classify`, `quadSidesOK_of_facets`, `isRupert_of_four_quad_facets` |
| `TriShadow` | L13, Lemma T (triangle shadow), oblique frame | `tri_localMax_unique`, `oblPt_inj`, `isRupert_triShadow` (no distinct depths needed: `isRupert_of_tilted_localMax`, `TriSeq`) |
| `TriShadow2` | L13, Lemma T over an edge (two vertices over the apex), oblique frame | `vert_tiltOK`, `isRupert_triShadow2` |
| `TriShadowChord` | L13, Lemma T′: `isRupert_triShadow` with a mixed tilt and the far-side test as `TiltOK`; a point on the far side hidden by the tilt | `isRupert_triShadow_tilt`, `chord_tiltOK` |
| `TriShadow2Chord` | L13, the same over an edge | `vert_tiltOK_tilt`, `isRupert_triShadow2_tilt` |
| `TriFaces` | L13, Lemma T over an edge or a vertex from the faces' chains, with interior points | `edge_core`, `isRupert_edge_frame`, `isRupert_vertex_frame` |
| `TriFacesChord` | L13, Lemma T′ from the faces' chains: one point on the far side | `isRupert_vertex_frame_chord`, `edge_core_chord`, `isRupert_edge_frame_chord` |
| `TriQuad` | L13, chains of quadrilaterals and triangles from a vertex or along an edge; two quadrilaterals sharing a vertex (Corollary T1), oblique frame | `quad_chain`, `chainOK_edge_p_up`, `tri_chain`, `triE_chain`, `ChainOK.far_eq`, `isRupert_twoQuads_frame` |
| `HullChain` | L13, upper and lower chains of any finite point set with distinct `t` and no three collinear (gift wrapping), also with two points over the apex | `ChainFrom`, `exists_chainFrom`, `exists_chainOK`, `exists_chainOK_edge` |
| `TriFacets` | L13, Lemma T at a vertex for any two facets, with interior points: frame, vertical, rotated, facet form | `isRupert_vertex_coords`, `isRupert_facets_vertex_vertical`, `isRupert_facets_vertex`, `isRupert_of_facets_vertex` |
| `TriFacetsChord` | L13, Lemma T′ at a vertex for any two facets (one off point on the far side): frame, vertical, rotated, facet form | `isRupert_vertex_coords_chord`, `isRupert_facets_vertex_vertical_chord`, `isRupert_facets_vertex_chord`, `isRupert_of_facets_vertex_chord` |
| `TriTie` | L13, Lemma T at the tie: one concave run (`localMax_unique_of_run`, `RunSeq`), Lemma T in every sector with four modes that allow z(xa) = z(xb) (`isRupert_triShadow_gen`), chains monotone at an extreme (`ChainOK.rise_of_far_top`, `fall_of_apex_top`), the frame to facet layers, and a triangle face settles the tie (`TriGenTri.tie`); the same over an edge (`isRupert_edge_frame_tie`, `TieHE`, `EdgeTie`), where a triangle face through the edge always settles it (`edgeTie_of_tri`) | `isRupert_vertex_frame_tie`, `TieH`, `isRupert_of_facets_vertex_tie`, `TriGenTie`, `TriGenTri`, `isRupert_of_facets_edge_tri`, `EdgePar` |
| `Forces` | L7, Lemma 7.1 at a view without a rotation or silhouette: if every force system (forces orthogonal to the view, `⟪F v, y - v⟫ ≤ 0` at test points, in equilibrium with zero torque about the view) vanishes, Rupert; for force-estimate arguments ("Lemma T at the tie, robust form") | `isRupert_of_no_forces`, `interior_proj_convexHull_nonempty`, `force_eq_zero_of_inside`, `force_mem_cone`, `det3_cramer` |
| `TieForces` | L13, Lemma T at the tie, robust form: the scalar core of the force argument (mass on the corners above the tie is `O(δ)`, the far end loses its edge force, Cramer on the far ends' generators and torques) | `tie_core`, `cramer3`, `cramer3_bound` |
| `TieRobust` | L13, Lemma T at the tie, robust form, geometric layer: tilted views `e_z + εv`, corner forces on their generators, the robust tie at one view and for all small tilts, Rupert (only test-point determinants and limits at `ε = 0` as hypotheses) | `tie_no_forces_at`, `tie_no_forces`, `isRupert_of_tie`, `isRupert_of_tilted_tie`, `force_eq_zero_of_left`, `IsForceSys`, `farDet` |
| `TieFrame` | L13, Lemma T at the tie, robust form, in the oblique frame of `isRupert_triShadow_gen` (same-sign sector, corners on one side of the tie, the far determinant `λμρA (r1·(b−a))`, `farDet_obl`; at a right angle, where it vanishes, `isRupert_of_tilted_tie_right` from `TieRight`, so `TieHR`/`TieHER` need only the tie), from chains at a vertex and over an edge, and through the coords, vertical, rotated and facet layers | `isRupert_triShadow_robust`, `isRupert_vertex_frame_tieR`, `isRupert_of_facets_vertex_tieR`, `TriGenTieR`, `TieHR`, `edge_robust_core`, `isRupert_edge_frame_tieR`, `isRupert_of_facets_edge_tieR`, `EdgeTieR`, `TieHER` |
| `TieRight` | L13, Lemma T at the tie, robust form, at a right angle of the far triangle (where `farDet` vanishes; FEWER-FACES-PROOFS.md, "Addendum: right angles"): torques about the other far end remove two unknowns, the corner generators are near `n2` (mass `O(δ²)`) or have nonnegative torque, the side generator's torque is `⟪a0 - a, w⟫⟪b - a, w⟫ = O(δ)` with a sign, and a `2 × 2` Cramer step finishes; scalar core, one view, small tilts, Rupert, both orientations | `tie_core_right`, `cramer2_bound`, `torque_about`, `tie_no_forces_at_right`, `tie_no_forces_right`, `isRupert_of_tie_right`, `isRupert_of_tie_right_neg` |
| `Transversal` | FEWER-FACES-PROOFS.md Proposition 8.7, sufficient direction: a small rotation (sense σ) about the non-horizontal line `{(c₀ + z c₁, z)}` moves a point `(p, z)` on the screen by `σ J (p − c₀ − z c₁)` (`screenVel_axis`); if this points strictly into the shadow at every point of `V`, i.e. the line meets each vertex's depth level inside its quarter-turned inward cone, `V` is Rupert (via Lemma 1); each vertex's condition is convex in the line's parameters in ℝ⁴, so by Helly it suffices that every 5 vertices admit a common line | `axisOmega`, `axisTau`, `screenVel_axis`, `isRupert_of_axis`, `isRupert_of_axis_image`, `convex_setOf_isInwardAt`, `isRupert_of_axis_helly` |
| `Chords` | FEWER-FACES-PROOFS.md Proposition 8.8 (faces seen edge-on cost nothing): at a view `u₀`, let each *middle* `m = a + s (b − a) + δ u₀` (`0 < s < 1`, `δ ≠ 0`) lie over a chord `[a, b]` whose ends move strictly to its inner side; if every other point has a local certificate of strict inward motion at `u₀` (the polytope without its middles is first-order free), `V` is Rupert. The tilt `ω × u₀ + η v′` hides each middle or exposes it as a corner with a positive chord test (the velocity is affine in the point: `det3_vel_middle`); this replaces the paper's choice of quadrant | `TiltCert.eventually_tilt`, `det3_vel_middle`, `exists_inner_ne_zero`, `ChordMiddle`, `eventually_tiltCert_middle`, `exists_tilt_chords`, `isRupert_of_chords` |
| `EdgeChords` | FEWER-FACES-PROOFS.md Theorem 8.9 with Lemma F (edge crossings: Lemma T over an edge with any far chain), in certificate form: two faces share the edge `vw`, `w = v − h u₀` (`h ≠ 0`, `u₀` along the edge), with far ends `A`, `B` and *middles* `c + s (A − c) + δ u₀` or `B + s (c − B) + δ u₀` (`c = v`, or `c = w` with `δ h < 0`; `EdgeMiddle`). If `K_v` (the hull without the middles and `w`) is first-order free at `u₀` (every other point has a `TiltCert`; `v` is the corner between `B` and `A` moving strictly inward; the far ends move strictly inward across the face sides), some tilt `u₀ + ε d` is free for all small `ε > 0` and `V` is Rupert. The tilt is chosen from the signs of `h G_j` (`G_j` the depth derivative of face `j`'s normal velocity): sector `S+` (`w` hidden), `S−` (`w` the corner between `B` and `A`), or a mixed sector near the boundary ray `h (A − v)` (resp. `h (B − v)`) with `w` a corner next to `v` on the apex edge. The unimodal corollary (Theorem 7.3 for `K_v`) is `isRupert_of_edgeChords_unimodal` in `UnimodalCert` | `edge_middle_sign`, `EdgeMiddle`, `eventually_tiltCert_axle_hidden`, `eventually_tiltCert_axle_corner`, `eventually_tiltCert_axle_after`, `eventually_tiltCert_axle_before`, `eventually_tiltCert_edgeMiddle`, `exists_tilt_axle`, `exists_tilt_edgeChords`, `isRupert_of_edgeChords` |
| `UnimodalCert` | Theorem 7.3 in certificate form, bridging it to Proposition 8.8 and Theorem 8.9: at a view `u₀` (`R u₀ = r e_z`, `r > 0`) where the silhouette is a strictly convex counterclockwise polygon `x` with cyclically unimodal depths and no horizontal double normal (other points strictly inside), some motion `(ω, τ)` has a `TiltCert` at every point and moves each corner strictly to the inner side of both its edges. Corners use their two neighbours; an interior point gets a corner certificate too (it need not lie strictly inside a triangle of points: the centre of a square), from a sign change of `cross2 (x l − q) ν` around the polygon, after perturbing `τ` so that its velocity `ν` is parallel to no `x j − q`. The bridge needs only some strictly inward first-order motion (`exists_tiltCert_of_firstOrderInward`, and likewise for the corollaries). Corollaries: Proposition 8.8 with `K′` (the points other than the middles) unimodal at `u₀` and the middles over its silhouette edges, and Theorem 8.9 with `K_v` unimodal at `u₀`, `v` a silhouette corner with neighbours `A`, `B` | `TiltCert.mono`, `exists_pos_succ_neg`, `exists_cross2_pos_of_mem_interior`, `det3_corner_pos`, `corner_ne_axle`, `exists_tiltCert_of_firstOrderInward`, `exists_tiltCert_of_unimodal`, `isRupert_of_chords_of_firstOrderInward`, `isRupert_of_edgeChords_of_firstOrderInward`, `isRupert_of_chords_unimodal`, `isRupert_of_edgeChords_unimodal` |
| `DepthSeparated` | FEWER-FACES-PROOFS.md Theorem 8.10 (depth-separated parallel pair), generalizing Theorem 7.3: a ccw strictly convex polygon with an edge `e = [p a, p (a + 1)]` and a corner `c` with `−n_e ∈ N_c`, the corners from `c` to `a` strictly on one side of the level `z c` and those from `a + 1` back to `c` strictly on the other (`IsDepthSeparatedPair`). Corner forces in the normal cones with zero sum and zero depth moment are all parallel to `n_e` (the edge-force proof: `E2 − z_c E1` crossed with `n_e` is a sum of terms of one sign); with zero torque and not all zero they give a horizontal double normal. The paper's `−n_e ∈ int N_c` (single parallel ray) is not needed for this. Rupert form at a view, certificate form (via `exists_tiltCert_of_firstOrderInward`), and Proposition 8.8 / Theorem 8.9 with a depth-separated `K′` / `K_v` | `IsDepthSeparatedPair`, `IsCcwPolygon.incr_outNormal`, `forces_parallel_of_depthSeparated`, `hasHorizontalDoubleNormal_of_forces_depthSeparated`, `exists_firstOrderInward_of_forces_hdn`, `exists_firstOrderInward_of_depthSeparated`, `isRupert_of_depthSeparatedView`, `exists_tiltCert_of_depthSeparated`, `isRupert_of_chords_depthSeparated`, `isRupert_of_edgeChords_depthSeparated` |
| `ExtremeRays` | CRIT5-WRITEUP.md §4 (the closed freedom criterion for small silhouettes): corner forces of a ccw strictly convex polygon as nonnegative loads on *slots* (corner, edge normal) with columns `(n, z n) ∈ ℝ⁴` (E1, E2) and torques `p × n`. A linear functional positive on every *extreme ray* (nonzero balanced load of minimal support) is positive on every nonzero balanced load; extreme rays load at most 5 slots. Closed (Cramer) form: with full rank, every extreme ray is `ε λ(T)` for five slots `T` with sign-consistent Cramer coefficients `λ_r = (−1)^r Δ_r` (`Δ` the 4×4 minors, closed form by the Plücker relation), its torque the 5×5 determinant. `RaysFree` (every extreme ray has torque of one sign `σ`) or `CramerCert` (the closed test) makes the silhouette first-order free, with no exclusion of horizontal double normals; any `k` (for `k ≤ 5`: ≤ 252 five-slot sets). Rupert form at a view, certificate form, and Proposition 8.8 / Theorem 8.9 with `K′` / `K_v` passing the test. Not formalized: the converse, Theorems A and B, the parallel/level/mixed classification | `IsBalancedSlots`, `IsExtremeSlots`, `pos_of_extremeSlots`, `IsExtremeSlots.card_support_le`, `cramerCoeff`, `cramerTorque`, `sum_cramerCoeff_smul`, `cramerTorque_eq_det`, `pos_of_cramer`, `slotNormal`, `slotCol`, `slotTorque`, `exists_slots_of_forces`, `RaysFree`, `torque_pos_of_extremeRays`, `raysFree_of_five_slots`, `CramerCert`, `cramerCert_raysFree`, `det_slotCols`, `exists_firstOrderInward_of_torque_ne_zero`, `isRupert_of_raysFreeView`, `exists_tiltCert_of_raysFree`, `isRupert_of_chords_raysFree`, `isRupert_of_edgeChords_raysFree` |
| `Parity` | FEWER-FACES-PROOFS.md Proposition 8.2, discrete core: a sequence of nonzero reals ending at the negative of its start changes sign an odd number of times (the rotating-calipers walk over antipodal vertex pairs, one step per edge, changes the sign of the depth difference exactly at the parallel systems; the walk itself is not yet formalized) | `odd_card_sign_changes` |
| `Global` | Global passages (not near the identity pose): a pose is a passage if every inner vertex is a combination of the outer projected vertices with all weights positive (the exact fixed-pose formulation; the base for anchored poses such as the corner placement) | `isRupert_of_pos_combinations`, `outerShadow_convexHull` |
| `Shear` | The torque of a force system balanced in E1, E2 is unchanged by shearing the shadow (`p ↦ p + z a + b`), i.e. the same in every view; in the view along the segment of two corners it is the moment of the other forces about their common point; with forces at three depths the group resultants are parallel and the torque is a signed triangle area in the (depth, offset) plane (rigidity criterion for non-unimodal silhouettes, FEWER-FACES.md; FEWER-FACES-PROOFS.md Prop. 8.3) | `sum_cross2_shear`, `sum_cross2_collapse`, `three_level_resultants`, `three_level_torque` |
| `ParallelFar` | Segments parallel to the view line at a far end (codimension-2 tail): `tiltOK_farComp1/2` (a vertical companion of a far end passes the far-edge test under a tilt ratio leaning toward the other face), chains `ChainOKc` with `exists_chainOKc` (points may share verticals), the vertex and edge frames with companions | `ChainOKc`, `exists_chainOKc`, `vertex_core_par`, `isRupert_vertex_frame_par`, `edge_core_par`, `isRupert_edge_frame_par` |
| `ParallelFacets` | The vertex bridge without the parallel-segment hypothesis: coordinates, vertical, rotated and facet layers; `TriGenFarP` (distinct far depths, one far end a single vertex) | `isRupert_vertex_coords_par`, `isRupert_facets_vertex_par`, `TriGenFarP`, `isRupert_of_facets_vertex_par` |
| `TriFacetsEdge` | L13, Lemma T over an edge for any two facets, with interior points: frame, vertical, rotated, facet form | `orient_ne_of_frame1'`, `isRupert_edge_coords`, `isRupert_facets_edge_vertical`, `isRupert_facets_edge`, `EdgeFar`, `EdgeFar.of_injOn`, `isRupert_of_facets_edge` |
| `Type10` | L13, Theorem E (type 10) from Lemma T by facet-functional coordinates; Cramer for affine functionals, proportional functionals | `affine_cramer`, `affine_vanish3`, `vanish3_ratio`, `isFacet_of_index`, `isRupert_type10` |
| `Type19` | L13, Theorem F (type 19), same method | `isRupert_type19` |
| `Type13` | L13, Theorem G (type 13), same method | `isRupert_type13` |
| `Type17` | L13, Theorem H (type 17), same method | `isRupert_type17` |
| `Type27` | L13, Theorem I (type 27), same method, three views | `isRupert_type27` |
| `Type23` | L13, Theorem J (type 23), same method, three views | `isRupert_type23` |
| `Type25` | L13, Theorem K (type 25), same method, three views | `isRupert_type25` |
| `Type26` | L13, Theorem L (type 26), same method, with an automorphism | `type26_core`, `isRupert_type26` |
| `Type12` | L13, Theorem M (type 12), same method | `isRupert_type12` |
| `Type22` | L13, Theorem N (type 22), same method | `isRupert_type22` |
| `Type28` | L13, Theorem O (type 28), same method | `isRupert_type28` |
| `Type05` | L13, type 05 by Lemma T (facet level), same method | `isRupert_type05_facets` |
| `Type08Lemmas` | Type 08 (`FEWER-FACES-PROOFS.md` §10), the lemmas: the cap `d` over the octahedron `K − 2`; coordinates in a plane from affine functions; Lemma 3 (single-plane form of Lemma 9.5); Lemma 4 (the cap in the axis view) with its facts (i)–(iii); Lemma 9.7 as a dependency; Lemma 9.6 as an equivalence and Lemma 1 (a), (b); Lemma 1 (c); Lemma 2; Lemma 6; Lemma 7; the T4 edge not bad | `IsCap`, `coords_of_affine3`, `not_bad_of_crossing`, `not_bad_of_inTri`, `inTri_cap_BD`, `inTri_cap_AB`, `IsCap.axis_facts`, `inTri_of_dep`, `facet_lt_iff_of_dep`, `far_end_Qbc_iff`, `far_end_Qab_iff`, `nws4_of_planar_quad`, `IsCap.Qac_coords'`, `IsCap.Qac_nws4`, `IsCap.middle_Qbc`, `type08_signs`, `type08_lemma6`, `type08_lemma7`, `type08_t4_not_bad` |
| `Type08Cases` | Theorem 8.9 with a unimodal `K_v` from determinant tests at an edge view (no rotation in the statement); type 08, cases N2 (Lemma 9.3 with a middle) and Q (`K_d` the face `Q_ac`) | `NoHDNAt`, `isRupert_of_edgeView`, `isRupert_quad_edge_middle`, `isRupert_type08_Q` |
| `Type08T4` | Type 08, case T4 (Lemma 5): the claim of Lemma 9.3 from one face, the closing by `x`, the T4 rim in coordinates | `quad_lower_of_face`, `nws4_closing_x`, `t4_dets`, `isRupert_type08_T4` |
| `Type08` | Theorem 10.1 (type 08): the normalized case analysis, the relabelling by Lemma 6 (`S3` and mirrored Gale vectors), the facet form (the cap from the facets, `exists_type08_cap`) | `NoPlaneParallel`, `OctFacets.isOctahedron`, `isRupert_type08_normalized`, `isRupert_type08`, `exists_type08_cap`, `isRupert_type08_facets` |
| `Slide` | §10 addendum (T1), Lemma C: Proposition 8.8 with one face at a view from determinant tests, either orientation; Lemma 7.4 by edges (a horizontal double normal joins two rim edges with meeting depth intervals and lies on the circle of a direction of the pair); the slide along a face circle `u₀ + t e`, `t → 0⁺`, with `NoBadNormal` in place of strict depths and of the double-normal exclusion; unimodality along the slide | `pairDirs`, `EdgesApart`, `exists_pairDir_of_hdn`, `NoBadNormal`, `isRupert_of_chordView_or`, `isRupert_of_slide`, `isRupert_of_slide''`, `SlideTest`, `StrictUnimodal`, `eventually_unimodal_of_strict` |
| `Type08Slide` | Type 08, the cases of Theorem 10.1 by slides (Lemma C) and Lemma H's five-corner rims: N2 in an octahedron with one more point (tests in either orientation, the closing by `x` with the triple-tie exclusion), T4 and Q in the frame `d; a, c, b` | `quad_edge_tests_or`, `nws4_closing_oct`, `isRupert_quad_edge_middle_slide`, `isRupert_quad_edge_middle_five`, `isRupert_t4_slide`, `isRupert_t4b_five`, `isRupert_t4d_five`, `isRupert_q_slide` |
| `Type08Tie` | Type 08, Lemma X: the routes at the far-end ties `T`, `T'` (four-corner slides with a middle next to a far end, five-corner rims with a poked-out vertex) | `isRupert_kb_four`, `isRupert_kd_four`, `isRupert_r2pp`, `isRupert_r2p`, `isRupert_r4pp`, `isRupert_r4p` |
| `Type08Codim` | Type 08, Theorem 10.1′ (Lean form) without planar equators: the far-end identity at the ties (Gale), `b'` a corner in the T4 case, the hypotheses per labelling, the case analysis, the relabelling, the facet form | `type08_T_far`, `type08_T'_far`, `t4_kappa_pos`, `Type08Gen`, `Type08GenAll`, `isRupert_type08_slide_core`, `isRupert_type08_slide`, `isRupert_type08_slide_facets` |
| `Type08Flat` | Type 08, Lemma K (one planar equator): the crossing diagonals of a planar equator, Lemma 7's quad edge from `(G4)`, the signs when `κ_b = 0`, the relabelling, the facet form | `flat_cross`, `not_bad_of_cross`, `type08_quad_edge`, `flatB_signs`, `isRupert_type08_flatA`, `isRupert_type08_flatB`, `isRupert_type08_flat`, `isRupert_type08_flat_facets` |
| `Type29Lemmas` | Type 29 (`FEWER-FACES-PROOFS.md` §12, Theorem P), the reusable lemmas for an octahedron with one more point: Lemma 1 (certification without a crossed pair: a quad edge whose tail is an inner vertex of its third pair, `[p x] [x x'] < 0`, is not bad; Lemma 9.7 via `inTri_of_dep` and §10's Lemma 3), Lemma 2 (exact lift: a middle or hidden extra point leaves the reduced polygons, and Lemma 9.3's unimodal closing, unchanged; through `isRupert_of_edgeView`, i.e. `isRupert_of_edgeChords_unimodal`), a hidden point from the facets, both together | `quad_edge_sep`, `inner_dep_signs`, `not_bad_of_inner`, `QuadMiddle`, `QuadHidden`, `isRupert_quad_edge_lift`, `quadHidden_of_beneath`, `isRupert_inner_quad_edge_lift` |
| `Type29Lift` | Type 29, Lemma 3 (b) with `t > 1` (the cap is the far end, `5` the middle): the octahedron's shadow tests in either orientation, the tests at the cap, a point inside a quadrilateral is on the positive side of a line through a vertex (barycentric identity), the closing of Lemma 9.3 for any 4-cycle or a triangle (either orientation), step 3 (the up face `356` rules out `K`-badness), the lift | `quad_edge_testsσ`, `cap_testsσ`, `det3_bary`, `inside_line_pos`, `isRupert_closing_quad`, `isRupert_closing_quadσ`, `isRupert_tri_viewσ`, `lift_far_not_bad_core`, `isRupert_lift_far` |
| `Type29` | Type 29, Theorem P of §12 (partial): the cap `IsCap29` over `O = K − 6` and `σ = (0 2)(4 5)`, Lemma 0 (b) (coordinates `s, t`), Lemma 3 (quad edges at `1` lift: `14`, `41`, `15`, `51`), Lemma 4 (the cap is hidden at `0→3`, `0→5`, `2→3`, `2→4`), clauses C1, C2 (`K − 5`; `K − 4` by `σ`), C3, and Theorem P; no `not_type29_of_isNopert` (that some clause holds is open) | `IsCap29`, `IsCap29.coords`, `isRupert_type29_14`, `isRupert_type29_41`, `type29_hidden_03`, `type29_hidden_05`, `Type29C1`, `Type29C2`, `Type29C3`, `isRupert_type29_C1`, `isRupert_type29_C2`, `isRupert_type29_C3`, `isRupert_type29_P` |
| `Type16` | Type 16, Lemma 11.U and Corollary 11.Ua of `FEWER-FACES-PROOFS.md` §11 addendum: screen coordinates of an edge view from two face functionals, the rim tests by `det3_frame`, part (b) in reals, the closing decision, the core in coordinates and from facets; `Type16` (facets), `σ = (0 6)(1 2)`, `MidOf`, "35 is bad", the far ends of `0235`, `1356` | `affine_frame3`, `det3_frame`, `frame_coords`, `isRupert_quad_rim`, `lemmaU_b_real`, `lemmaU_nws4`, `lemmaU_coords`, `lemmaU_facets`, `Type16`, `Type16.sigma`, `MidOf`, `Type16Bad35`, `plane_quad_coords`, `quad_middle`, `isRupert_type16_35`, `type16_not_bad35_of_far`, `type16_not_bad35_of_acute` |
| `Type16M` | Type 16, Theorem M′ (conditional): the octahedral region `Oct16`, Lemma 11.1 (`5*`, `K*` type 08), S1 at `ℓ` (third quadrilateral, T4 case in `K*`, N2), S2's N2 branch (Lemma 11.5), Proposition 11.V (R1, R2, Lemma 11.8 at `24`), Gale-form wrappers, `Type16Clause` and the theorem; no `not_type16_of_isNopert` | `Oct16`, `Oct16.five_beyond`, `Oct16.star`, `Oct16.facets`, `Oct16.isCap`, `middle_Qbc_of`, `isRupert_type16_N2`, `type16_not_bad35_thirdQuad`, `t4_not_bad'`, `type16_not_bad35_T4`, `type16_lemma5_mid`, `isRupert_type16_S2N2`, `isRupert_quad_rim_coords`, `isRupert_type16_24`, `type16_R1`, `type16_R2`, `isRupert_type16_V`, `Type16Clause`, `isRupert_type16_M` |
| `OctAxis` | `FEWER-FACES-PROOFS.md` §13 (two-test certificates), Euclidean form: the angle lemma for 4-corner rims (Lemma 13.2, Corollary 13.3: depth-separated diagonals whose projections meet along both views force the sign of `⟪u₁, u₂⟫`; shared-diagonal form), the cluster signs of every octahedron (Lemma 13.4), the views and middles (Lemma 13.5), the sign identity (Lemma 13.6, by the dependencies `[a ·]`, `[b ·]` and Plücker, no continuity step), Proposition 8.8 with Theorem 7.3 at a vertex view from determinant tests, the test at `a'` (triangle or quadrilateral rim; extra points hidden or middles at the apex), Theorem 13.7 (the octahedral axis lemma) and the lift 13.8 (i), (ii) to `K = O ∪ {m}` | `dep_eq_zero_of_two`, `galeD_ne_zero`, `pole_signs'`, `cluster_signs`, `axisView`, `axisView_eq_neg`, `axis_sign`, `axis_sign_two`, `SegMeet`, `DepthSep`, `depthSep_meet_sign`, `depthSep_det_sign`, `not_both_depthSep`, `axis_test_facts`, `isRupert_of_vertexView`, `AxisHidden`, `ApexMid`, `AxisExtra`, `overlap4_of_not_depthSep`, `isRupert_axisTest_core`, `segMeet_of_sides`, `axisTest_meets`, `isRupert_axisTest`, `isRupert_octAxis_gen`, `isRupert_octAxis`, `isRupert_octAxis_lift` |
| `EdgePair` | `FEWER-FACES-PROOFS.md` §14 (edge pairs), Euclidean form: Lemma E (two 4-corner closings at an edge crossing along `vw`, view `u = w − v`; `[a b c v] [a b c w] ≤ 0` excludes both rims being depth-separated, so one closing is unimodal), the parameter form, (ii) ⟺ (iii), the converse for depth functionals, Corollary 14.1 (Theorem 8.9 with Theorem 7.3 for either closing, middles and hidden points allowed; triangle closings), the wedge argument and Proposition 14.3 (E06: `[3450] [3456] < 0` on every type 16; the pair at `06` certifies `K` when `1`, `2` are hidden) | `edgePair_param`, `edgePair_not_both`, `edgePair_unimodal`, `SegMeetsTri`, `edgePair_tri_iff`, `edgePair_converse`, `EdgeHidden`, `EdgeMid`, `isRupert_edgePair_closing`, `isRupert_edgePair`, `wedge_sep`, `type16_sep06`, `isRupert_type16_06`, `TriHidden`, `isRupert_edgeTri`, `isRupert_type16_06_tri` |
| `Type24` | `FEWER-FACES-PROOFS.md` §15 (type 24 outside `C̄ ∪ Σ_B`): oblique coordinates at the cap `1` by Cramer's rule, the side coefficients `ω` and `Δ`, the window triangle (Theorem 15.4, Theorem 5 at a view in the tangent cone), the side crossings as triangle tests (Lemma 15.5, Theorem 15.7), Corollary 15.8 | `cramer_vec`, `isRupert_vertexTri`, `isRupert_window_frame`, `isRupert_sideCrossing_frame`, `Type24`, `omega3`, `Delta24`, `omega_identity`, `isRupert_type24_window`, `isRupert_type24_B`, `isRupert_type24_outside_Cbar` |
| `TriBridge` | L13, Corollary T1 from facets: convex position of four points, the vertical and general bridges | `convex_four`, `isRupert_twoQuads_vertical`, `isRupert_twoQuads`, `TriGen`, `TriGenFar`, `TriGen.far`, `isRupert_of_two_quad_facets_vertex` |

## Formalization choices

* **Inwardness.** `IsInwardAt S p d := ∃ ε > 0, p + ε d ∈ interior S`, so no
  description of polygons by inequalities is needed (Mathlib has no
  Minkowski–Weyl).  It is automatic at interior points, so `FirstOrderInward`
  quantifies over all of `V` (`firstOrderInward_iff_frontier`).  For convex
  sets it agrees with the normal-cone description
  (`isInwardAt_iff_forall_normal`).
* **Double normals** use the general definition (a chord `[a, b]` with
  `b − a ∈ N(b)` and `a − b ∈ N(a)`) in any real inner product space, with no
  special case for triangles.
* **Views.** Everything first-order happens in the standard view (`proj_xy`,
  depth = coordinate 2); a general view is reduced to it by a rotation
  (`exists_rotation_to_ez`, `isRupert_of_isRupert_image_rotation`).
* **Rotation curve.** Lemma 1 holds for any matrix curve with `R 0 = 1` and
  `R' 0 = [ω]×`.  The passages use the Cayley curve `rotCurve` (rational, in
  SO(3) for every parameter) rather than the matrix exponential, for which
  Mathlib lacks `det (exp A) = exp (tr A)`.
* **Coplanar theorem.** `W ⊆ V` is arbitrary (not `V ∩ Π`), and there are no
  vertex or convex-position hypotheses.  Cor. 5.4 is stated with the crossing
  hypothesis (the segment `DE` meets `relint conv W`), not with "opposite
  sides, no common face", which would need polytope face theory.
* **No combinatorial types.** Cor. 5.6 uses Radon's theorem
  (`radon_partition`); the per-type theorems take facet hypotheses
  (`IsFacetTriangle`: a strict supporting plane), and L10 derives them from
  signs of affine dependencies.
* **Not formalized:** the converse (obstruction) directions of L2 and L3,
  which no Rupert theorem needs.
