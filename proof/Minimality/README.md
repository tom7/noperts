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
  `246`). With this, every type proved on paper (24 of 29) is excluded at the
  facet level in general position.

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
