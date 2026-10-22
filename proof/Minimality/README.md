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
* Theorem 18.3 (Theorem 7.3 with ties, `FEWER-FACES-PROOFS.md` §18.3;
  `RobustUnimodal.lean`) — `hasHorizontalDoubleNormal_of_forces_robust`,
  `exists_firstOrderInward_of_robustUnimodal`, `isRupert_of_robustUnimodalView`: the depths
  need only be *robustly unimodal* (`IsRobustUnimodal`: (R1) no two weak peaks, (R2) no three
  equal, (R3) no level pair inside a monotone run, stated for any four positions in cyclic
  order).  The core is `forces_parallel_weak` (Steps 2–4 with weakly monotone runs; a
  weightless stretch of the force polygon is excluded by (R2), (R3), `deg_lemma_weak`).
  Sources: `IsCyclicUnimodal.isRobustUnimodal`, `isRobustUnimodal_three` (triangles not all
  level), `IsCcwPolygon.isRobustUnimodal_affine` (planar rims: a nonconstant affine depth on a
  strictly convex polygon), `isRobustUnimodal_of_single_tie` (Lemma 18.4 (α): unimodal on both
  sides of one tie), `isRobustUnimodal_quad` (4-cycles, `QuadTie`, `RobustAxis.lean`).
  Cyclic subsequences: `IsRobustUnimodal.comp` (`CycBetween`), with
  `IsCcwPolygon.cross2_fan_pos` (corners in cyclic order are counterclockwise).
  Certificate forms (`RobustCert.lean`): `exists_tiltCert_of_robustUnimodal`,
  `isRupert_of_chords_robustUnimodal`, `isRupert_of_edgeChords_robustUnimodal`,
  `isRupert_of_uniform_doubles_robustUnimodal` (Theorem 18.1 in its tie form),
  `isRupert_of_edgeView_robust`, `isRupert_of_vertexView_robust`,
  `isRupert_of_edgeView_uniform_robust`.
* Lemma E with ties and general position up to single ties (`RobustEdge.lean`; §14 with
  §18.3–18.4) — `edgePair_nws_core`, `edgePair_nws`, `edgePair_robust`: at an edge crossing with
  `[a b c v] [a b c w] ≤ 0` and a strictly convex shadow, one of the rims `(v, a, c, b)`,
  `(w, a, c, b)` has diagonals that are not even weakly separated (`NWS4`), hence is robustly
  unimodal (`NWS4.isRobustUnimodal`), unless the three far depths are equal: every other tie is
  allowed (the depth chain `d_v ≤ e ≤ d_w` over the interior crossing of the diagonals,
  `segMeet_strict`).  Rupert forms: `isRupert_edgePair_robust`, `isRupert_edgeTri_robust`
  (triangles: not all three depths equal), `isRupert_quad_rim_int_robust`,
  `isRupert_edgePair_uniform_robust` (with the uniform tilt).  The octahedral quads of tiers Q, H
  with ties: `isRupert_quad_edge_lift_tie` (the closing of Lemma 9.3 is `NWS4`; only the far ends
  both at the depth of `y'` is excluded, `nws4_closing_x_tie`); planar 4-corner rims:
  `nws4_of_planar_quad_tie`.  `GenPosTie` (no two segments parallel, at most one tied pair at
  the view along each segment, `OneTieAt`: both codimension 2), `GenPos.genPosTie`,
  `GenPosTie.noTriple`, `GenPosTie.touch_oct`.  Robust unimodality by perturbation
  (`isRobustUnimodal_of_perturb`: a rim with one tied pair, unimodal along a family of small
  perturbations that separates the pair from both sides; Lemma 18.4 (α) for an explicit family),
  used for the pentagon of type 21's `Y` (`type21_Y_robust`, `isRupert_quint_rim_robust`), and
  its open-criterion form `isRobustUnimodal_of_nhds` (the pentagons of type 16's `Ω`).
* Lemma 18.2 (the limit lemma, at the shape's own metric; `LimitCert.lean`) —
  `cycBetween_of_tendsto` (18.2 (a): the corner labels of the limit are a cyclic subsequence
  of the labelled rim), `isRobustUnimodal_cornerRim_of_tendsto` (18.2 (b) with distinct
  depths), `isRobustUnimodal_cornerRim_of_tendsto_single_tie` (18.4 (α)),
  `isRobustUnimodal_cornerRim_or_of_tendsto` (pairs, 19.7 (a)); Rupert forms
  `isRupert_of_limitCertificate` and `isRupert_of_limitCertificate_tie` (with 18.1 and 18.3:
  shapes `K_n → K` certified by one labelled test, `K`'s corner rim with distinct depths, or
  one tie approached from both sides, and no horizontal double normal).  Not formalized:
  metric-freeness across metrics and the codimension count.
* Lemma 18.2 (a)–(c) with the corner rim constructed (`LimitRim.lean`):
  `isRupert_of_tendsto_rimCert` — shapes `K_n → K` frequently carrying one frame-free
  labelled certificate (`RimCertAt`: strictly convex counterclockwise determinant tests at the
  view, every point weakly inside, robust depths), views converging to `u ≠ 0`, the ties of
  `K`'s labelled depths kept along the sequence; then `K` (no point inside a segment of two
  others, not in a plane, no horizontal double normal at `u`) is Rupert.  Steps: hulls in
  support-function form pass to limits (`SuppIn`, `suppIn_of_tendsto`), weak convexity in the
  limit (`cyc_nonneg_of_tendsto`), robust unimodality with kept ties
  (`isRobustUnimodal_of_tendsto_ties`), the rim only loses corners (`exists_cornerRim`: the
  least label over each extreme point, Krein–Milman for the hull; `cycBetween_iff_val`,
  `exists_enum`, `cross2_ne_zero_of_extremePoints`), every hull point is interior or on a
  closed side (`IsCcwPolygon.mem_side_of_mem_convexHull`).  Point-form certificates
  (`RimCert.lean`): `RimCertPts`, `RimCert`, `rimCertPts_of_class`, `rimCert_edgePair_robust`,
  `rimCert_edgeTri_robust`, `TieSeg`.  The existence of limit certificates is done for type 16
  (`Type16Limit.lean`, below).

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
  `246`). With this, every type proved on paper (now 27 of 29, with types 08, 16 and 21) is excluded
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
  `Type08Slide.lean`, `Type08Tie.lean`, `Type08Rd.lean`, `Type08R0.lean`, `Type08Codim.lean`,
  `Type08Flat.lean`): type 08 without `GenPos`, `NoPlaneParallel` and `NoHDNAt`.  The
  hypotheses, per labelling of Lemma 6, are collected in `Type08Gen` (`Type08GenAll`:
  all six labellings); `O` may have one planar equator.  Lemma C (`isRupert_of_slide`):
  slide the view along the great circle of a face through the named crossing; the face's middles lie over its side
  (Proposition 8.8 with one face), the rim is `K_v`'s, depth ties and horizontal double
  normals occur at isolated views unless a direction of a pair of rim edges with
  meeting depth intervals (Lemma 7.4 by edges, `exists_pairDir_of_hdn`, `pairDirs`) is
  normal to the face (`NoBadNormal`).  The case slides: N2 `isRupert_quad_edge_middle_slide`,
  T4 `isRupert_t4_slide`, Q `isRupert_q_slide` (in the frame `d; a, c, b`, all tests
  multiples of `E = det3 (a − d) (c − d) (b − d)`).  Lemma H for the closings with one
  circle: the five-corner rim along the other face (`isRupert_quad_edge_middle_five`,
  `isRupert_t4b_five`, `isRupert_t4d_five`; strictly unimodal, `StrictUnimodal`, or, Lemma
  H (c), with a depth-separated pair: Theorem 8.10 along the slide, `DepthSepAt`,
  `UniOrSep`, `isRupert_of_slide_uos`, `SlideDS.lean`), and
  Theorem R of A.10 for its two-peaked piece `R_d` (`Type08Rd.lean`): Lemma R2's
  slot-weight certificate of the limit system (`rd_limit_cert`) becomes a motion that is
  strictly inward at all ten slots (`TiltCert`) at the views `u₀ + κ e_k` in `F_k`'s plane
  for all small `κ > 0` (`eventually_slot`: zero at `κ = 0` with a positive first-order
  term), with `F_k`'s middles over its side (`isRupert_of_chords`); in coordinates
  `isRupert_rd_std`, for any orthonormal frame `isRupert_rd`, and for N2–`K_c` and
  T4–`K_b` `isRupert_quad_edge_middle_rd`, `isRupert_t4b_rd`, with (H1)–(H4) as the
  hypothesis `RdRim`.  Lemma R0 (`Type08R0.lean`) derives `RdRim` on `R_d` (`RdCond`: `g`
  parallel to the face and not to the chord `[v, f]`, a horizontal double normal
  perpendicular to the face, five distinct depths, not strictly unimodal; the third
  alternative in `Type08Gen.slideN2c`, `slideT4b`): (H1) from the two peaks, the unimodal
  `K_v`, the weak saddle of `K_w` and the claim of Lemma 9.3/5 (`rd_depths`), (H2) from the
  face `Φ` (`rd_coords`), (H4) from Lemma 9.7 / (T2) with `κ_a > 0` (`type08_rd_sides`), in
  the frame of A.10 (`exists_rdFrame`); `rdRim_of_R0`, `isRupert_quad_edge_middle_rdCond`,
  `isRupert_t4b_rdCond`.  For T4–`K_d`, `R_d` is empty (A.10's remark: `g = b'c ∥ [d, a]`,
  and with a weak saddle of `K_b` the rim rises to its only peak `b'`; `t4d_five_strict`,
  `t4d_rd_empty`), so on its type-(d) surface `Type08Gen.slideT4d` asks only that the
  five-corner rim has no tie between neighbours (`t4d_slide_of_par`).
  Lemma X at the far-end ties `T` (`β₂ = 1`) and `T'` (`α₁ = 1`): the far end of the
  other face from the identity `α + β = κ_b` (`type08_T_far`, `type08_T'_far`), and the
  routes R1/R4′ (`isRupert_kb_four`), R2′/R3 (`isRupert_kd_four`), R2″ (`isRupert_r2pp`),
  R2′ with `a'` poking out (`isRupert_r2p`), R4″ (`isRupert_r4pp`), R4′ with `a` poking out
  (`isRupert_r4p`); which route applies is derived from the depths as in the addendum
  (`Type08X.lean`: `isRupert_routeT`, `isRupert_routeT'`), leaving the generic conditions
  `RouteT`, `RouteT'`.  The persistent double normal of a poked-out short edge (parallel to
  the face) is excluded through its feet (`NoBadNormalR`, `NoFeet`; Lemma 7.4 by edges with
  feet, `exists_pairDir_of_hdn'`), so R2″ and R4″ are needed exactly where it occurs, and
  there their rims are strictly unimodal.
  Lemma G: in the T4 case `b'` is a corner (`t4_kappa_pos`), the other (G1) coincidences
  never occur in the frame.  Lemma K (`isRupert_type08_flat`): with `κ_X = 0`, `X` takes the
  role `a` (`isRupert_type08_flatA`: Lemma 7's quad edge from `(G4)`, `type08_quad_edge`;
  "not bad" from the crossing diagonals of the planar equator, `flat_cross`,
  `not_bad_of_cross`) or `b` (`isRupert_type08_flatB`: signs from `(G4)`, `flatB_signs`;
  the T4 case empty).  The hypotheses left in `Type08Gen` are generic conditions (each
  fails only in codimension 2, by the addendum's count, A.7); that count is not
  formalized.
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
* §21 of `FEWER-FACES-PROOFS.md` (type 29 by octahedron class: the covered classes K4 and K3;
  `Type29NF.lean`, `Type29K4.lean`, `Type29K3.lean`, `Type29Cover.lean`, `Type29Facets.lean`).
  Normal coordinates (Lemma 21.1): `NF29` (`1 = 0`, `4 = e₁`, `5 = e₂`, `3 = −e₃` in the frame
  `x 1; x 4 − x 1, x 5 − x 1, x 1 − x 3`, so `O` is six numbers and the cap is `(s, t, 0)`), every
  test a polynomial times the frame determinant (`nf29_test`), `σ = (0 2)(4 5)` (`NF29.sigma`), and
  from the facets `IsCap29.toNF29` (each inequality a facet sign, `IsCap29.nf29_core`).  K4
  (Theorem 21.11): Lemmas 21.7, 21.8 (`NF29.k4_facts`), F35 (21.9: `V`, `Y`, `NF29.isRupert_k4_A`),
  F234 by `σ`, F35′ (21.10: `W`, `Z`, Corollary 13.3, `NF29.isRupert_k4_B2`); `NF29.isRupert_K4a`,
  `NF29.isRupert_K4b` on `R_G`.  K3 (Theorem 21.22): Lemma 21.12 (`NF29.k3_facts`), Lemma E at
  `56`, `14`, `46` off `R` (21.13), P14 or a free `T2` (21.15 (i)), `R = ∅` for `h2 ≥ 1 + A2` (ii),
  `h0 > F5` (iii), P11, the planar `T3`, Lemma X, the planar `Y1` (21.17), P13 and Y′ (21.20 with
  21.21, the pattern argument `k3_Y2_core`); `NF29.isRupert_K3a`, `NF29.isRupert_K3b` on `R_G`.
  Off `R_G`, Lemma E at the E-good quad edge (clause C1 of Theorem P, in coordinates):
  `NF29.isRupert_K4a_all`, `_K4b_all`, `_K3a_all`, `_K3b_all`; from the facets
  `isRupert_type29_K4`, `isRupert_type29_K3`.  Hypotheses: the special positions of §21.5 (and
  `h0 ≠ 1`, `F5 ≠ h0` in K3, `s, t ≠ 1` at the C1 edges), distinct depths on the named rims and no
  horizontal double normal at the named views (`K4Gen`, `K4C1Gen`, `K3Gen`, `K3C1Gen`).  Not
  formalized: classes K2 and K1, the limit lemma for the codimension-1 boundaries.
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
  formalized: Lemma 1 in general, Lemma 4 (insertion), Theorem S.
* §16 of `FEWER-FACES-PROOFS.md` (type 21, the tier cover; `Type21Tier.lean`,
  `Type21Cover.lean`, `Type21F1.lean`, `Type21F2.lean`, `Type21R.lean`, `Type21Cap.lean`,
  `Type21Entry.lean`, `Type21O2.lean`, `Type21Other.lean`, `Type21F2Case.lean`,
  `Type21Pattern.lean`, `Type21Facets.lean`).  The tiers as Rupert lemmas: Lemma 16.1 (`EGoodQuad`: a quad edge in
  Gale form that is E-good, `[x' x] [x' y] > 0`; `EGoodQuad.tests`, `not_bad_of_egood`), tier Q
  (`Type21Q`, `cert_type21_Q` for `K − 2`, `cert_type21_Q2` for `K − 6`), tier H
  (`Type21H`, `cert_type21_H`, `_H2`: the cap is hidden by `quadHidden_of_beneath`, which
  replaces Lemma 16.4), tier F1 (Lemma 16.7, `cert_type21_F1`: the vertex test `T1` by
  `isRupert_axisTest`, the pentagon `Y` along `04` by `cert_type21_Y`, `isRupert_quint_rim`,
  `type21_Y_unimodal`), tier F2 (Lemma 16.8 (a) `vertex_sep`, Lemma 16.9
  `cert_type21_F2`), tier R (Lemma 16.5: `rimCert_ridge`, `Type21RQ`,
  `cert_type21_R`).  Gale computations: the cap parameter `τ` (`IsCap21.tau`,
  `IsCap21.gale_rel`), the dependencies `{1 ·}`, `{0 ·}` of `K − 6` (Lemma 16.2,
  `type21_depO2_c`, `type21_depO2_a`), the facet values in brackets (`type21_f014`, …), the
  bracket identities (`type21_id_*`, by `type21_ring`), Lemma 16.11 (`type21_A1`), Lemma 16.12
  (`type21_lemma1612`), the steps `Q` at `25` and `23` of `K − 6` (`cert_type21_step3`,
  `_step5`).  **Theorem 16.13** (the cap-face class): `cert_type21_capFace_norm`
  (normalized, `CapNorm`), `cert_type21_capFace` (`CapFace` for `K − 2` or `K − 6`; the
  normalization by `GaleData.flip`, `σ1`, `σ2`), off `NoPlaneParallel` (every tie of a Gale
  comparison, `facet_tie_det`), `GenPos`, `NoHDNEdges` and `T1Gen` at the four vertex crossings
  (`Type21CapGen`).  From the facets: `exists_type21_cap`
  (the octahedron `K − 2` with its face `356`).  **The §16 addendum** (the other Gale
  classes): Lemma 16.16 (`arc_step1`, `type21_O_quad36` for `K − 2`, `type21_O2_quad04` for
  `K − 6`), the Gale data of `K − 6` (`type21_galeO2`, its pair brackets
  `type21_galeO2_kappa`), Theorem 16.18 (class (a), `cert_type21_classA`), Theorem 16.20
  (class (b), `cert_type21_classB`, with R at the ridge `26`), Lemma 16.21
  (`type21_near_or_A1`), Theorem 16.23 (class (c), `cert_type21_classC`) with Lemma 16.24
  (F2 on the rest of class (c): `cert_type21_F2case` for the Gale facts and
  `cert_type21_F2_frame` for the geometry in the frame `4; 3, 5, 6`, every determinant a
  bracket polynomial times `det(3 − 4, 5 − 4, 6 − 4)`), the normal form `(+, −, +)`
  (`cert_type21_pattern`), and Lemma 16.15 with Theorem 16.26 (`type21_O2_signs`,
  `cert_type21_all`: the cap-face class by 16.13, the other patterns by `σ1`, `σ2`, `σ2σ1`
  and the Gale reflection).  **The switch surface** `δ_014(2) = δ_014(5)` (§16 parts K–M;
  `UniformTilt.lean`, `Type21Switch.lean`): Lemma 16.27 (the uniform tilt,
  `isRupert_of_edgeChords_uniform`) and 16.27′ (doubles, `isRupert_of_uniform_doubles`), each
  with Theorem 7.3; Corollary 14.1 with middles over any side (`isRupert_edgePair_uniform`);
  Lemma 16.28 (`type21_switch_view`, `type21_switch_mid1`, `type21_switch_mid6`), Lemma 16.29
  (`type21_switch_sep`) and Theorem 16.30 (`cert_type21_switch`, under `CrossNorm` and
  `δ_0256(4) < δ_0256(1)`), which closes the halves `H⁻` (in 16.13) and `H⁻_c` (in class (c)).
  The planar equators of `K − 2` and `K − 6` are explicit exclusions
  (five planes) in place of 16.25's continuity argument; `f = 0` and every tie are in
  `NoPlaneParallel`.  From the facets, `isRupert_type21_facets`; at the entry point,
  `not_type21_of_isNopert`, unconditional off the special positions: `NoPlaneParallel`,
  `GenPosTie` (no parallel segments, at most one tie at each edge view: codimension 2; every
  edge-view test allows single ties: Lemma E with ties at the ridge and the switch surface, the
  robust quad lift in tiers Q/H, the planar closing `2346`, and `Y`'s pentagon by
  `type21_Y_robust`), no horizontal double normal at the edge views, the five planar equators,
  `T1View` at the four vertex crossings, and `F2Views` (the two vertex tests of F2) in the four
  labellings (both allow the depth ties of `QuadTie` on their rims: Theorem 18.3 through
  `isRupert_axisTest_core_robust`, `RobustAxis.lean`).  Not formalized: Lemma 16.4's
  silhouette argument (replaced; tier H hides the cap by strict facet inequalities, so 16.4's
  special position "P(2) on ∂S_O", which Lemma 16.31 closes on paper, never arises in Lean),
  Lemma 16.8 (b), Lemma 16.25 (replaced by the exclusion), the boundary cases of 16.30, AX.
  Every theorem of the tier cover concludes a rim certificate at a named view (`CertV`: a
  segment or a view satisfying `L`), with no horizontal double normal assumed (`cert_type21_*`,
  §9's lifts in `Type21LiftCert.lean`, the crossing tests in `RimCertLift.lean`);
  `isRupert_type21_facets` is re-derived from `cert_type21_facets` in `Type21Limit.lean`.
* §18.6 step 2 for type 21 (`Type21Limit.lean`, with `RimCertLift.lean`, `Type21LiftCert.lean`):
  **type 21 outside the HDN set and codimension 2**, `isRupert_type21_limit` /
  `isRupert_type21_limit_facets` and the entry point `not_type21_of_isNopert_codim2` (the entry
  point with §22.2's weakening at the two-triangle views, see §22 below).  Hypotheses: the facets, no horizontal double normal at the views along the segments and the
  lines of the eight facet pairs `014/0256`, `014/2346`, `135/0256`, `135/2346`, `046/134`,
  `046/015`, `235/134`, `235/015` (`NoHDNAff`), and at most one tie at these named views
  (`OneTie21`, counted as `OneTie16`).  No general position, no sign condition or Gale equality
  of the cover, no planar equator, no switch surface, no (G1).  Proof: normal-form shapes in the
  frame `2; 0, 3, 6` (`co21`, `nfShape21`, `Facets21.eq_nfShape`: `5` on `0256`, `4` on `2346`,
  seven parameters); the special positions of the cover (every instance of `NoPlaneParallel`
  and of the parallel clause of `GenPosTie`, the five planar equators, the twelve far-side tests
  of `T1` and F2) as one polynomial `gen21`, nonzero by `decide` at an integer point
  (`genPoly21_ne_zero`); the tie of `K` kept by the shear `restore`; facet functions of the
  nearby shapes as determinants (`fac21`, `Facets21.exists_kappa`); the cover at a generic shape
  (`cert21_of_generic`), whose ties are those of `K`: at most one at each named view, none along
  `a − b` when `a, b` tie at a view of `T1` (`noTieAt_seg_of_tie`), and a tie at no more than one
  view of F2 (`noTieAt_or`).  The vertex tests now allow a single tie that is a level rim edge
  inside a run (formerly excluded by `QuadTie`): such a rim is weakly separated
  (`weakSep_of_not_robust`); in F1 the wrong weak separation puts `0` on the segment `[5, 4]`
  and the right one gives `Y` (strictly, or with no tie along `04`, `T1Tie`); in F2 the rim
  without a tie is strictly separated and the weak sign (`weakSep_det_sign`, the equators not
  planar) excludes the pair (`F2Tie`).  `T1View`, `F2Views` (with `QuadTie`) keep their old
  meaning for `not_type21_of_isNopert`.  Not formalized: 18.4 (β) itself (the codimension-2
  condition is `OneTie21`, conservative: over all named views), the codimension count.
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
  T4 weak edges); that some clause always holds is open.  The entry point for type 16 is
  the cover of §19 (next item).
* §19 of `FEWER-FACES-PROOFS.md` (type 16, the cover; `Type16NF.lean`, `Type16Cover.lean`,
  `Type16Rims.lean`, `Type16Pairs.lean`, `Type16Main.lean`).  The normal form `NF16`
  (`3 = 0`, `0 = e₁`, `5 = e₂`, `6 = e₃`, `2 = (a, b, 0)`, `1 = (0, g, d)`, `4 = (p, q, r)`, in the
  frame `x 3; x 0 − x 3, x 5 − x 3, x 6 − x 3` with its determinant `D`, and the type
  inequalities of §19.0) from the facets (`Type16.toNF`), and `σ = (06)(12)`
  (`NF16.sigma`); every orientation test is a polynomial times `D` (`det3_nfV`, the tactic
  `nf_test`), every depth an inner product (the paper's "every metric").  R1 and R2 exclude
  each other (`NF16.R2_neg_of_R1`).  Certificates in either orientation `σ = sign D`:
  `isRupert_edgePairσ`, `isRupert_edgeTriσ`, `isRupert_of_edgeViewσ`,
  `isRupert_of_vertexViewσ`, with explicit quadrilateral and pentagonal rims
  (`isRupert_vquadσ`, `isRupert_vquintσ`, `isRupert_equadσ`, `isRupert_equintσ`).
  Every step ends in a certificate `Cert16` (§18.2: a rim certificate `RimCert` at a named
  view, `view16`: the segments and the six vertex crossings `vtxView16`; no horizontal double
  normal assumed), through the certificate forms `rimCert_edgePairσ_robust`,
  `rimCert_edgeTriσ_robust`, `rimCert_vquadσ`, `rimCert_vquintσ`, `rimCert_equadσ`,
  `rimCert_equintσ`.  Proposition 14.3 off `R1 ∪ R2` (`NF16.cert_E06`); Lemma 19.1
  (`NF16.g_gt_one`, `NF16.q_gt_b`); Theorem 19.2 step by step (`cert_stepA`,
  `_stepU1a`–`_stepU5`, `_stepD1`–`_stepD7`; Lemma E pairs, the planar closing at `14`,
  triangle closings) and its dispatch (`NF16.cert_R1_or_omega`, residual `NF16.Omega`); Lemma
  19.3 (`NF16.cert_F3`: `T1 = K_3` at `35` and `T2 = 046/145` at `4`, view `vT2`), Lemma 19.4
  (`NF16.cert_F1s`: `A = 036/146` at `6`, view `vA`, and `B = K_6` at `36`), Lemma 19.5
  (`NF16.cert_T6`: `T_a = 0235/046` at `0`, view `uA`, `A`, and `T_c = K_1` at `15`; the
  failure directions by the four-corner rule `depthSep_of_meet`, `depthSep_sign` and the cone
  identities (C1)–(C3), (A1), (A2′), (A3) as vector identities, `cone_inner3`); the views
  `vT2`, `vA`, `uA` are named (`NF16.vtxView16_vT2`: `vtxView16 x 0 = −D vT2`, and so on); the
  cover (`NF16.cert_omega`, `NF16.cert_R1`, `NF16.cert_nf`); the special positions from the
  points (`NF16.Gen.of`, `NF16.Views.of`, `NF16.R_ne`).  From a certificate to Rupertness:
  `Cert16.isRupert` (convex position `Type16.noSeg`, no horizontal double normal at the named
  views `Type16.noHDN_views`); `NF16.isRupert_type16`, `isRupert_type16_facets`.  Ties (Theorem
  18.3): the Lemma E cover by Lemma E with ties (`depth_far3`, `depth_tri3` from `TieSeg`); on
  `Ω` every rim robustly unimodal: quadrilaterals unless weakly separated
  (`NWS4.isRobustUnimodal`), pentagons by their open criteria with one tie (`quint_B_robust`,
  `quint_Tc_robust`, `quint_A_robust`, through `isRobustUnimodal_of_nhds`), and the pair and
  triple arguments with weak separations (`not_weakSep_of_meet`, `eq_of_weakSep_meet`,
  `weakSep_sign`: a weak failure either gives the old sign or puts three points at one depth).
  At the entry point `not_type16_of_isNopert`, off explicit special positions: `GenPosTie`,
  `NoPlaneParallel` (the equalities in the sign conditions of the route), no horizontal double
  normal at the edge views, the coplanarities `0134`, `2346`, `LineAff16`, and at most one tie
  with no horizontal double normal at the six vertex views (`ViewAff16`).
* §18.6 step 2 and Theorem 19.8 for type 16 (`Type16Limit.lean`, with `LimitRim.lean` and
  `RimCert.lean`): **type 16 outside the HDN set and codimension 2**,
  `isRupert_type16_limit` / `isRupert_type16_limit_facets` and the entry point
  `not_type16_of_isNopert_codim2` (the entry point with §22.2's weakening at the two-triangle
  views, see §22 below).  Hypotheses: the facets, no horizontal double normal at the
  views along the segments and the lines of the six facet pairs (`NoHDNAff`), and at most one
  tie at these named views (`OneTie16`, with `TieInst16`, `SameTie16`: the tie of `s, t` along
  `ij` and the tie of `i, j` along `st` count once).  No general position, no sign condition of
  the route, no (G1), no `LineAff16`.  Proof: normal-form shapes from parameters (`nfShape`,
  `NF16.ofParams`, `ineq16`); the special positions of the cover as one nonzero polynomial
  (`genPoly16`, `genPoly16_ne_zero` by one evaluation) whose nonvanishing set is dense
  (`exists_seq_eval_ne_zero`, `MvPolynomial.funext_set` on boxes); the tie of `K` is kept along
  the sequence by a unimodular shear (`restore`, `det3_restore`, `view16_restore`); ties of
  `K_n` are ties of `K` eventually (`eventually_ties`, `oneTieAt_of_ties`); each `K_n` has a
  certificate (`NF16.cert_nf`), normalized to finitely many labelled forms
  (`Cert16.exists_certL`, `CertL16`), a subsequence carries one (`frequently_exists_of_finite`),
  and `isRupert_of_tendsto_rimCert` concludes.  Not formalized: 19.7 (b) / 18.4 (β) across
  certificates (two ties on different certificates' rims are excluded together with every
  other pair of ties), the codimension count itself (stated, not proved).
* §22 of `FEWER-FACES-PROOFS.md` (HDN exceptions of types 16 and 21; partial: Proposition 22.2 at
  the two-triangle views; `Sector.lean`, `Type16Sector.lean`, `Type21Sector.lean`).
  **Proposition 22.2, general form** (`isRupert_of_tiltHides`): at a view `u`, a cycle `X` of
  points of `V`, every point weakly left of every side, robustly unimodal depths, and a tilt `d`
  that hides every point over a side line (`TiltHides`: `[X (i+1) − X i, z − X i, d] > 0`) make
  `V` Rupert, with no condition on horizontal double normals or ties: along `u + εd` the
  silhouette is `X`, and robust unimodality is open in the order of the depths
  (`IsRobustUnimodal.isCyclicUnimodal_of_order`, from `IsRobustUnimodal.not_weak_peaks`), so
  Corollary 8.0′ (`isRupert_of_tilted_unimodal'`, Theorem 7.5) applies.  The cone of tilts
  (`exists_tiltHides_of_normals`): if every side constraint is a positive multiple of one of two
  non-parallel face normals (the closing is realized on both face circles), one tilt hides all;
  for two triangles this holds for every rim (`exists_tiltHides_tri`, with (G1) as `G1Tri`: every
  point over a support line lies with the line's ends on one of the triangles; one constraint per
  triangle, `cross_tri_sides`).  The limit lemma with the tilt alternative
  (`isRupert_of_tendsto_rimCert_or`): no horizontal double normal at the limit view, or a hiding
  tilt for the labelled rim at the limit.  At the limit, (G1) at an edge view is `G1Edge`
  (`ParOnly`: the axle is the only pair over one point, which a certificate never takes as
  consecutive labels, `RimCertAt.not_axle`; with `G1Tri`), at a vertex view `G1Vtx`
  (`NoParAt`); `exists_tiltHides_limit`.  Types 16 and 21 (`Sec16`, `Sec21`;
  `isRupert_type16_limit_sec`, `isRupert_type21_limit_sec` from the extracted sequences
  `exists_certSeq16`, `exists_certSeq21`; facets forms `isRupert_type16_limit_facets_sec`,
  `isRupert_type21_limit_facets_sec`): at the two-triangle edges (type 16: `04`, `06`, `14`,
  `24`, `45`, `46`; type 21: `01`, `04`, `14`, `15`, `13`, `35`) and two-triangle vertex
  crossings (type 16: `046/145`, `036/146`, `046/245`, `036/024`; type 21: `046/134`, `046/015`,
  `235/134`, `235/015`) the hypothesis is "no horizontal double normal, or (G1)"
  (`HDNOrG1Edge`, `HDNOrG1Aff`): codimension 2.  The entry points
  `not_type16_of_isNopert_codim2`, `not_type21_of_isNopert_codim2` use these.  Not formalized:
  22.2 at quadrilateral faces (two-circle closings such as `K_0` at `02`; they share their view
  with a one-circle closing, so the view's hypothesis would not change without 22.3–22.10),
  22.3–22.10 (one realizing circle: classes H_j, c_j via 22.4, d_j via A.10's Theorem R,
  Lemma 22.7, the partner closing, 22.13, 22.14), and the codimension count of §22.4.  So
  horizontal double normals remain excluded at the views with a quadrilateral face: type 16 at
  the other fifteen segments and the lines of `0235/046`, `1356/046`; type 21 at the other
  fifteen segments and the lines of `014/0256`, `014/2346`, `135/0256`, `135/2346`.
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
* §17 of `FEWER-FACES-PROOFS.md` and its addendum (type 24 in `C̄` near the cube corner;
  `Type24Cap.lean`, `Type24Corner.lean`), at `K`'s own metric (depth `⟪·, d⟫`). Lemma C
  (Theorem 17.10, the cap-edge dichotomy): along a cap edge `1x` the rim of `K_1` is
  `(1, y, R, w)`; each far-path step keeps the sign of `ΔX_x` while
  `|ΔX_y ⟪e_y, e_x⟫ + ΔX_w ⟪e_w, e_x⟫| < ‖e_x‖² |ΔX_x|`, which follows from `|c| < δ` with
  `δ (L_y |ΔX_y| + L_w |ΔX_w|) ≤ L_x |ΔX_x|` on every step (`capStep_of_cos`; `δ ≤ δ_x`), so
  with `(H-cap)` the depths rise and fall along `R` (`exists_arch`) and the rim is unimodal
  unless `1` is a local maximum (`capEdge_unimodal`); Rupert form with `x` a double over `1`
  (`isRupert_capEdge`, `isRupert_capEdge_frame`, rim data `CapRim`), for type 24
  `isRupert_type24_E2`, `_E6` and the dichotomy `isRupert_type24_capEdge` (Rupert for
  `|c|∞ < δ` unless all three inner products at `1` are `≤ 0`); `(H-cap)` from "3 is the
  middle" and the planar quad (`noInteriorMin_of_mid3`, `Type24.hcap2`, `Type24.hcap6`).
  Lemma Q / Q′ (17.4, 17.19): a rim that is the planar quad never fails, at every metric
  (`planarQuad_fails4`, `planarQuad_unimodal`, `isRupert_planarQuad`, `isRupert_type24_Q`).
  Lemma 17.15 (8.8 for faces without a common vertex) is `isRupert_of_chords` /
  `isRupert_disjointFaces`. The circle identity 17.3 (c) (`circle_depth`, `circle_depth6`) and
  M3 (17.7) in BB's every-metric form (`m3_not_both`, `isRupert_m3`). At an exact corner
  (`ExactCorner`: orthogonal axes at `1`): M3 and its mirror (`m3_corner`, `m3_corner6`), one
  ratio on circle 2 (17.14 (a), `fails4_circle2_iff`) and the closed forms 17.5, 17.17 (b), (c)
  (`pencil_0264`, `pencil_02x6`, `t26_fails_corner`, `s0_fails_corner`), M1 (17.8, `m1_corner`;
  WP_2 as its depth chain at a view in `(lo_f, ω3)`), the T′ pair (17.17 (d) with the pair
  rule, `tpair_corner`), M3′ (17.18, `m3prime_corner`), with Rupert forms through `QuadTest'`
  (`isRupert_of_two_tests`, `isRupert_m3_corner`, `isRupert_m1_corner` with Lemma W as a
  hypothesis, `isRupert_tpair_corner`, `isRupert_m3prime_corner`). `Type24WP.lean`: Lemma W
  (`isRupert_lemmaW`: a point hidden strictly inside, or over an open side of, a certified rim
  of `V ∖ {p}` costs nothing), WP as a Rupert item (`isRupert_wp2`, `isRupert_wp6`: on the arc
  the cap `1` is a middle over the side `0 b`, and the 5-cycle `(c, q, 0, b, 3)` with four
  monotone corners is unimodal), M1 with `hWP` discharged (`m1_corner_Ioo`,
  `isRupert_m1_corner_wp`: the rim of `B` on `(lo, ω3)` and exclusions off a finite set of arc
  views), L7 (15.15) at the corner and with the radius 17.8′ (`l7_frame_corner`,
  `l7_frame_radius`, `isRupert_l7_t26`, `_t62`, `_t06`, `isRupert_l7_t26_radius`), the arc
  criterion 17.16′ on circle 2 ("if", with WP: `arc_criterion2`, `arc_criterion2_wp`,
  `isRupert_arc_criterion2`) and its pair form (`pair_rule`, `circle2_pair`,
  `isRupert_circle2_pair`), the radii 17.1 / 17.1′ (`inner_frame_diff`, `radius_pos`,
  `radius_pos_octant`), WP near the corner and on the obtuse octant (17.11,
  `wpChain2_radius`, `wpChain2_octant`) and 17.12 with WP_2 as the item
  (`isRupert_type24_near_wp2`). Not formalized: the geometric half of 17.9 (the rim of `K_1`,
  "3 in the middle": hypotheses), 17.6's face conditions (WP's rim is a hypothesis), the
  finiteness of the exclusions on the arc, the "only if" of 17.16′, the radii of the other
  items (`S_0`, `δ_M3`, 17.20) and 17.12 beyond WP_2, the exact-corner lemmas off the corner
  (except M3, L7 and WP_2).
* §20 of `FEWER-FACES-PROOFS.md` (type 24 inside `C̄` at every metric; `Type24Metric.lean`,
  `Type24Chain.lean`), at `K`'s own metric with no radius. Failure depends on the depth covector
  `u = G d` only (20.1 (a), `fails4_iff_covFails`, X-only `CovFails`). Lemma C without `δ`: a
  cap-edge crossing fails only through a dip of a far corner (20.2 (b),
  `isCyclicUnimodal_of_noDip`, `isRupert_capEdge_noDip`, rim data `CapRim0`; 20.2 (c),
  `mid3_not_dip`, `isRupert_capEdge_mid3`); acute-safety (`AcuteSafe`, X-only) and 20.2 (a), a
  single far corner is acute-safe for `E_2`, `E_6`, `E_0` (`acuteSafe_four`, `capRim_far_sum`,
  `Type24.safeE2_of_four`, `_E6`, `_E0`); Theorem 20.8 (`isRupert_type24_two_safe`,
  `Type24.obtuse_of_two_safe`: Conjecture A for two acute-safe cap edges); Lemma 20.6 at the
  exact corner (`Type24.s0_e05_corner`, mirror `s0_e04_corner`, Rupert forms); Lemma 20.3 (WP_2
  just above the view `t3` where `z0 = z2`: `wpChain_after`, `wpView_t3`,
  `isRupert_wp2_after`); Theorem 20.4, the window chain, for a general arc (`windowChain`, with
  the X-only hypotheses (H_h), (H_l), (H⁺)); its data `WindowChain` and Rupert forms on arcs 2
  and 6 (`isRupert_windowChain2`, `_6`), Corollary 20.5 on the closed obtuse octant
  (`isRupert_windowChain_octant`) and Theorem 20.9 (`isRupert_type24_uniform`: two acute-safe
  cap edges and the chain give Rupert at every metric). Not formalized: 20.1 (c), (d), the LPs
  deciding acute-safety and (H) for given classes, Proposition 20.7's certificates, 20.6's
  radius.
* §20, continued, of `FEWER-FACES-PROOFS.md` (side-safety, (L), Conjecture B; `Type24Side.lean`,
  `Type24Lambda.lean`). The sink lemma 20.2 (d) (`capRim0_sink`, `Type24.sinkE2`, `_E6`, `_E0`;
  from the converse dip lemma `exists_dip_of_not_unimodal` and the rim facts `CapRim0.ne_ax`,
  `CapRim0.path`) and its `m = 2` corollary (`capRim0_five_fails_iff`), the common sink
  (`common_sink`); side-safety (`SideSafe`, X-only, `Type24.SideCovered`) and Theorem 20.8′
  (`isRupert_type24_side_safe`, `Type24.obtuse_of_side_safe`: Conjecture A when each cosine is
  seen on a safe side; 20.8 is the case `Type24.sideCovered_of_twoSafe`); Theorem 8.10 as a
  cap-edge item (`isRupert_capRim0_depthSeparated`, `isRupert_capRim0_uos`, general edge views
  `isRupert_of_edgeView_depthSeparated`), useless for 4-corner rims
  (`not_fails4_of_depthSepAt`). Lemma 20.10 (OO's identity `Lambda.identity`, both clauses
  `Lambda.lemma_20_10`, `Lambda.lemma_20_10_strict`, at `K`'s metric `lemma_20_10_wp`); the
  window chain in general form (`windowChain_gen`: `r4 > 1` or (L2), Theorem 20.4″; (L) from
  `c' ≤ 1`, (L), (H⁺) or (Λ), Corollary 20.11), its data `ChainData` and Rupert forms
  (`isRupert_chainData2`, `_6`, `isRupert_chainData2_L2`, `_6_L2`, `WindowChainΛ`,
  `isRupert_windowChainΛ2`, `_6`, `isRupert_windowChainΛ_octant`) and Theorem 20.9′
  (`isRupert_type24_uniform_side`). Not formalized: the LPs deciding side-safety, (H) and (H⁺),
  the third item `012/0345`, Conjecture B_DS, the per-class certificates.
* §20, continued (2) and (3), of `FEWER-FACES-PROOFS.md` (the circle of `236`, DS side-safety;
  `Type24Circle236.lean`, `Type24DS.lean`, `Type24Circle.lean`). Lemma 20.12 (`Cu13.S1`, `S2`,
  `S4`, `S5`; (S1) at `K`'s metric `Type24.s1_pattern`, its geometric half from `T′(6,2)`'s rim
  `Type24.c5_lt_of_rimT62`). Theorem 20.13: E23's three cases (`e23_cases`; edge crossings with a
  general axle `EdgeRim`, `isRupert_edgeRim`), with the ten LPs as X-only hypotheses (`K236bar`,
  `K236`, on Gram entries `Gram3`) on the closed (`isRupert_circle236_octant`) and open
  (`isRupert_circle236_open`) obtuse octant; Corollary 20.14 (`Type24.ObtuseCovered`,
  `isRupert_type24_obtuse_octant`) and Theorem 20.9″ (`isRupert_type24_uniform_circle`).
  Corollary 20.19, the planar quad rim at every metric (`planarRim_coeffs`: `s, t > 0`,
  `s + t > 1` read off the rim; `QuadTest'.isRupert_planar`, `isRupert_type24_planarQuad` from the
  face `0345`). Lemma 20.18 (cu14's core `Cu14.P1`, `P2`, `lemmaY`; general labels `lemmaY_core`,
  `YBelow`, `isRupert_lemmaY`; `R_bc` `isRupert_lemmaY_bc`, mirror `isRupert_lemmaY_bc'`). DS
  side-safety (`ParPairAt`, `DepthSepZ`, `DSGood`, `DSSafeQ`, `isRupert_capEdge_dsSafe`),
  Theorems 20.16 (`Type24.DSSideCovered`, `isRupert_type24_dsSide`) and 20.17 (`RegSign`,
  `Type24.DSRegionsCovered`, `isRupert_type24_dsRegions`), the acute side by 20.17–20.19
  (`Type24.AcuteCovered`, `isRupert_type24_acute`), Theorem 20.9‴ (`isRupert_type24_uniform_ds`,
  `isRupert_type24_uniform_dsRegions`, `isRupert_type24_uniform_acute`). Not formalized: (S3),
  closed forms of the LPs `z3 > z0, z5`, Lemma 20.15 (DS-safety is a hypothesis), the LPs and cell
  enumerations deciding DS-safety, (K236) and (Y) for given classes, Propositions 20.7′ and 20.20
  and their per-class certificates, the class counts.

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
| `SlideDS` | §10 addendum, Lemma H (c) and Lemma X: Theorem 8.10 along a face circle (a depth-separated pair in space at the view, strict, so it persists along the slide); Lemma 7.4 by edges with the feet of the double normal, and `NoBadNormalR` (a bad direction normal to the face only matters if the double normal's feet lie on the two edges: the persistent double normal); Proposition 8.8 at a view and along a slide, unimodal or depth-separated | `DepthSepAt`, `isDepthSeparatedPair_of_depthSepAt`, `eventually_depthSepAt`, `NoFeet`, `exists_pairDir_of_hdn'`, `NoBadNormalR`, `NoBadNormal.toR`, `isRupert_of_chordViewG_or`, `isRupert_of_slideG`, `UniOrSep`, `isRupert_of_slide_uos` |
| `Type08Slide` | Type 08, the cases of Theorem 10.1 by slides (Lemma C) and Lemma H's five-corner rims: N2 in an octahedron with one more point (tests in either orientation, the closing by `x` with the triple-tie exclusion), T4 and Q in the frame `d; a, c, b` | `quad_edge_tests_or`, `nws4_closing_oct`, `isRupert_quad_edge_middle_sel`, `isRupert_quad_edge_middle_slide`, `isRupert_quad_edge_middle_five`, `t4_closing`, `isRupert_t4_sel`, `isRupert_t4_slide`, `isRupert_t4b_five`, `isRupert_t4d_five`, `isRupert_q_slide` |
| `Type08Tie` | Type 08, Lemma X: the routes at the far-end ties `T`, `T'` (four-corner slides with a middle next to a far end, five-corner rims with a poked-out vertex, the latter with `NoBadNormalR`) | `isRupert_kb_four`, `isRupert_kd_four`, `isRupert_r2pp`, `isRupert_r2p`, `isRupert_r4pp`, `isRupert_r4p` |
| `Type08X` | Type 08, Lemma X: which route applies at `T` and `T'` (the paper's case analysis from the depths: the separated depths, Lemma 5's closing and claim, the poked-out rims strictly unimodal, the persistent double normal giving the depth inequality that makes R2″ / R4″ unimodal) | `strictUnimodal_of_unique`, `claim_contra`, `RouteT`, `RouteT'`, `isRupert_routeT`, `isRupert_routeT'` |
| `Type08Rd` | Type 08, A.10 (`R_d` is Rupert): Lemma R2's certificate, slot tests along a tilt, Theorem R in coordinates and in any orthonormal frame (the isometry to coordinates), the `R_d` conditions along an edge view, the closings N2–`K_c` (the hidden `a` inside a triangle of the rim) and T4–`K_b` | `rd_limit_cert`, `eventually_det3_lin`, `eventually_slot`, `isRupert_rd_std`, `IsFrame`, `isRupert_of_frame_image`, `isRupert_rd`, `RdRim`, `isRupert_of_rdRim`, `rdHidden_quad_edge`, `isRupert_quad_edge_middle_rd`, `isRupert_t4b_rd` |
| `Type08R0` | Type 08, Lemma R0 of A.10 ((H1)–(H4) on `R_d`): orthonormal frames, the depths (two peaks, the weak saddle of `K_w`, the claim), (H2) and (H4) in coordinates, the abstract lemma, the two closings, (H4) from the Gale diagram | `exists_rdFrame`, `two_peaks`, `rd_depths`, `rd_coords`, `RdCond`, `rdRim_of_R0`, `quad_edge_claim`, `t4_claim`, `isRupert_quad_edge_middle_rdCond`, `isRupert_t4b_rdCond`, `type08_rd_sides` |
| `Type08Codim` | Type 08, Theorem 10.1′ (Lean form) without planar equators: the far-end identity at the ties (Gale), `b'` a corner in the T4 case, `R_d` empty for T4–`K_d` (A.10's remark), the hypotheses per labelling, the case analysis, the relabelling, the facet form | `type08_T_far`, `type08_T'_far`, `t4_kappa_pos`, `t4d_five_strict`, `t4d_rd_empty`, `t4d_slide_of_par`, `Type08Gen`, `Type08GenAll`, `isRupert_type08_slide_core`, `isRupert_type08_slide`, `isRupert_type08_slide_facets` |
| `Type08Flat` | Type 08, Lemma K (one planar equator): the crossing diagonals of a planar equator, Lemma 7's quad edge from `(G4)`, the signs when `κ_b = 0`, the relabelling, the facet form | `flat_cross`, `not_bad_of_cross`, `type08_quad_edge`, `flatB_signs`, `isRupert_type08_flatA`, `isRupert_type08_flatB`, `isRupert_type08_flat`, `isRupert_type08_flat_facets` |
| `Type29Lemmas` | Type 29 (`FEWER-FACES-PROOFS.md` §12, Theorem P), the reusable lemmas for an octahedron with one more point: Lemma 1 (certification without a crossed pair: a quad edge whose tail is an inner vertex of its third pair, `[p x] [x x'] < 0`, is not bad; Lemma 9.7 via `inTri_of_dep` and §10's Lemma 3), Lemma 2 (exact lift: a middle or hidden extra point leaves the reduced polygons, and Lemma 9.3's unimodal closing, unchanged; through `isRupert_of_edgeView`, i.e. `isRupert_of_edgeChords_unimodal`), a hidden point from the facets, both together | `quad_edge_sep`, `inner_dep_signs`, `not_bad_of_inner`, `QuadMiddle`, `QuadHidden`, `isRupert_quad_edge_lift`, `quadHidden_of_beneath`, `isRupert_inner_quad_edge_lift` |
| `Type29Lift` | Type 29, Lemma 3 (b) with `t > 1` (the cap is the far end, `5` the middle): the octahedron's shadow tests in either orientation, the tests at the cap, a point inside a quadrilateral is on the positive side of a line through a vertex (barycentric identity), the closing of Lemma 9.3 for any 4-cycle or a triangle (either orientation), step 3 (the up face `356` rules out `K`-badness), the lift | `quad_edge_testsσ`, `cap_testsσ`, `det3_bary`, `inside_line_pos`, `isRupert_closing_quad`, `isRupert_closing_quadσ`, `isRupert_tri_viewσ`, `lift_far_not_bad_core`, `isRupert_lift_far` |
| `Type29` | Type 29, Theorem P of §12 (partial): the cap `IsCap29` over `O = K − 6` and `σ = (0 2)(4 5)`, Lemma 0 (b) (coordinates `s, t`), Lemma 3 (quad edges at `1` lift: `14`, `41`, `15`, `51`), Lemma 4 (the cap is hidden at `0→3`, `0→5`, `2→3`, `2→4`), clauses C1, C2 (`K − 5`; `K − 4` by `σ`), C3, and Theorem P; no `not_type29_of_isNopert` (that some clause holds is open) | `IsCap29`, `IsCap29.coords`, `isRupert_type29_14`, `isRupert_type29_41`, `type29_hidden_03`, `type29_hidden_05`, `Type29C1`, `Type29C2`, `Type29C3`, `isRupert_type29_C1`, `isRupert_type29_C2`, `isRupert_type29_C3`, `isRupert_type29_P` |
| `Type29NF` | Type 29, §21.0: the normal form `NF29` (Lemma 21.1) in the frame `x 1; x 4 − x 1, x 5 − x 1, x 1 − x 3`, `σ = (0 2)(4 5)`, the test tactics, a vertex-view triangle rim | `NF29`, `sigma29`, `image_sigma29`, `NF29.sigma`, `nf29_simp`, `nf29_vec`, `nf29_test`, `isRupert_vtriσ` |
| `Type29K4` | Type 29, §21.1 (class K4 on `R_G`): Lemmas 21.7–21.10, Theorem 21.11; the tests `V`, `Y`, `W`, `Z`, Corollary 13.3 with a shared diagonal | `NF29.k4_facts`, `NF29.isRupert_k4_V`, `NF29.isRupert_k4_Y`, `k4_Y_core`, `NF29.isRupert_k4_A`, `NF29.isRupert_k4_W`, `NF29.isRupert_k4_Z`, `NF29.isRupert_k4_B2`, `K4Gen`, `NF29.isRupert_K4a`, `NF29.isRupert_K4b` |
| `Type29K3` | Type 29, §21.2 (class K3 on `R_G`): Lemmas 21.12–21.21, Theorem 21.22; the tests `T1`, `T2`, `T3`, `Xa`, `Y1`, `Y2`, Lemma E at `56`, `14`, `46`, Corollary 13.3 in general form | `NF29.k3_facts`, `not_both_depthSep_gen`, `NF29.isRupert_k3_P14`, `NF29.isRupert_k3_P11`, `NF29.isRupert_k3_X`, `NF29.isRupert_k3_P13`, `k3_Y2_core`, `NF29.isRupert_k3_Yp`, `NF29.planar_unimodal`, `NF29.k3_R_empty`, `NF29.isRupert_k3_notR`, `K3Gen`, `NF29.isRupert_K3a`, `NF29.isRupert_K3b` |
| `Type29Cover` | Type 29, classes K4 and K3 with Theorem P: Lemma E at the E-good quad edges of `O` (clause C1 in coordinates) and the full class theorems | `K4C1Gen`, `K3C1Gen`, `NF29.isRupert_K4a_all`, `NF29.isRupert_K4b_all`, `NF29.isRupert_K3a_all`, `NF29.isRupert_K3b_all` |
| `Type29Facets` | Type 29 from its facets: the normal form of an `IsCap29` point set (Lemma 21.1, facet signs as determinant ratios) and the class theorems | `facet_ratio`, `IsCap29.nf29_core`, `IsCap29.det_ne`, `IsCap29.toNF29`, `isRupert_type29_K4`, `isRupert_type29_K3` |
| `Type16` | Type 16, Lemma 11.U and Corollary 11.Ua of `FEWER-FACES-PROOFS.md` §11 addendum: screen coordinates of an edge view from two face functionals, the rim tests by `det3_frame`, part (b) in reals, the closing decision, the core in coordinates and from facets; `Type16` (facets), `σ = (0 6)(1 2)`, `MidOf`, "35 is bad", the far ends of `0235`, `1356` | `affine_frame3`, `det3_frame`, `frame_coords`, `isRupert_quad_rim`, `lemmaU_b_real`, `lemmaU_nws4`, `lemmaU_coords`, `lemmaU_facets`, `Type16`, `Type16.sigma`, `MidOf`, `Type16Bad35`, `plane_quad_coords`, `quad_middle`, `isRupert_type16_35`, `type16_not_bad35_of_far`, `type16_not_bad35_of_acute` |
| `Type16M` | Type 16, Theorem M′ (conditional): the octahedral region `Oct16`, Lemma 11.1 (`5*`, `K*` type 08), S1 at `ℓ` (third quadrilateral, T4 case in `K*`, N2), S2's N2 branch (Lemma 11.5), Proposition 11.V (R1, R2, Lemma 11.8 at `24`), Gale-form wrappers, `Type16Clause` and the theorem (the entry point is §19, `Type16Main`) | `Oct16`, `Oct16.five_beyond`, `Oct16.star`, `Oct16.facets`, `Oct16.isCap`, `middle_Qbc_of`, `isRupert_type16_N2`, `type16_not_bad35_thirdQuad`, `t4_not_bad'`, `type16_not_bad35_T4`, `type16_lemma5_mid`, `isRupert_type16_S2N2`, `isRupert_quad_rim_coords`, `isRupert_type16_24`, `type16_R1`, `type16_R2`, `isRupert_type16_V`, `Type16Clause`, `isRupert_type16_M` |
| `OctAxis` | `FEWER-FACES-PROOFS.md` §13 (two-test certificates), Euclidean form: the angle lemma for 4-corner rims (Lemma 13.2, Corollary 13.3: depth-separated diagonals whose projections meet along both views force the sign of `⟪u₁, u₂⟫`; shared-diagonal form), the cluster signs of every octahedron (Lemma 13.4), the views and middles (Lemma 13.5), the sign identity (Lemma 13.6, by the dependencies `[a ·]`, `[b ·]` and Plücker, no continuity step), Proposition 8.8 with Theorem 7.3 at a vertex view from determinant tests, the test at `a'` (triangle or quadrilateral rim; extra points hidden or middles at the apex), Theorem 13.7 (the octahedral axis lemma) and the lift 13.8 (i), (ii) to `K = O ∪ {m}` | `dep_eq_zero_of_two`, `galeD_ne_zero`, `pole_signs'`, `cluster_signs`, `axisView`, `axisView_eq_neg`, `axis_sign`, `axis_sign_two`, `SegMeet`, `DepthSep`, `depthSep_meet_sign`, `depthSep_det_sign`, `not_both_depthSep`, `axis_test_facts`, `isRupert_of_vertexView`, `AxisHidden`, `ApexMid`, `AxisExtra`, `overlap4_of_not_depthSep`, `isRupert_axisTest_core`, `segMeet_of_sides`, `axisTest_meets`, `isRupert_axisTest`, `isRupert_octAxis_gen`, `isRupert_octAxis`, `isRupert_octAxis_lift` |
| `EdgePair` | `FEWER-FACES-PROOFS.md` §14 (edge pairs), Euclidean form: Lemma E (two 4-corner closings at an edge crossing along `vw`, view `u = w − v`; `[a b c v] [a b c w] ≤ 0` excludes both rims being depth-separated, so one closing is unimodal), the parameter form, (ii) ⟺ (iii), the converse for depth functionals, Corollary 14.1 (Theorem 8.9 with Theorem 7.3 for either closing, middles and hidden points allowed; triangle closings), the wedge argument and Proposition 14.3 (E06: `[3450] [3456] < 0` on every type 16; the pair at `06` certifies `K` when `1`, `2` are hidden) | `edgePair_param`, `edgePair_not_both`, `edgePair_unimodal`, `SegMeetsTri`, `edgePair_tri_iff`, `edgePair_converse`, `EdgeHidden`, `EdgeMid`, `isRupert_edgePair_closing`, `isRupert_edgePair`, `wedge_sep`, `type16_sep06`, `isRupert_type16_06`, `RdHidden`, `isRupert_edgeTri`, `isRupert_type16_06_tri` |
| `Type16NF` | Type 16, the normal form of §19.0: frames (`nfP`, `nfV`, `det3_nfV`), `NF16` with the type inequalities, `Type16.toNF` from the facets, `NF16.sigma`, R1 and R2; certificates in either orientation; tools (`nf_test`, `nf_vec`, `depth_nodup4`, `eq_comb_div`, `meet_of_smul`) | `nfP`, `nfV`, `det3c`, `det3_nfV`, `NF16`, `NF16.R2_neg_of_R1`, `NF16.sigma`, `Type16.nf_core`, `Type16.toNF`, `isRupert_edgePairσ`, `isRupert_edgeTriσ`, `isRupert_edgePairσ_robust`, `isRupert_edgeTriσ_robust`, `isRupert_of_edgeViewσ`, `isRupert_of_vertexViewσ`, `exists_sign`, `nf_pos`, `depth_nodup4`, `depth_nodup3`, `depth_far3`, `depth_tri3` |
| `Type16Cover` | Type 16, Theorem 19.2 (the Lemma E cover in `R1`) and Proposition 14.3 off `R1 ∪ R2`, step by step in the normal form, as certificates `Cert16`; Lemma 19.1; the residual `Ω` | `NF16.cert_E06`, `NF16.cert_stepA`, `NF16.cert_stepU1a`, …, `NF16.cert_stepD7`, `NF16.g_gt_one`, `NF16.q_gt_b`, `NF16.Gen`, `NF16.Omega`, `NF16.cert_R1_or_omega` |
| `Type16Rims` | Single tests with explicit quadrilateral and pentagonal rims, at edge and vertex views, in either orientation | `quad_unimodal`, `isRupert_vquadσ`, `isRupert_vquintσ`, `isRupert_equadσ`, `isRupert_equintσ`, `Pent15`, `PentIn` |
| `Type16Pairs` | Type 16 on `Ω`: Lemma 19.3 (pair `T1`, `T2`), Lemma 19.4 (pair `A`, `B`), Lemma 19.5 (triple `T_a`, `A`, `T_c`); the views `vT2`, `vA`, `uA`; the four-corner rule (also with ties) and the depth patterns of the pentagons (also their open, tie-tolerant forms) | `depthSep_of_meet`, `depthSep_sign`, `not_weakSep_of_meet`, `eq_of_weakSep_meet`, `weakSep_sign`, `quint_B_robust`, `quint_Tc_robust`, `quint_A_robust`, `cone_inner3`, `NF16.vT2`, `NF16.vA`, `NF16.uA`, `NF16.named_vT2`, `NF16.named_vA`, `NF16.named_uA`, `NF16.cert_F3`, `NF16.cert_F1s`, `NF16.cert_T6`, `quint_B_unimodal`, `quint_Tc_unimodal`, `quint_A_unimodal` |
| `Type16Main` | Type 16, Theorem 19.6 (the cover, certificate form) and its special positions from the points and facets; from a certificate to Rupertness | `NF16.cert_omega`, `NF16.cert_R1`, `NF16.cert_nf`, `NF16.Gen.of`, `NF16.Views.of`, `Type16.noSeg`, `Cert16.isRupert`, `Type16.noHDN_views`, `NF16.isRupert_type16`, `ViewAff16`, `LineAff16`, `isRupert_type16_facets` |
| `Type16Limit` | Type 16, §18.6 step 2 and Theorem 19.8: normal-form shapes from parameters, the special positions of the cover as one nonzero polynomial and the density of its nonvanishing set, the tie-restoring shear, ties at the named views (`OneTie16`), the limit certificate; type 16 outside the HDN set and codimension 2 | `nfShape`, `NF16.ofParams`, `genPoly16`, `genPoly16_ne_zero`, `exists_seq_eval_ne_zero`, `restore`, `det3_restore`, `TieInst16`, `SameTie16`, `OneTie16`, `oneTieAt_of_ties`, `eventually_ties`, `Cert16.exists_certL`, `isRupert_of_cert_seq`, `exists_certSeq16`, `isRupert_type16_limit`, `isRupert_type16_limit_facets` |
| `Type16Sector` | Type 16, §22.2 at the two-triangle views: the views, (G1) there, the hiding tilt of the limit rim, the limit lemma with the tilt alternative, the facets form | `triEdge16`, `TriVtx16`, `Sec16`, `Sec16.tiltHides`, `Face16.det3_ne`, `isRupert_of_cert_seq_sec`, `isRupert_type16_limit_sec`, `HDNOrG1Edge`, `HDNOrG1Aff`, `isRupert_type16_limit_facets_sec` |
| `UniformTilt` | `FEWER-FACES-PROOFS.md` §16 part K: Lemma 16.27 (the uniform tilt: Theorems 8.8 and 8.9 with the single tilt `ω × u₀ + η v′`; a middle over any certified chord is exposed only when its depth offset helps it, and the axle gets a certificate in each of the four sectors of Lemma F, the mixed ones by the screen Plücker identity) and Lemma 16.27′ (doubles: any finite set of vertices over certified corners), each with Theorem 7.3; determinant-test forms, a 4-corner closing, and Corollary 14.1 with middles over any side of the shadow (Lemma E picks the closing) | `det3_plucker_screen`, `det3_apex_tilt`, `eventually_chord_choice`, `eventually_axle_uniform`, `isRupert_of_edgeChords_uniform`, `isRupert_of_edgeChords_uniform_unimodal`, `isRupert_of_uniform_doubles`, `isRupert_of_uniform_doubles_unimodal`, `isRupert_of_edgeView_uniform`, `isRupert_quad_uniform`, `isRupert_edgePair_uniform` |
| `RobustUnimodal` | `FEWER-FACES-PROOFS.md` §18.0, 18.3, 18.4: robust unimodality (R1)–(R3), cyclic subsequences, triangles, planar rims, one tie, limits; Steps 2–4 of Theorem 7.3 with weakly monotone runs; Theorem 18.3 | `IsRobustUnimodal`, `IsRobustUnimodal.comp`, `isRobustUnimodal_three`, `IsCcwPolygon.isRobustUnimodal_affine`, `isRobustUnimodal_of_single_tie`, `isRobustUnimodal_of_tendsto`, `deg_lemma_weak`, `forces_parallel_weak`, `hasHorizontalDoubleNormal_of_forces_robust`, `isRupert_of_robustUnimodalView` |
| `RobustCert` | Theorem 18.3 in the certificate forms (Propositions 8.8, 8.9, Lemma 16.27, Theorem 18.1 in its tie form, determinant-test views) | `exists_tiltCert_of_robustUnimodal`, `isRupert_of_uniform_doubles_robustUnimodal`, `isRupert_of_edgeView_robust`, `isRupert_of_vertexView_robust` |
| `RobustAxis` | The vertex test of Theorem 13.7 with ties: triangle and 4-corner rims (`QuadTie`) | `QuadTie`, `isRobustUnimodal_quad`, `isRupert_axisTest_core_robust`, `isRupert_axisTest_robust` |
| `RobustEdge` | Lemma E with ties (one closing `NWS4` unless the far depths are equal) and its Rupert forms; the quad lift of Lemma 9.3 with ties; general position up to single ties (`GenPosTie`); robust unimodality by perturbation | `NWS4.isRobustUnimodal`, `edgePair_nws_core`, `edgePair_nws`, `edgePair_robust`, `isRupert_edgePair_robust`, `isRupert_edgeTri_robust`, `isRupert_edgePair_uniform_robust`, `isRupert_quad_edge_lift_tie`, `nws4_of_planar_quad_tie`, `OneTieAt`, `GenPosTie`, `isRobustUnimodal_of_perturb`, `isRobustUnimodal_of_nhds` |
| `LimitCert` | Lemma 18.2 (limit certificates) at the limit shape's own metric, with 18.4 (α) and pairs; Rupert forms with 18.1 and 18.3 | `cycBetween_of_tendsto`, `isRobustUnimodal_cornerRim_of_tendsto`, `isRupert_of_limitCertificate`, `isRupert_of_limitCertificate_tie` |
| `LimitRim` | Lemma 18.2 (a)–(c) with the corner rim constructed: frame-free labelled certificates, hulls in support-function form, the rim only loses corners (Krein–Milman), robust unimodality with kept ties; the Rupert form | `RimCertAt`, `SuppIn`, `suppIn_of_tendsto`, `cyc_nonneg_of_tendsto`, `isRobustUnimodal_of_tendsto_ties`, `exists_cornerRim`, `IsCcwPolygon.mem_side_of_mem_convexHull`, `frequently_exists_of_finite`, `isRupert_of_tendsto_rimCert` |
| `Sector` | Proposition 22.2: robust unimodality is open in the depth order, the tilt that hides the side points, the cone of tilts from two face normals, two triangles, the limit lemma with the tilt alternative, (G1) at a view | `IsRobustUnimodal.not_weak_peaks`, `IsRobustUnimodal.isCyclicUnimodal_of_order`, `TiltHides`, `isRupert_of_tiltHides`, `exists_tiltHides_of_normals`, `G1Tri`, `cross_tri_sides`, `exists_tiltHides_tri`, `RimCertAt.lab_injective`, `isRupert_of_tendsto_rimCert_or`, `ParOnly`, `NoParAt`, `G1Edge`, `G1Vtx`, `RimCertAt.not_axle`, `exists_tiltHides_limit`, `cross_ne_zero_of_noSeg` |
| `RimCert` | Rim certificates in point form (the part of a crossing test that passes to limits) and their producers; ties at segment views | `RimCertPts`, `RimCert`, `RimCertPts.toAt`, `rimCertPts_of_class`, `rimCertPts_quad`, `rimCertPts_tri`, `rimCert_edgePair_robust`, `rimCert_edgeTri_robust`, `TieSeg` |
| `Type21Tier` | `FEWER-FACES-PROOFS.md` §16, tiers Q and H: Lemma 16.1 in Gale form (E-good quad edges: the two facet inequalities and "not bad"), Q at the eight directed K-quad edges of `K − 2` and of `K − 6`, H at `1 → 3`, `1 → 5` (the cap hidden from the facets) | `EGoodQuad`, `not_bad_of_egood`, `EGoodQuad.tests`, `Type21Q`, `cert_type21_Q`, `cert_type21_Q2`, `Type21H`, `cert_type21_H`, `cert_type21_H2` |
| `Type21Cover` | §16.0–16.3, 16.11, 16.12: dependencies from values, the normalized cap-face class and its cross brackets, the cap parameter `τ`, two dependencies of `K − 6` (Lemma 16.2), the facet values in brackets, the bracket identities, Lemma 16.11 (A1), Lemma 16.12, `Q` at `25` and at `23` of `K − 6` | `isDep_of_values`, `GaleData.flip`, `CapNorm`, `type21_cross_signs`, `IsCap21.gale_rel`, `IsCap21.tau`, `type21_depO2_c`, `type21_depO2_a`, `type21_f014`, `type21_r_pos`, `type21_A1`, `cert_type21_step3`, `cert_type21_step5`, `type21_lemma1612` |
| `Type21F1` | Lemma 16.7 (F1): the depth analysis of the pentagon `(0, 6, 2, 5, 1)` (16.7 (d)) and its tie form (one tie, by perturbation), a five-corner edge view in either orientation, the edge crossing `Y` along `04` (twenty determinant tests from the faces), `T1` and the sign argument | `type21_Y_unimodal`, `type21_Y_robust`, `isRupert_quint_rim`, `isRupert_quint_rim_robust`, `cert_type21_Y`, `cert_type21_F1` |
| `Type21F2` | Lemma 16.8 (a) (vertex separation, every octahedron) and Lemma 16.9 (F2: two vertex tests at `4` sharing the diagonal `[4, 5]`) | `vertex_sep`, `cert_type21_F2` |
| `Type21R` | Lemma 16.5 (R): a ridge view between two vertical faces (triangle rim with the last point hidden, or Lemma E), the type-21 ridge `26` in its four quadrants | `EdgeMid.swap_ab`, `rimCert_ridge`, `ridge_mid_far`, `ridge_mid_near`, `RidgeOK`, `Type21RQ`, `Type21R`, `cert_type21_ridge_quad`, `cert_type21_R` |
| `Type21Switch` | §16 parts L–M, the switch surface `δ_014(2) = δ_014(5)`: Lemma 16.28 (the view along `25`: the shadow `(p, P0, P4, P3)` from the faces `0256`, `014`, `235` parallel to the view, `1` over the far side `0 – 4`, `6` over the side `p – P0`), Lemma 16.29 (`2`, `5` on opposite sides of `034`, from `{1 ·}` of `K − 6`), Theorem 16.30 (Lemma E at `25` with the uniform tilt) | `det3_facet_prop`, `type21_switch_view`, `type21_switch_mid1`, `type21_switch_mid6`, `type21_switch_sep`, `cert_type21_switch` |
| `Type21Cap` | Theorem 16.13 (the cap-face class): ties from `NoPlaneParallel`, the R1 region, steps 1–5, the half `H⁻` of the switch surface by Theorem 16.30, the normalization by the Gale reflection, `σ1`, `σ2` | `facet_tie_det`, `T1Gen`, `cert_type21_capFace_norm`, `CapFace`, `Type21CapGen`, `cert_type21_capFace_O`, `cert_type21_capFace` |
| `Type21Entry` | Type 21 from its facets: the octahedron `K − 2` with its face `356`, the special positions of `T1` along a line of two faces | `image_seven21`, `exists_type21_cap`, `affine_linear_eq`, `T1View` |
| `Type21O2` | §16 addendum: Lemma 16.16 (the Step-1 pairs are E-good), the Gale data of `K − 6` with its values (Lemma 16.2) | `GaleQuad`, `step1_gale`, `arc_step1`, `type21_galeO2` |
| `Type21Other` | §16 addendum: Lemma 16.16 for `K − 2`, Theorem 16.18 (class (a)), Theorem 16.20 (class (b), R at the ridge `26` via the plane `145`), Lemma 16.21 (near or A1), `f ≠ 0`, the pair brackets of `K − 6`, Lemma 16.22, F1 in facet form | `type21_O_quad36`, `cert_type21_classA`, `IsCap21.rep2`, `cert_type21_classB`, `type21_plane145`, `type21_near_or_A1`, `gale_f_ne`, `type21_galeO2_kappa`, `type21_O2_quad04`, `cert_type21_F1'` |
| `Type21F2Case` | Lemma 16.24 (F2 on the rest of class (c)): the frame computations (`det3_scaled_combo`), a hidden point from a degenerate combination, the geometry of the two vertex tests, the Gale facts of step 1; Theorem 16.23 (class (c)) | `det3_scaled_combo`, `axisHidden_of_rel`, `F2ViewsL`, `cert_type21_F2_frame`, `cert_type21_F2case`, `cert_type21_classC` |
| `Type21Pattern` | The normal form `(+, −, +)` (classes (a), (b), (c) by the signs of `{5 4}`, `{0 3}`; the ties from `NoPlaneParallel`), the signs of `K − 6` (Lemmas 16.3, 16.14), Lemma 16.15 and Theorem 16.26 | `galeD_pair_ne_zero`, `cert_type21_pattern`, `type21_O2_signs`, `F2Views`, `Type21OtherGen`, `cert_type21_all` |
| `Type21Facets` | Type 21 from its facets (Theorem 16.26), certificate form | `cert_type21_facets` |
| `RimCertLift` | Rim certificates of the crossing tests of the type-21 tiers (§18.2): Theorem 8.9, Proposition 8.8 and Lemma 16.27′ at determinant views, the quad lift of Lemma 9.3 with ties, Corollary 14.1 with the uniform tilt, the vertex test of Theorem 13.7; certificates at named views (`CertV`); weak separations with one tie | `CertV`, `rimCertPts_of_edgeView_robust`, `rimCertPts_of_vertexView_robust`, `rimCertPts_of_edgeView_uniform_robust`, `rimCert_quad_edge_lift_tie`, `rimCert_edgePair_uniform_robust`, `rimCert_axisTest_gen`, `rimCert_axisTest_robust`, `OneTie4`, `NoTieAt`, `weakSep_of_not_robust`, `lt_of_le_of_noTie` |
| `Type21LiftCert` | Lemma 3 of §9 (the eight directed K-quad edges of tier Q) in certificate form | `cert_type21_05`, `cert_type21_06`, `cert_type21_60_far`, `cert_type21_60`, `cert_type21_50`, `cert_type21_43`, `cert_type21_34`, `cert_type21_46`, `cert_type21_64` |
| `Type21Limit` | Type 21, §18.6 step 2: the old entry statement from the certificates, normal-form shapes from parameters, the special positions of the cover as one nonzero polynomial, the named views and ties across them, the cover at a generic shape, the limit certificate; type 21 outside the HDN set and codimension 2 | `Facets21`, `Facets21.noSeg`, `isRupert_of_rimCert`, `isRupert_type21_facets`, `co21`, `nfShape21`, `Facets21.eq_nfShape`, `gen21`, `genPoly21_ne_zero`, `view21`, `Facets21.vtxView21_ne_zero`, `OneTie21`, `noTieAt_seg_of_tie`, `noTieAt_or`, `cert21_of_generic`, `exists_certSeq21`, `isRupert_type21_limit`, `isRupert_type21_limit_facets` |
| `Type21Sector` | Type 21, §22.2 at the two-triangle views (as `Type16Sector`) | `triEdge21`, `TriVtx21`, `Sec21`, `Sec21.tiltHides`, `isRupert_of_cert_seq21_sec`, `isRupert_type21_limit_sec`, `isRupert_type21_limit_facets_sec` |
| `Type24` | `FEWER-FACES-PROOFS.md` §15 (type 24 outside `C̄ ∪ Σ_B`): oblique coordinates at the cap `1` by Cramer's rule, the side coefficients `ω` and `Δ`, the window triangle (Theorem 15.4, Theorem 5 at a view in the tangent cone), the side crossings as triangle tests (Lemma 15.5, Theorem 15.7), Corollary 15.8 | `cramer_vec`, `isRupert_vertexTri`, `isRupert_window_frame`, `isRupert_sideCrossing_frame`, `Type24`, `omega3`, `Delta24`, `omega_identity`, `isRupert_type24_window`, `isRupert_type24_B`, `isRupert_type24_outside_Cbar` |
| `Type24Cap` | `FEWER-FACES-PROOFS.md` §17 at every metric: Lemma C (Theorem 17.10, the cap-edge crossings with explicit `δ`, the arch of the far path, `(H-cap)` from 17.9), Lemma Q / Q′ (17.4, 17.19, the planar quad), Lemma 17.15 (8.8 for disjoint faces) | `exists_arch`, `isCyclicUnimodal_of_arch`, `capStep_of_cos`, `capEdge_unimodal`, `isRupert_capEdge`, `CapRim`, `isRupert_capEdge_frame`, `isRupert_type24_E2`, `isRupert_type24_E6`, `isRupert_type24_capEdge`, `noInteriorMin_of_mid3`, `Fails4`, `planarQuad_fails4`, `planarQuad_unimodal`, `isRupert_quadView`, `isRupert_planarQuad`, `isRupert_disjointFaces` |
| `Type24Corner` | `FEWER-FACES-PROOFS.md` §17 on the circle of `236` and at exact corners: the circle identity (17.3 (c)), M3 at every metric (BB) and at the corner (17.7), one ratio on circle 2 (17.14 (a)), the closed forms (17.5, 17.17 (b)–(d)), M1 (17.8), the T′ pair, M3′ (17.18), Rupert forms | `circle_depth`, `m3_not_both`, `ExactCorner`, `Type24.depth_corner`, `Type24.m3_corner`, `Type24.fails4_circle2_iff`, `Type24.pencil_0264`, `Type24.m1_corner`, `Type24.tpair_corner`, `Type24.m3prime_corner`, `QuadTest'`, `isRupert_of_two_tests`, `isRupert_m3`, `isRupert_m3_corner`, `isRupert_m1_corner`, `isRupert_tpair_corner`, `isRupert_m3prime_corner`, `isRupert_type24_Q` |
| `Type24WP` | `FEWER-FACES-PROOFS.md` §17 (rest): Lemma W, WP as a Rupert item and M1 with WP discharged, L7 (15.15, 17.8′), the arc criterion 17.16′ on circle 2 and its pair form, the radii 17.1, 17.1′, 17.11 and 17.12 with WP_2 | `isRupert_lemmaW`, `isRupert_wp`, `isRupert_wp2`, `isRupert_wp6`, `Type24.m1_corner_Ioo`, `isRupert_m1_corner_wp`, `l7_frame_corner`, `l7_frame_radius`, `isRupert_l7_t26`, `isRupert_l7_t26_radius`, `Type24.arc_criterion2`, `Type24.arc_criterion2_wp`, `pair_rule`, `Type24.circle2_pair`, `isRupert_circle2_pair`, `radius_pos`, `radius_pos_octant`, `Type24.wpChain2_octant`, `isRupert_type24_near_wp2` |
| `Type24Metric` | `FEWER-FACES-PROOFS.md` §20.1, 20.2, 20.6, 20.8: depth covectors, Lemma C without a radius (the dip mechanism), acute-safe cap edges, `S_0` with `E_05` at the exact corner, Conjecture A for two acute-safe cap edges | `fails4_iff_covFails`, `isCyclicUnimodal_of_noDip`, `CapRim0`, `isRupert_capEdge_noDip`, `isRupert_capEdge_mid3`, `AcuteSafe`, `acuteSafe_four`, `Type24.safeE2_of_four`, `isRupert_type24_two_safe`, `Type24.obtuse_of_two_safe`, `Type24.s0_e05_corner`, `isRupert_s0_e05_corner` |
| `Type24Chain` | `FEWER-FACES-PROOFS.md` §20.3–20.5, 20.9: WP at the view `t3`, the window chain at every metric, the closed obtuse octant, the uniform statement | `wpChain_after`, `wpView_t3`, `isRupert_wp2_after`, `windowChain`, `WindowChain`, `isRupert_windowChain2`, `isRupert_windowChain6`, `isRupert_windowChain_octant`, `isRupert_type24_uniform` |
| `Type24Side` | `FEWER-FACES-PROOFS.md` §20, continued (11, 12): the sink lemma 20.2 (d) and its `m = 2` corollary, the common sink, side-safety and Theorem 20.8′ (Conjecture A when each cosine is seen on a safe side), Theorem 8.10 as a cap-edge item | `exists_dip_of_not_unimodal`, `CapRim0.path`, `capRim0_sink`, `Type24.sinkE2`, `Type24.sinkE0`, `capRim0_five_fails_iff`, `common_sink`, `SideSafe`, `Type24.SideCovered`, `isRupert_type24_side_safe`, `Type24.obtuse_of_side_safe`, `not_fails4_of_depthSepAt`, `isRupert_capRim0_uos` |
| `Type24Lambda` | `FEWER-FACES-PROOFS.md` §20, continued (13, 14): Lemma 20.10 (OO's identity, both clauses), Corollary 20.11, Theorem 20.4″ (the chain without `r4 > 1`), the window chain in general form, Theorem 20.9′ | `Lambda.lemma_20_10`, `Lambda.lemma_20_10_strict`, `lemma_20_10_wp`, `windowChain_gen`, `wpL2_of_poly`, `ChainData`, `isRupert_chainData2_L2`, `WindowChainΛ`, `isRupert_windowChainΛ_octant`, `isRupert_type24_uniform_side` |
| `Type24Circle236` | `FEWER-FACES-PROOFS.md` §20, continued (2): Lemma 20.12 (UU's S1, S2, S4, S5, the linear identities of Theorem 20.13 on depth values; connected to `IsRupert` in `Type24Circle`) | `Cu13.S1`, `Cu13.S2`, `Cu13.S4`, `Cu13.S5` |
| `Type24DS` | `FEWER-FACES-PROOFS.md` §20, continued (3): Corollary 20.19 (the planar quad rim), Lemma 20.18 (Lemma Y; cu14's core moved in), DS side-safety (Theorems 20.16, 20.17), the acute side by 20.17–20.19 | `planarRim_coeffs`, `QuadTest'.isRupert_planar`, `isRupert_type24_planarQuad`, `Cu14.lemmaY`, `lemmaY_core`, `YBelow`, `isRupert_lemmaY`, `isRupert_lemmaY_bc`, `DSSafeQ`, `isRupert_capEdge_dsSafe`, `Type24.DSSideCovered`, `Type24.DSRegionsCovered`, `isRupert_type24_dsSide`, `isRupert_type24_dsRegions`, `Type24.AcuteCovered`, `isRupert_type24_acute` |
| `Type24Circle` | `FEWER-FACES-PROOFS.md` §20, continued (2), (3): Theorem 20.13 (closed and open obtuse octant), Corollary 20.14, Theorems 20.9″ and 20.9‴ | `Gram3`, `K236bar`, `K236`, `EdgeRim`, `isRupert_edgeRim`, `e23_cases`, `Type24.c5_lt_of_rimT62`, `Type24.s1_pattern`, `isRupert_circle236_octant`, `isRupert_circle236_open`, `Type24.ObtuseCovered`, `isRupert_type24_obtuse_octant`, `isRupert_type24_uniform_circle`, `isRupert_type24_uniform_ds`, `isRupert_type24_uniform_acute` |
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
