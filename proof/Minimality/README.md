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
  on the `s`-side of each segment of that ray's chain, distinct depths along
  the cycle, and `s z_A > s z_B`: the tilt `-s r1 + s r2` is unimodal, so `V`
  is Rupert. Unimodality is `tri_localMax_unique` (every local maximum of
  `s z` lies on the concave chain).
* `isRupert_twoQuads_frame` (`TriQuad.lean`): two quadrilaterals sharing the
  apex, one on each ray, each convex in its `(t, z)`-plane (either
  orientation), distinct positive `t` on each, seven distinct depths: Rupert.
  `quad_chain` gives the upper and lower chains of a convex quadrilateral seen
  from a vertex (six cases plus relabelling). Next: the bridge from two
  quadrilateral facets of a 7-point set sharing one vertex (types 02, 07, 09,
  14, 18, 20 by Corollary T1): rotation of the view `n1 × n2` to `ez`,
  oblique coordinates, and the convex cyclic order of each quadrilateral from
  extremality.

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
| `TriShadow` | L13, Lemma T (triangle shadow), oblique frame | `tri_localMax_unique`, `oblPt_inj`, `isRupert_triShadow`, `isRupert_triShadow_injOn` |
| `TriQuad` | L13, two quadrilaterals sharing a vertex (Corollary T1), oblique frame | `quad_chain`, `ChainOK.far_eq`, `isRupert_twoQuads_frame` |

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
