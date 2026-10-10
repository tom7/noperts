module

public import SmallRupert.Basic
public import SmallRupert.FirstOrder
public import SmallRupert.DoubleNormal
public import SmallRupert.Coplanar
public import SmallRupert.Planes
public import SmallRupert.Pyramid
public import SmallRupert.Crossing
public import SmallRupert.FewVertices
public import SmallRupert.BicappedTetrahedron
public import SmallRupert.SixVertices
public import SmallRupert.CycSeq
public import SmallRupert.Polygon
public import SmallRupert.Thm73
public import SmallRupert.BadViews
public import SmallRupert.Perturb
public import SmallRupert.Unimodal
public import SmallRupert.Octahedron
public import SmallRupert.Prism
public import SmallRupert.Tilt
public import SmallRupert.RightPrism
public import SmallRupert.L8Shapes
public import SmallRupert.L8T4
public import SmallRupert.L8T3
public import SmallRupert.Witnesses
public import SmallRupert.OctahedronAll

/-!
# SmallRupert: Rupert theorems for small polyhedra (overview)

Formalization of `nopert229/notes/LEMMAS.md` against `IsRupert` from
`Noperthedron/MainTheorem.lean`.  `V : Finset ℝ³` is the vertex set (it may
contain non-extreme points).  Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`.  Headline theorems:

**Lemma 1 and the coplanar silhouette (L1–L5)**
* `isRupert_of_firstOrderInward` — a strictly inward first-order motion gives a passage (L1).
* `isRupert_of_crossing` — Theorem 5, frame-free crossing form.
* `isRupert_of_admissibleViews_nonempty` — Theorem 5 (an admissible coplanar view).
* `isRupert_of_pyramid` — Cor. 5.3: pyramids.
* `isRupert_of_segment_crossing` — Cor. 5.4: bipyramid lemma, crossing form.
* `isRupert_bipyramid` — bipyramids over any waist polygon (via `isRupert_of_waist`).
* `isRupert_of_card_le_five` — Cor. 5.6: every polyhedron with at most 5 vertices.
* `isRupert_bicappedTetrahedron` — Cor. 5.7: every bicapped tetrahedron (T7).

**Six vertices (L6)**
* `isRupert_frustum` — T1 frustum (three lateral lines through a point).
* `isRupert_parallelPrism` — T1 with parallel lateral edges, not a translation prism.
* `isRupert_cappedSquarePyramid` — T5 unless `S₁S₄ ∥ S₂S₃`.

**Unimodal silhouettes (L7)**
* `exists_forces_of_not_firstOrderInward` — Lemma 7.1 (needed direction).
* `hasHorizontalDoubleNormal_of_forces` — Theorem 7.3 (⇒), pure polygon form.
* `isRupert_of_unimodalView` — Theorem 7.3 at an explicit view.
* `exists_badPlanes` — Lemma 7.4: bad views lie on finitely many great circles.
* `isRupert_of_genericUnimodalView` — Theorem 7.5 (plus `isRupert_of_open_unimodal`).
* `isRupert_translationPrism` — Theorem 7.7: translation prisms, unless right over a non-obtuse triangle.
* `isRupert_octahedron_conditionA` — Cor. 7.8: octahedra with Condition A.

**Tilting off degenerate views (L8)**
* `isRupert_of_tiltCert` — frame-free Lemma 1 with local certificates.
* `eventually_tilted_cycle` — Lemma 8.0, instance-wise determinant form.
* `isRupert_of_tilted_unimodal` — Cor. 8.0′ (robust unimodality).
* `isRupert_rightPrism` — Theorem 8.1: every right prism over a convex polygon.
* `isRupert_translationPrism_all` — every triangular translation prism (7.7 + 8.1).
* `isRupert_cappedSquarePyramid_all` — Theorem 8.2: every T5.
* `isRupert_T4` — Theorem 8.3: every T4.
* `isRupert_T3` — Theorem 8.4: every T3.

**Every octahedron (L9)**
* `isRupert_octahedron` — Theorem 9.9: every convex octahedron (`IsOctahedron`, type T6).
* `isRupert_planar_equator` — an octahedron with a planar equator (Cor. 5.4).
* `isRupert_of_touching_pair` — Lemma 9.4: two touching quad edges (axis view).
* `isRupert_quad_edge` — Lemma 9.3: a quad edge that is neither bad nor touching.
* `isRupert_octahedron_generic` — §9.5: the Gale-diagram selection (`f ≠ 0`).
* `isRupert_weak_edge` — Lemma 9.11: weak quad edges (parallel faces).
* `isRupert_octahedron_parallel` — §9.6: the case `f = 0`.
* `isRupert_of_tilted_unimodal_σ` — Cor. 8.0′ for either orientation (eventual `Q`,
  covering the lexicographic tie-breaks of Cor. 9.0).

**Non-vacuity** (`Witnesses.lean`): explicit rational instances of every
hypothesis structure (`IsBicappedTetrahedron`, `IsCappedSquarePyramid` generic
and with `S₁S₄ ∥ S₂S₃`, `IsT4`, `IsT3` generic and with `BB' ∥ CC'`,
`IsOctahedron` with Condition A), each fed to its headline theorem (the
octahedron also to `isRupert_octahedron`).

Not formalized: the 6-vertex classification itself (that every convex polyhedron
with 6 vertices is one of T1–T7 with the stated face structure), the L3/L2(d)
obstruction directions, and the conjectures of LEMMAS.md.
-/
