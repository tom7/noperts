# SmallRupert: proof plan

Formalization of `nopert229/notes/LEMMAS.md` (coplanar silhouettes) against
`IsRupert` from `Noperthedron/MainTheorem.lean`. Build: `lake build SmallRupert`
(imports only Mathlib and `Noperthedron.Rupert.Basic`).

## Status

Fully proved (axioms: propext, Classical.choice, Quot.sound only):
- `isRupert_bipyramid` (any number of waist points), via the waist lemma
  `isRupert_of_waist` (Pyramid.lean);
- `isRupert_of_crossing` (Crossing.lean): Theorem 5 in any frame, with the
  "line through `v` meets a positive combination of `W`" hypothesis;
- `isRupert_of_admissibleViews_nonempty` (general L5, LEMMAS.md's `U_Π ≠ ∅`),
  `isRupert_of_segment_crossing` (Cor. 5.4), `isRupert_of_pyramid` (Cor. 5.3);
- `isRupert_of_card_le_five` (Cor. 5.6), via a minimal hull subset, the
  pyramid case, and Radon's theorem for five points in general position;
- `isRupert_bicap_normalForm` and `isRupert_bicappedTetrahedron` (Cor. 5.7);
- on the way: L1, L2 realization, L3 existence (general convex polygon), the
  L4 transfer, rotation/translation invariance of `IsRupert`.

- six vertices (SixVertices.lean): `isRupert_frustum` and
  `isRupert_parallelPrism` (T1 except translation prisms),
  `isRupert_cappedSquarePyramid` (T5 with facet hypotheses, unless
  `S₁S₄ ∥ S₂S₃`) and its normal form `isRupert_cappedSquarePyramid_normalForm`.

Still `sorry` (none is used by the theorems above): the L3 obstruction and
L2(d) obstruction (optional), the `⇒` halves of L2/L4 iffs, L3.0 range form,
the generic-view density statements of Coplanar.lean (`dense_generic_...`,
`isOpen_admissibleViews`, `exists_firstOrderInward_of_coplanar`,
`isRupert_of_generic_admissibleView`).

- L7, unimodal silhouettes (all proved, standard axioms only):
  - Lemma 7.1, direction used: `exists_forces_of_not_firstOrderInward`
    (normal-cone form; no (G1) needed);
  - Theorem 7.3 (⇒), pure polygon form: `hasHorizontalDoubleNormal_of_forces`
    (CycSeq/Polygon/Thm73: sign-switch sequences, cyclic-order API for
    corners over `ZMod k`, no-zigzag, Step 5);
  - Theorem 7.3 at an explicit view: `exists_firstOrderInward_of_unimodal`,
    `isRupert_of_unimodalView`;
  - Lemma 7.4: `exists_badPlanes` (BadViews; stated without (G1)/(G2), the
    bad great circles come from `badDirs V`);
  - Theorem 7.5: `isRupert_of_genericUnimodalView`, plus the robust forms
    `isRupert_of_eventually_unimodal` and `isRupert_of_open_unimodal`
    (Perturb: openness of (G1)/interior/unimodality, density of views off
    finitely many great circles);
  - Theorem 7.7: `isRupert_translationPrism` (Prism; every translation prism
    except right prisms over non-obtuse triangles);
  - Corollary 7.8: `isRupert_octahedron_conditionA` (Octahedron).
- L8, tilting off degenerate views (all proved, standard axioms only):
  - frame-free Lemma 1 with local certificates `isRupert_of_tiltCert`;
    Lemma 8.0 instance-wise in determinant form `eventually_tilted_cycle`
    (`D0 ≥ 0`, `D0 = 0 ⇒ D1 > 0` per test, via `eventually_pos_affine`);
    Corollary 8.0′ `isRupert_of_tilted_unimodal` (Tilt);
  - Theorem 8.1: `isRupert_rightPrism` (every right prism over a strictly
    convex polygon, explicit motion, no L7), and with 7.7
    `isRupert_translationPrism_all` (every triangular translation prism)
    (RightPrism);
  - Theorem 8.2: `isRupert_cappedSquarePyramid_all` (every T5) (L8Shapes);
  - Theorem 8.3: `isRupert_T4` (every T4, structure `IsT4`) (L8T4);
  - Theorem 8.4: `isRupert_T3` (every T3, structure `IsT3`) (L8T3).
  The facet structures `IsT4`, `IsT3` (and the T5 exceptional case) were
  checked non-vacuous on exact rational examples (hull facets computed in
  Python), not in Lean.

## Modules and dependency order

| module | content (LEMMAS.md) | key statements |
|---|---|---|
| `Basic` | §0 setting | `IsInwardAt`, `IsDoubleNormalDir`, `screenVel`, `isRupert_iff_shadows`, rotation invariance, `isInwardAt_iff_forall_normal` |
| `FirstOrder` | L1 | `eventually_forall_mem_interior`, `eventually_innerShadow_subset`, `isRupert_of_firstOrderInward` |
| `DoubleNormal` | L3, L3.0, L4 transfer | `exists_admissible_inward_field` (L3 existence), `isDoubleNormalDir_convexHull_cases`, `isDoubleNormalDir_proj_iff'` |
| `Coplanar` | L2, L4, L5 | `exists_motion_iff`, `exists_firstOrderInward_of_plane`, `isRupert_of_admissibleViews_nonempty` |
| `Pyramid` | waist lemma | `isRupert_of_waist`, `isRupert_bipyramid` |
| `Planes` | plane utilities | `exists_plane_of_coplanar`, `det4`, `sum_smul_mem_interior_convexHull` |
| `Crossing` | L5 (any frame), Cor. 5.3, 5.4 | `isRupert_of_crossing`, `isRupert_of_admissibleViews_nonempty`, `isRupert_of_pyramid`, `isRupert_of_segment_crossing` |
| `FewVertices` | Cor. 5.6 | `isRupert_of_card_le_five` |
| `BicappedTetrahedron` | Cor. 5.7 | `isRupert_bicap_normalForm`, `isRupert_bicappedTetrahedron` |
| `SixVertices` | L6 (partial) | `isRupert_frustum`, `isRupert_parallelPrism`, `isRupert_cappedSquarePyramid` |
| `CycSeq` | L7 Thm 7.3 core | sign-switch sequences, `forces_parallel` |
| `Polygon` | corner API | `IsCcwPolygon`, `normalConeAt`, `normalCone_decomp` |
| `Thm73` | Thm 7.3 glue | `IsCyclicUnimodal`, `HasHorizontalDoubleNormal`, `noZig`, `hdn_of_parallel` |
| `BadViews` | Lemma 7.4 | `badDirs`, `exists_badDir_of_hdn` |
| `Perturb` | genericity | `IsCcwPolygon.mem_interior_iff`, `eventually_isCcwPolygon`, `exists_rotation_near_avoiding` |
| `Unimodal` | Lemma 7.1, Thms 7.3, 7.5 | `exists_forces_of_not_firstOrderInward`, `isRupert_of_genericUnimodalView` |
| `Octahedron` | Cor. 7.8 | `isRupert_octahedron_conditionA` |
| `Prism` | Thm 7.7 | `isRupert_translationPrism` |
| `Tilt` | Lemma 8.0, Cor. 8.0′ | `isRupert_of_tiltCert`, `eventually_tilted_cycle`, `isRupert_of_tilted_unimodal` |
| `RightPrism` | Thm 8.1 | `isRupert_rightPrism`, `isRupert_translationPrism_all` |
| `L8Shapes` | Thm 8.2, tools | `cmb`, `det3_cmb`, `NWS4`, `isRupert_cappedSquarePyramid_all` |
| `L8T4` | Thm 8.3 | `IsT4`, `isRupert_T4` |
| `L8T3` | Thm 8.4 | `IsT3`, `isRupert_T3` |

Order of work: Basic → FirstOrder → DoubleNormal → Coplanar (L2 + plane form
of L5) → `isRupert_bipyramid` → FewVertices → general L5 → Bicap → SixVertices.

Directions not needed by any Rupert theorem (optional): L3 obstruction
(`not_forall_inward_of_isDoubleNormalDir`), L2(d) obstruction
(`not_forall_inward_rigid`), the `⇒` halves of the L2/L4 iffs.

## Design choices

* **Inwardness** `IsInwardAt S p d := ∃ ε > 0, p + ε d ∈ interior S`. No
  H-representation of polygons is needed (Mathlib has no Minkowski–Weyl).
  Automatic at interior points, so `FirstOrderInward` quantifies over all of
  `V` (= LEMMAS.md's `V_∂` condition, `firstOrderInward_iff_frontier`).
  The normal-cone form (`isInwardAt_iff_forall_normal`) is used inside L3.
* **Double normals** by the general definition (chord `[a,b]`,
  `b − a ∈ N(b)`, `a − b ∈ N(a)`), in any real inner product space; no
  triangle special case (LEMMAS.md Cor. 3.1 was wrong).
* **Views.** Everything first-order happens in the standard view
  (`proj_xy`, depth = coordinate 2); a general view `u` is reduced by a
  rotation `R` with `R u ∥ ez` and `isRupert_of_isRupert_image_rotation`.
* **Rotation curve.** L1 is stated for any matrix curve with `R 0 = 1`,
  `R' 0 = [ω]×` entrywise (no matrix norm instance needed). The corollary uses
  the Cayley curve `cayley ((s/2) ω)` (same formula as
  `Noperthedron.cayleyMatrix`, SO(3) for every `s`, rational entries, so the
  derivative is `HasDerivAt.div` of polynomials). Preferred over
  `NormedSpace.exp`, where Mathlib lacks `det (exp A) = exp (tr A)`.
* **Coplanar theorem.** `W ⊆ V` arbitrary (not `V ∩ Π`), `Π = affineSpan W`,
  `admissibleViews V W` = `U_Π`. No vertex/convex-position hypotheses.
* **Cor. 5.4** is stated with the crossing hypothesis (segment `DE` meets
  `relint conv W`), not "opposite sides, no common face" (that implication
  needs polytope face theory absent from Mathlib).
* **Cor. 5.6** via Radon (`radon_partition`) instead of combinatorial types
  and Lemma 5.5.
* **Cor. 5.7** combinatorial hypothesis = eight `IsFacetTriangle`s (strict
  supporting planes), plus nodup and affine independence of `ABCT`.

## Hard steps and attack

1. **L1 analytic core** (`eventually_forall_mem_interior`). For each `i`:
   `IsInwardAt` gives `ε, r` with `ball (φ0 + ε d) r ⊆ S`. From
   `hasDerivWithinAt_iff_isLittleO` (on `Ici 0`, restricted to `𝓝[>] 0`):
   `‖φ t − φ0 − t d‖ ≤ (r/2ε) t` eventually. Then
   `φ t = (1 − t/ε) φ0 + (t/ε) y` with `y ∈ ball (φ0+εd) r ⊆ interior S`;
   `Convex.combo_closure_interior_mem_interior`. Uniformity:
   `Filter.eventually_all_finset`. Shadow: `AffineMap.image_convexHull` +
   `convexHull_min` + `Convex.interior`.
2. **Rotations.** `isRupert_image_rotation` already exists in
   `PentagonalHexecontahedron/IcoInstance.lean` (copy). Rotation taking unit
   `u = (a,b,c)`, `c ≥ 0`, to `ez`: explicit Rodrigues matrix
   `[[1 − a²/(1+c), −ab/(1+c), −a], [−ab/(1+c), 1 − b²/(1+c), −b], [a, b, c]]`;
   SO(3) by `field_simp; linear_combination` with `a²+b²+c² = 1`.
3. **L3 existence** (`exists_admissible_inward_field`), coordinates
   `x = ⟪û,·⟫`, `y = ⟪ŵ,·⟫`, `ŵ = J û`. Extreme faces `F_A`, `F_B` of `x`
   (`IsCompact.exists_isMinOn`); their `y`-images are compact convex subsets of
   ℝ, disjoint by "not a double normal" (L3.0), hence strictly separated by
   some `y₀` (`Real.convex_iff_ordConnected`). Field `v = w + δ z`:
   `w(p) = a + θ(p)(b − a) − p` (squash onto chord `[a,b]`, `θ` affine in `x`),
   `z(p) = κ(y₀ − y) û + τ(p) ŵ` with `τ` affine, `z(a) = μ_a (c − a)`,
   `z(b) = μ_b (c − b)` for an interior `c`. Both admissible
   (`⟪û, M û⟫ = 0`). Defect analysis on `Γ = {(p,n) : p ∈ W, ‖n‖=1, n ∈ N(p)}`:
   `⟪n,w(p)⟫ ≤ 0` always; if `= 0`, then either `⟪n,ŵ⟫ = 0` (so `n = ±û`, `p` in
   `F_B`/`F_A`, and `⟪n,z(p)⟫ = ∓σ < 0`) or `p` is on the chord (then `n` is a
   normal at `a` and/or `b` and `⟪n,z(p)⟫` is a convex combination of negative
   values). Uniform `δ` by compactness of `Γ` (`IsCompact.tendsto_subseq`).
   Conclude with `isInwardAt_iff_forall_normal` (⇐: separation
   `geometric_hahn_banach_open_point` + compactness of the unit sphere +
   `Convex.closure_interior_eq_closure_of_nonempty_interior`).
4. **L4 genericity.** `isDoubleNormalDir_convexHull_cases` (a chord end not in
   `W` is a positive combination of ≥ 2 minimizers, `Finset.mem_convexHull`),
   so bad views lie in finitely many planes `d^⊥`. Pick `u = u₀ + t ζ` with
   `ζ` avoiding all `d^⊥` (one-parameter family `(1, s, 0)`, finitely many bad
   `s`) and `t ∈ 𝓝[≠] 0` off a finite set; openness of `U_Π` keeps `u`
   admissible.
5. **L5 plane form glue.** Plane `⟪N, x⟫ = h`, `N 2 ≠ 0` gives depth
   `z = ⟪g, Px⟫ + c`; face-on (`g = 0`) excluded because a diameter is a
   horizontal double normal; `û = J g`, lifted `δ = (J g, 0)` lies in the plane
   direction; transfer (L4) + L3 + L2 + L1.
6. **General L5** needs `Π` 2-dimensional from `¬Collinear` and
   `u ∉ Π.direction` (`Submodule.finrank_lt`, `Collinear` ↔ rank ≤ 1) and the
   normal `N`. `isOpen_admissibleViews` needs the transversal intersection point
   to move continuously.

## Effort estimates (Lean lines, rough)

| module | estimate |
|---|---|
| Basic (rotations, normal-cone lemma) | 300 |
| FirstOrder (L1 + Cayley) | 300 |
| DoubleNormal (L3 existence, L3.0, finiteness, transfer) | 600 |
| Coplanar (L2, plane-form L5, genericity, general L5) | 600 |
| Pyramid (+ bipyramid) | 250 |
| FewVertices (Radon, extreme points) | 300 |
| BicappedTetrahedron (normal form 200, facets → normal form 400) | 600 |
| SixVertices | 400 |
