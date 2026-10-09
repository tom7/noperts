# SmallRupert: proof plan

Formalization of `nopert229/notes/LEMMAS.md` (coplanar silhouettes) against
`IsRupert` from `Noperthedron/MainTheorem.lean`. Build: `lake build SmallRupert`
(imports only Mathlib and `Noperthedron.Rupert.Basic`).

## Status

Fully proved (axioms: propext, Classical.choice, Quot.sound only):
`isRupert_bipyramid` (Tom's challenge, any number of waist points), and on
its path L1 (`isRupert_of_firstOrderInward`, `eventually_innerShadow_subset`,
Cayley curve), L3 existence (`exists_admissible_inward_field`, general convex
polygon), L2 realization (`exists_motion_of_admissible`), L4 transfer and
finiteness cases, the plane form of Theorem 5
(`exists_firstOrderInward_of_plane`), rotation invariance and rotations to the
standard view. Everything else is still `sorry`.

## Modules and dependency order

| module | content (LEMMAS.md) | key statements |
|---|---|---|
| `Basic` | §0 setting | `IsInwardAt`, `IsDoubleNormalDir`, `screenVel`, `isRupert_iff_shadows`, rotation invariance, `isInwardAt_iff_forall_normal` |
| `FirstOrder` | L1 | `eventually_forall_mem_interior`, `eventually_innerShadow_subset`, `isRupert_of_firstOrderInward` |
| `DoubleNormal` | L3, L3.0, L4 transfer | `exists_admissible_inward_field` (L3 existence), `isDoubleNormalDir_convexHull_cases`, `isDoubleNormalDir_proj_iff'` |
| `Coplanar` | L2, L4, L5 | `exists_motion_iff`, `exists_firstOrderInward_of_plane`, `isRupert_of_admissibleViews_nonempty` |
| `Pyramid` | Cor. 5.3, 5.4 | `isRupert_of_pyramid`, `isRupert_of_segment_crossing`, `isRupert_bipyramid` |
| `FewVertices` | Cor. 5.6 | `isRupert_of_card_le_five` |
| `BicappedTetrahedron` | Cor. 5.7 | `isRupert_bicap_normalForm`, `isRupert_bicappedTetrahedron` |
| `SixVertices` | L6 (partial) | frustum, parallel prism, T5 normal form |

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
