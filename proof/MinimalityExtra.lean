module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Side results of the minimality project (statements)

This file states, using only Mathlib, results found along the way to
`AnySevenVertexNopertIsSimplicial` that are of interest on their own. Proofs are in
`MinimalityExtra/` (Mathlib only where possible); `ProofOfMinimalityExtra.lean` ties the
definitions here to the rest of the repository. Each result is stated as a `def ... : Prop`,
as in `MainTheorem.lean`.

## The converse of the unimodal criterion fails

A *unimodal view* of a 7-vertex point set `x` is a direction `u` in which the silhouette is a
convex polygon whose corners are among the points, all other points lie strictly inside it,
and the depths `⟪x i, u⟫` of the corners, read cyclically, are distinct with exactly one local
maximum. The unimodal criterion says that a unimodal view gives a Rupert passage.
`ExistsFirstOrderPassageWithoutUnimodalView` says the converse fails: there is a 7-vertex
polytope (all vertices exposed, with a quadrilateral face) that has a first-order passage
(a view `w` and a motion `(ω, τ)` that moves every silhouette corner strictly inward) but
has no unimodal view at all.

## Which depth conclusions hold at every metric

A view `v` comes with a choice of metric, a positive definite matrix `G`, and the depth of a
point `x` along the view is `⟪G v, x⟫`, so the depth functional is `l = G v`. Depth on a coplanar
rim is unimodal at every metric (`CoplanarRimDepthUnimodal`); four non-coplanar points are
two-peaked at some metric, whatever the view (`TwoPeakedDepthsAtSomeMetric`). So no fixed view
with a non-coplanar rim certifies unimodality at every metric. Here points and functionals are
plain coordinate vectors `Fin 3 → ℝ`.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra

open scoped RealInnerProductSpace
open Finset

/-- The cross product in `ℝ³`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The determinant of the three vectors `a`, `b`, `c` (the triple product `(a × b) · c`). -/
noncomputable def det3 (a b c : ℝ³) : ℝ :=
  (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
    (a 0 * b 1 - a 1 * b 0) * c 2

/-- A cyclic sequence of distinct reals with exactly one local maximum (hence
exactly one local minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The labelled cycle `lab 0, lab 1, …` is the strict rim of the view `u`: for every
side `lab i → lab (i+1)`, every other point `x m` lies strictly to the left, i.e. the
determinant of `x (lab (i+1)) - x (lab i)`, `x m - x (lab i)` and the view direction `u`
is positive.  So the projections of the points `x (lab i)` are the corners of a strictly
convex counterclockwise polygon containing the projections of all points. -/
def StrictRim {k : ℕ} [NeZero k] (x : Fin 7 → ℝ³) (u : ℝ³) (lab : ZMod k → Fin 7) : Prop :=
  ∀ (m : Fin 7) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- The point set `x` has a unimodal view: a direction `u` and a cycle of `k ≥ 3` distinct
points forming the strict rim of the silhouette in direction `u`, whose depths `⟪x i, u⟫`
are cyclically unimodal. -/
def HasUnimodalView (x : Fin 7 → ℝ³) : Prop :=
  ∃ (u : ℝ³) (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin 7),
    3 ≤ k ∧ Function.Injective lab ∧ StrictRim x u lab ∧
      IsCyclicUnimodal (fun i => ⟪x (lab i), u⟫)

/-- A local certificate at the point `x`, for the view `w` and the infinitesimal motion
`(ω, τ)` (velocity `ω × y + τ` at `y`): either `x` is a silhouette corner between `y₀`
(before) and `y₁` (after) and its velocity points strictly into the angle `y₀ x y₁`, or `x`
lies strictly inside the (projected) triangle `a b c` of points of `V`. -/
def TiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, 0 < det3 (y₁ - x) (y₀ - x) w ∧
      0 < det3 (y₁ - x) (cross ω x + τ) w ∧ 0 < det3 (x - y₀) (cross ω x + τ) w) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
      0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w)

/-- The finite point set `V` has a first-order passage: at the view `w ≠ 0` the motion
`(ω, τ)` moves every silhouette corner strictly inward, and every other point is strictly
inside a triangle of points of `V`. -/
def HasFirstOrderPassage (V : Finset ℝ³) : Prop :=
  ∃ w ω τ : ℝ³, w ≠ 0 ∧ ∀ y ∈ V, TiltCert V w ω τ y

/-- **Converse of the unimodal criterion fails.**  There are seven points in `ℝ³`, all
exposed vertices of their convex hull, four of them spanning a quadrilateral face (the other
three strictly below its plane), which have a first-order passage but no unimodal view. -/
def ExistsFirstOrderPassageWithoutUnimodalView : Prop :=
  ∃ x : Fin 7 → ℝ³,
    (∀ i, ∃ c : ℝ³, ∀ j, j ≠ i → ⟪c, x j⟫ < ⟪c, x i⟫) ∧
    (∃ (n : ℝ³) (h : ℝ), n ≠ 0 ∧ (∀ i : Fin 7, i.val < 4 → ⟪n, x i⟫ = h) ∧
      (∀ i : Fin 7, 4 ≤ i.val → ⟪n, x i⟫ < h)) ∧
    HasFirstOrderPassage (univ.image x) ∧
    ¬ HasUnimodalView x

section MetricUniform

open Matrix

/-- The depth of the point `x` along the view `v` in the metric `G`: `⟪G v, x⟫`. -/
def depth (G : Matrix (Fin 3) (Fin 3) ℝ) (v x : Fin 3 → ℝ) : ℝ := (G *ᵥ v) ⬝ᵥ x

/-- The triple product `det(a, b, c) = (a × b) · c` of three vectors of `ℝ³`. -/
def tripleProduct (a b c : Fin 3 → ℝ) : ℝ :=
  (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
    (a 0 * b 1 - a 1 * b 0) * c 2

/-- A cyclic sequence `z 0, z 1, z 2, z 3` of four reals is *two-peaked* if the two
opposite entries `z 0, z 2` are both strictly larger than the other two, or the two entries
`z 1, z 3` are both strictly larger than the other two. Then each of the two larger entries is
a strict local maximum of the cyclic sequence, so there are two cyclic peaks. -/
def TwoCyclicPeaks4 (z : ZMod 4 → ℝ) : Prop :=
  max (z 1) (z 3) < min (z 0) (z 2) ∨ max (z 0) (z 2) < min (z 1) (z 3)

/-- The points `x 0, x 1, …, x (k-1)` of `ℝ³` (cyclic order, `k ≥ 3`) form a *strictly convex
planar cycle* with normal `n`: all the points lie in one plane `{y | n ⬝ y = const}`, and for
each side `x i → x (i+1)` every other point `x m` lies strictly to its left as seen from the
direction `n`, i.e. `det(x (i+1) - x i, x m - x i, n) > 0`. Equivalently the points are the
vertices, in counterclockwise order, of a convex polygon in that plane, no three collinear. -/
def IsStrictConvexPlanarCycle {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (n : Fin 3 → ℝ) :
    Prop :=
  (∀ i, n ⬝ᵥ x i = n ⬝ᵥ x 0) ∧
    ∀ i m : ZMod k, m ≠ i → m ≠ i + 1 → 0 < tripleProduct (x (i + 1) - x i) (x m - x i) n

/-- (Theorem F, easy half.) Every linear functional `l` with `l(v) > 0` is the depth functional
`G v` of some positive definite symmetric matrix `G`: `G v = l`, so
`⟪G v, y⟫ = l(y)` for all `y`. -/
def ExistsMetricWithPrescribedDepth : Prop :=
  ∀ v l : Fin 3 → ℝ, 0 < l ⬝ᵥ v →
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ v = l

/-- (Theorem U, four points.) Let `x 0, x 1, x 2, x 3` be four points of `ℝ³` that are not
coplanar (the vectors `x i - x 0` are linearly independent) and let `v ≠ 0` be any view
direction. Then there is a positive definite metric `G` for which the depths
`⟪G v, x i⟫`, read in the cyclic order `x 0, x 1, x 2, x 3`, are two-peaked, hence not
cyclically unimodal (two local maxima rather than one).

So no single view with a non-coplanar rim is unimodal at every metric. This shows two peaks;
it does not show that the view is first-order rigid, which is a stronger property. -/
def TwoPeakedDepthsAtSomeMetric : Prop :=
  ∀ (x : ZMod 4 → Fin 3 → ℝ) (v : Fin 3 → ℝ),
    LinearIndependent ℝ ![x 1 - x 0, x 2 - x 0, x 3 - x 0] → v ≠ 0 →
      ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
        TwoCyclicPeaks4 (fun i => depth G v (x i)) ∧
        ¬ IsCyclicUnimodal (fun i => depth G v (x i))

/-- (Theorem C, depth part.) If the points `x i` form a strictly convex planar cycle (the rim
of a view whose corners are coplanar) and `l` is any linear functional that takes distinct
values on them, then `l (x i)` is cyclically unimodal. In particular this holds for the depth
functional `l = G v` at every metric `G` and every view `v` for which the depths are distinct:
depth on a coplanar rim is unimodal at every metric. -/
def CoplanarRimDepthUnimodal : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ (x : ZMod k → Fin 3 → ℝ) (n : Fin 3 → ℝ),
    IsStrictConvexPlanarCycle x n → ∀ l : Fin 3 → ℝ,
      Function.Injective (fun i => l ⬝ᵥ x i) → IsCyclicUnimodal (fun i => l ⬝ᵥ x i)

/-- (Sanity, contrast with Theorem U.) For four points forming a strictly convex planar cycle,
the depths are two-peaked at no linear functional, hence at no metric `G` and view `v`
(take `l = G v`): the conclusion of `TwoPeakedDepthsAtSomeMetric` fails for every metric. -/
def CoplanarConvexQuadrilateralNeverTwoPeaked : Prop :=
  ∀ (x : ZMod 4 → Fin 3 → ℝ) (n : Fin 3 → ℝ),
    IsStrictConvexPlanarCycle x n → ∀ l : Fin 3 → ℝ, ¬ TwoCyclicPeaks4 (fun i => l ⬝ᵥ x i)

end MetricUniform

end MinimalityExtra
