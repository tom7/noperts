module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.CrossProduct
public import MainTheorem
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

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

## Rim shape and first-order freedom are independent at a single view

`ExistsTetrahedronViewsIndependent`: one tetrahedron has a view with a unimodal rim that is
rigid, a view with a two-peaked rim that is free, and a view with a two-peaked rim that is rigid.
So a unimodal rim alone does not make a view free: that also needs no horizontal double normal.
`ExistsMetricChangingFreedom`: the same tetrahedron and affine view, with the same silhouette and
the same depth order, can be free in one metric and rigid in another, so freedom at a two-peaked
rim is not combinatorial.

## The chirotope does not determine the silhouette

`ChirotopeDoesNotDetermineSilhouette`: two generic 5-point configurations with the same signs of
all 4-point determinants can have different shadows along the direction of a pair of points. That
direction depends on 5-point determinants such as `det(b - a, d - c, e - c)`, so a certificate
at a pair view cannot be uniform over a chirotope class.

## Arrangement vertices suffice

`ArrangementVerticesSuffice`: if finitely many linear forms on `ℝ³`, two of them independent,
are all positive somewhere, then some vertex of their great-circle arrangement, with a tilt,
already has that sign pattern lexicographically. So a search for a cell defined by the signs of
linear forms in the view need only try arrangement vertices.
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

section TetrahedronViews

/-- `StrictRim` of `MinimalityExtra.lean`, with the same definition, for a point family indexed
by an arbitrary `Fin n` (the original is for `Fin 7`). -/
def StrictRimN {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ (m : Fin n) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- A cyclic sequence of distinct reals with exactly two local maxima (hence exactly two
local minima). For `k = 4` this means: both entries of one diagonal are strictly above both
entries of the other. -/
def IsCyclicTwoPeaked {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 2

/-- The view `w` of the finite point set `V` is *free*: there is a first-order motion
`(ω, τ)` with a `TiltCert` certificate at every point of `V` (every silhouette corner moves
strictly inward, every other point is strictly inside a projected triangle of points of `V`).
This is `HasFirstOrderPassage` at a fixed view. A view is *rigid* if it is not free. -/
def FreeAt (V : Finset ℝ³) (w : ℝ³) : Prop :=
  ∃ ω τ : ℝ³, ∀ y ∈ V, TiltCert V w ω τ y

/-- **Rim shape and first-order freedom are independent at a single view.**  There are four
points `x` of `ℝ³`, not coplanar, and three views `wa wb wc` such that, with `V` the set of
the four points:
(a) at `wa` the four points form a strict rim (a 4-cycle) whose depths `⟪x i, wa⟫` are
cyclically unimodal (distinct, one local maximum), and the view is rigid;
(b) at `wb` the strict rim has cyclically two-peaked depths and the view is free;
(c) at `wc` the strict rim has cyclically two-peaked depths and the view is rigid. -/
def ExistsTetrahedronViewsIndependent : Prop :=
  ∃ x : Fin 4 → ℝ³, det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) ≠ 0 ∧
    ∃ wa wb wc : ℝ³,
      (∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN x wa lab ∧
          IsCyclicUnimodal (fun i => ⟪x (lab i), wa⟫)) ∧
        ¬ FreeAt (univ.image x) wa ∧
      (∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN x wb lab ∧
          IsCyclicTwoPeaked (fun i => ⟪x (lab i), wb⟫)) ∧
        FreeAt (univ.image x) wb ∧
      (∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN x wc lab ∧
          IsCyclicTwoPeaked (fun i => ⟪x (lab i), wc⟫)) ∧
        ¬ FreeAt (univ.image x) wc

/-- **First-order freedom depends on the metric; the combinatorics does not.**
Same polytope, same affine view, same silhouette, same depth order, two metrics: free in one,
rigid in the other. Precisely: there are four non-coplanar points `x`, a view direction `v`, a
cyclic labelling `lab` and an invertible matrix `A` (with positive determinant; `A` encodes the
metric `G = AᵀA`, so that `y i = A (x i)` is the same shape seen in the metric `G`, with view
`w = A v`) such that `lab` is a strict rim of `x` at `v` and of `y` at `w`; the depths
`⟪x (lab i), v⟫` and `⟪y (lab i), w⟫` are both cyclically two-peaked and induce the same order
(`depth i < depth j` for `x` exactly when it holds for `y`); and the view `v` of `x` is free
while the view `w` of `y` is rigid. -/
def ExistsMetricChangingFreedom : Prop :=
  ∃ (x : Fin 4 → ℝ³) (v : ℝ³) (lab : ZMod 4 → Fin 4) (A : Matrix (Fin 3) (Fin 3) ℝ),
    det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) ≠ 0 ∧ 0 < A.det ∧
    Function.Injective lab ∧
    StrictRimN x v lab ∧
    StrictRimN (fun i => Matrix.toEuclideanLin A (x i)) (Matrix.toEuclideanLin A v) lab ∧
    IsCyclicTwoPeaked (fun i => ⟪x (lab i), v⟫) ∧
    IsCyclicTwoPeaked
      (fun i => ⟪Matrix.toEuclideanLin A (x (lab i)), Matrix.toEuclideanLin A v⟫) ∧
    (∀ i j : ZMod 4, ⟪x (lab i), v⟫ < ⟪x (lab j), v⟫ ↔
      ⟪Matrix.toEuclideanLin A (x (lab i)), Matrix.toEuclideanLin A v⟫ <
        ⟪Matrix.toEuclideanLin A (x (lab j)), Matrix.toEuclideanLin A v⟫) ∧
    FreeAt (univ.image x) v ∧
    ¬ FreeAt (univ.image (fun i => Matrix.toEuclideanLin A (x i))) (Matrix.toEuclideanLin A v)

end TetrahedronViews

section Chirotope

open Matrix

/-- Two 5-point configurations have the same chirotope (the signs of the 4-point
determinants `det(x j - x i, x k - x i, x l - x i)`): for all indices `i j k l`, the sign of
this determinant for `x` equals its sign for `y`. -/
def SameChirotope (x y : Fin 5 → Fin 3 → ℝ) : Prop :=
  ∀ i j k l : Fin 5,
    SignType.sign (tripleProduct (x j - x i) (x k - x i) (x l - x i)) =
      SignType.sign (tripleProduct (y j - y i) (y k - y i) (y l - y i))

/-- A 5-point configuration is generic in the chirotope sense: every 4-point determinant with
four distinct indices is nonzero. -/
def ChirotopeGeneric (x : Fin 5 → Fin 3 → ℝ) : Prop :=
  ∀ i j k l : Fin 5, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    tripleProduct (x j - x i) (x k - x i) (x l - x i) ≠ 0

/-- The directed side `(a, b)` of the shadow of `p` along the view `u`: every other point
`p m` (with `m` not `a`, `b`, and not the vertex `4`, which projects onto vertex `3`) lies
strictly to the left of the directed line from `p a` to `p b` in the projection. -/
def IsShadowSide (p : Fin 5 → Fin 3 → ℝ) (u : Fin 3 → ℝ) (a b : Fin 5) : Prop :=
  ∀ m : Fin 5, m ≠ a → m ≠ b → m ≠ 4 → 0 < tripleProduct (p b - p a) (p m - p a) u

/-- The chirotope does not determine the silhouette. There are two generic 5-point
configurations with the same chirotope, such that for some directed side `(a, b)` with
`a, b` in `{0, 1, 2, 3}`, the pair is a shadow side along `x 4 - x 3` but not along
`y 4 - y 3`. -/
def ChirotopeDoesNotDetermineSilhouette : Prop :=
  ∃ x y : Fin 5 → Fin 3 → ℝ, ChirotopeGeneric x ∧ ChirotopeGeneric y ∧ SameChirotope x y ∧
    ∃ a b : Fin 5, a ≠ 4 ∧ b ≠ 4 ∧ a ≠ b ∧
      IsShadowSide x (x 4 - x 3) a b ∧ ¬ IsShadowSide y (y 4 - y 3) a b

end Chirotope

section ArrangementVertices

open Matrix

/-- ARRANGEMENT VERTICES SUFFICE. Let `l 0, …, l (n-1)` be linear forms on `ℝ³` (vectors;
the value at the view `u` is `l k ⬝ᵥ u`; signs of conditions are absorbed into the forms, so the
open chamber is `{u | ∀ k, 0 < l k ⬝ᵥ u}`). Assume at least two of the forms are linearly
independent (this is implied by the forms spanning `ℝ³`, and is the sharp requirement; see
`ChamberNeedsRank`) and the chamber is nonempty. Then there are a nonzero view `u₀`, two
indices `i j` with independent forms vanishing at `u₀` (so `u₀` is a multiple of the cross
product `l i × l j`, an arrangement vertex) and a tilt `d` such that for every form `k` either
`l k ⬝ᵥ u₀ > 0`, or `l k ⬝ᵥ u₀ = 0` and `l k ⬝ᵥ d > 0` (lexicographic cell: `u₀ + ε d` lies in
the chamber for small `ε > 0`). -/
def ArrangementVerticesSuffice : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    (∃ i j, LinearIndependent ℝ ![l i, l j]) →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)

/-- The same with the hypothesis in the form used by the notes: the forms span the dual of
`ℝ³`, `Submodule.span ℝ (Set.range l) = ⊤` (rank 3). Weaker than `ArrangementVerticesSuffice`'s
hypothesis, so this is a consequence. -/
def ArrangementVerticesSufficeSpan : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    Submodule.span ℝ (Set.range l) = ⊤ →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)

/-- Explicit lexicographic form of `ArrangementVerticesSuffice`: moreover `u₀ + ε • d` lies in
the open chamber for every small `ε > 0`. -/
def ArrangementVerticesSufficeLex : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    (∃ i j, LinearIndependent ℝ ![l i, l j]) →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ k, 0 < l k ⬝ᵥ (u₀ + ε • d))

/-- THE INDEPENDENT-PAIR HYPOTHESIS IS NEEDED (and it is the sharp one). There is a family of
forms (a single form, so rank 1: all forms parallel) whose open chamber is nonempty, with no two
independent forms, and for which no vertex-with-tilt as in `ArrangementVerticesSuffice` exists.
For families of rank 2 (two independent forms, all forms in their span) the theorem holds: the
vertex is the common kernel line of all the forms, which lies in the closed cone. -/
def ChamberNeedsRank : Prop :=
  ∃ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) ∧
    (¬ ∃ i j, LinearIndependent ℝ ![l i, l j]) ∧
    ¬ ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)

end ArrangementVertices

section Box

/-- Auxiliary: the sign (`1` or `-1`) of coordinate `j` of corner `i`: `1` iff bit `j` of `i` is set. -/
noncomputable def boxSign (j : ℕ) (i : Fin 8) : ℝ := if i.val / 2 ^ j % 2 = 1 then 1 else -1

/-- The eight corners of the box with half-sides `a b c`; bit j of the index gives the sign of coordinate j. -/
noncomputable def boxPts (a b c : ℝ) : Fin 8 → ℝ³ :=
  fun i => !₂[boxSign 0 i * a, boxSign 1 i * b, boxSign 2 i * c]

/-- **Rectangular boxes have no unimodal view.** -/
def BoxesHaveNoUnimodalView : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → ∀ (u : ℝ³) (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin 8),
    3 ≤ k → Function.Injective lab → StrictRimN (boxPts a b c) u lab →
      ¬ IsCyclicUnimodal (fun i => ⟪boxPts a b c (lab i), u⟫)

end Box

/-!
## Depth-separated views are free (Theorem 8.10)

A generic view is free, with any number of peaks and no torque condition, when a rim edge and a
corner on parallel support lines split the rim by depth: the level of the corner crosses the rim
only at that corner and on that edge. On a unimodal rim every level does this. The repository's
`Minimality.exists_tiltCert_of_depthSeparated` proves the same in a frame, by Gordan's lemma; the
proof in `MinimalityExtra/DepthSeparated.lean` is frame-free with an explicit motion.
-/

section DepthSeparated

/-- The point of the line through the edge `a` at the depth of the corner `c`. -/
noncomputable def levelPoint {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : ℝ³ :=
  X a + (⟪X c - X a, w⟫ / ⟪X (a + 1) - X a, w⟫) • (X (a + 1) - X a)

/-- The hidden points of `x` (off the rim `lab`) lie strictly inside a projected triangle of
points.  Only a hidden point on every such triangle's boundary fails this, a special position. -/
def HiddenInTriangles {n k : ℕ} (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ m, (∀ i, m ≠ lab i) → ∃ p ∈ Finset.univ.image x, ∃ q ∈ Finset.univ.image x, ∃ r ∈ Finset.univ.image x,
    0 < det3 (q - p) (r - p) w ∧ 0 < det3 (q - p) (x m - p) w ∧
    0 < det3 (r - q) (x m - q) w ∧ 0 < det3 (p - r) (x m - r) w

/-- A *split antipodal level pair* (edge `a`, corner `c`) of the cycle `X` at the view `w`: `c`
is the strict minimum of the height `det3 d w ·` across the edge `a` (`d = X (a+1) - X a`), so the
support lines at the edge and at `c` are parallel, the corners on the arc from `c` to `a` lie on
one side of the level of `c`, and those on the arc from `a + 1` back to `c` on the other.  This is
`Minimality.IsDepthSeparatedPair`, frame-free and with a strict antipode. -/
def IsDepthSeparatedAt {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : Prop :=
  (∀ i, i ≠ c → det3 (X (a + 1) - X a) w (X c) < det3 (X (a + 1) - X a) w (X i)) ∧
    (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X c, w⟫ < ⟪X (c + s), w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∨
      ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + s), w⟫))

/-- **Depth-separated views are free.**  A view with a strict rim and a split antipodal level pair without a
horizontal double normal at it is free, whatever the number of peaks. -/
def DepthSeparatedViewIsFree : Prop :=
  ∀ (n k : ℕ) [NeZero k] (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) (a c : ZMod k),
    3 ≤ k → Function.Injective lab → StrictRimN x w lab → HiddenInTriangles x w lab →
    IsDepthSeparatedAt (fun i => x (lab i)) w a c →
    ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c), x (lab (a + 1)) - x (lab a)⟫ ≠ 0 →
    FreeAt (Finset.univ.image x) w

/-- The spin part of a row of the Edge-Plane Lemma: the value at the end `X j` of the edge `i` of
the rotation about the vertical through `X a`, corrected along `N` so that the edge `a` keeps its
line. -/
noncomputable def edgePlaneSpin {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k) : ℝ :=
  det3 (X (i + 1) - X i) (cross w (X j - X a)) w +
    (⟪X j - X a, w⟫ / ⟪X (a + 1) - X a, w⟫) *
      det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) w) w

/-- **Edge-Plane Lemma.** At a view with a strict rim, if some `(α, μ, s)` makes every row off the
edge `a` positive, the view is free. The rows ask the line `ρ = α + μ z` to separate two point
sets in a plane; the motion turns about an axis in the plane through the edge `a` normal to its
support plane. -/
def EdgePlaneFreedom : Prop :=
  ∀ (n k : ℕ) [NeZero k], 3 ≤ k → ∀ (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n),
    Function.Injective lab → StrictRimN x w lab → HiddenInTriangles x w lab →
    ∀ (a : ZMod k) (s α μ : ℝ), ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 →
    (∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) →
    FreeAt (Finset.univ.image x) w

end DepthSeparated

/-!
## Metric identities and a sequence lemma

`HdnEquation` writes the HDN condition at every metric through the adjugate. `SingleViewFarkas`
says when a depth pattern cannot occur at a view at any metric. `CircleReduction` and
`CircleReductionExists` say that on the circle `n^⊥` a metric acts only through its restriction to
`n^⊥` and a free shadow vector. `MergeLemma` is about cyclic
sequences: a transversal crossing of adjacent entries whose merged cycle is unimodal leaves the
cycle unimodal on one side of the crossing.
-/

section Identities

open Matrix in
/-- (Lemma 27.35, the HDN equation.)  Let `G` be a metric (positive definite matrix), `u` a
view, `[a, b]` a side with `z a ≠ z b` where `z x = ⟪u, x⟫_G = u ⬝ᵥ G *ᵥ x`, and `c` a further
point; `e = b - a`, `w = c - a`.  If `y = a + λ e` is the point of the line `ab` at depth
`z c` (that is `λ ⟪u, e⟫_G = ⟪u, w⟫_G`), then
`⟪u, e⟫_G ⟪y - c, e⟫_G = ⟪u, w⟫_G ⟪e, e⟫_G - ⟪u, e⟫_G ⟪w, e⟫_G = (u × e)ᵀ adj(G) (w × e)`. -/
def HdnEquation : Prop :=
  ∀ (G : Matrix (Fin 3) (Fin 3) ℝ), G.PosDef → ∀ (a b c u : Fin 3 → ℝ) (lam : ℝ),
    u ⬝ᵥ G *ᵥ a ≠ u ⬝ᵥ G *ᵥ b →
    lam * (u ⬝ᵥ G *ᵥ (b - a)) = u ⬝ᵥ G *ᵥ (c - a) →
      (u ⬝ᵥ G *ᵥ (b - a)) * ((a + lam • (b - a) - c) ⬝ᵥ G *ᵥ (b - a)) =
          (u ⬝ᵥ G *ᵥ (c - a)) * ((b - a) ⬝ᵥ G *ᵥ (b - a)) -
            (u ⬝ᵥ G *ᵥ (b - a)) * ((c - a) ⬝ᵥ G *ᵥ (b - a)) ∧
      (u ⬝ᵥ G *ᵥ (c - a)) * ((b - a) ⬝ᵥ G *ᵥ (b - a)) -
            (u ⬝ᵥ G *ᵥ (b - a)) * ((c - a) ⬝ᵥ G *ᵥ (b - a)) =
          crossProduct u (b - a) ⬝ᵥ G.adjugate *ᵥ crossProduct (c - a) (b - a)

open Matrix in
/-- (Lemma 25.60, single-view Farkas.)  Points `P : ι → ℝ³`, a pattern `p` (a finite set of
pairs `(h, l)`, each asserting `z h ≥ z l`), and a view `r ≠ 0`.  The
pattern is *realizable* at `r` if some metric `G` (positive definite) has depth
`z x = x ⬝ᵥ G *ᵥ r` with `z h ≥ z l` for all `(h, l) ∈ p`.  If `-r` lies in the convex cone
spanned by the differences `P h - P l`, `(h, l) ∈ p`, the pattern is not realizable at `r`. -/
def SingleViewFarkas : Prop :=
  ∀ {ι : Type} (P : ι → Fin 3 → ℝ) (p : Finset (ι × ι)) (r : Fin 3 → ℝ), r ≠ 0 →
    (∃ c : ι × ι → ℝ, (∀ q ∈ p, 0 ≤ c q) ∧
        -r = ∑ q ∈ p, c q • (P q.1 - P q.2)) →
      ¬ ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
          ∀ q ∈ p, P q.2 ⬝ᵥ G *ᵥ r ≤ P q.1 ⬝ᵥ G *ᵥ r

open Matrix in
/-- (Lemma 25.59, circle reduction, identity part.)  Let `n ≠ 0`, `Π = n^⊥`, `G ≻ 0`, and let
`d` satisfy `G d = n` and `n·d = 1` (so `d = G⁻¹n` up to the normalisation).  Let `m` satisfy
`n·m = 1`.  For `v` with `Pv = v - (n·v) m` (so `Pv ∈ Π`) and `g = d - m` (so `g ∈ Π`), every
`r ∈ Π` satisfies `⟨r, G v⟩ = ⟨r, G Pv⟩ - (n·v) ⟨r, G g⟩`. -/
def CircleReduction : Prop :=
  ∀ (G : Matrix (Fin 3) (Fin 3) ℝ) (n d m v r : Fin 3 → ℝ), G.PosDef → n ≠ 0 →
    G *ᵥ d = n → n ⬝ᵥ d = 1 → n ⬝ᵥ m = 1 → n ⬝ᵥ r = 0 →
      r ⬝ᵥ G *ᵥ v = r ⬝ᵥ G *ᵥ (v - (n ⬝ᵥ v) • m) - (n ⬝ᵥ v) * (r ⬝ᵥ G *ᵥ (d - m))

open Matrix in
/-- (Lemma 25.59, circle reduction, existence part.)  Given a symmetric `Y` that is positive on
`n^⊥ \ {0}`, and `m`, `g` with `n·m = 1`, `n·g = 0`, there is a positive definite `G` with
`G (m + g) = n` and `⟨r, G s⟩ = ⟨r, Y s⟩` for all `r, s ∈ n^⊥`. -/
def CircleReductionExists : Prop :=
  ∀ (Y : Matrix (Fin 3) (Fin 3) ℝ) (n m g : Fin 3 → ℝ),
    Y.IsSymm → n ⬝ᵥ m = 1 → n ⬝ᵥ g = 0 →
    (∀ r, n ⬝ᵥ r = 0 → r ≠ 0 → 0 < r ⬝ᵥ Y *ᵥ r) →
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ (m + g) = n ∧
      ∀ r s, n ⬝ᵥ r = 0 → n ⬝ᵥ s = 0 → r ⬝ᵥ G *ᵥ s = r ⬝ᵥ Y *ᵥ s

/-- (Lemma 26.4, merge lemma.)  A cycle of `n + 2` affine functions `f j (λ) = α j + β j * λ`
(the depths of the rim corners along a circle of views); the corners `0` and `1` are adjacent.
At `λ₀` the depths of `0` and `1` cross transversally (`β 0 ≠ β 1` and equal value), and the
cycle in which `0` and `1` are merged into one entry (`ZMod (n+1)`, the entry `j` of the
original cycle going to `max (j.val - 1) 0`) has distinct values and a single local maximum
(`IsCyclicUnimodal`).  Then the original cycle is unimodal for all `λ` in an open interval
on one side of `λ₀` adjacent to `λ₀`.  The (cyclic) position of the adjacent pair is
normalised to `0, 1`, and the original cycle has at least `2` entries (for `n = 0` the
hypothesis is void). -/
def MergeLemma : Prop :=
  ∀ (n : ℕ) (α β : ZMod (n + 2) → ℝ) (lam0 : ℝ) (m : ZMod (n + 1) → ℝ),
    β 0 ≠ β 1 → (∀ j, α j + β j * lam0 = m ((j.val - 1 : ℕ) : ZMod (n + 1))) →
    IsCyclicUnimodal m →
    ∃ ε > 0,
      (∀ lam, lam0 < lam → lam < lam0 + ε → IsCyclicUnimodal (fun j => α j + β j * lam)) ∨
      (∀ lam, lam0 - ε < lam → lam < lam0 → IsCyclicUnimodal (fun j => α j + β j * lam))

end Identities

/-!
## Stability of the Rupert property

Rupert is stable under small changes of the hull, with an explicit rate in terms of the clearance
of a passage. Since every set of at most 6 non-collinear points is Rupert, compactness shows
that any finite set close enough to one (and not nearly collinear) is Rupert, for any number of
points. In particular a 7-vertex Nopert in the unit ball with a triple of points of cross
product norm at least `r` has all vertex distances at least `ε(r)`; the constant is not explicit.
-/

section Stable

/-- `W` has a passage with clearance `δ`: a closed `δ`-ball about each point of the inner shadow lies
in the outer shadow. -/
def HasClearance (W : Finset ℝ³) (δ : ℝ) : Prop :=
  ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ p ∈ convexHull ℝ (W : Set ℝ³),
    Metric.closedBall (inner_offset + proj_xy (inner_rotation.toEuclideanLin p)) δ ⊆
      { proj_xy (outer_rotation.toEuclideanLin q) | q ∈ convexHull ℝ (W : Set ℝ³) }

/-- **Clearance is stable.** A passage of `W` with clearance `δ` gives a passage of `V` when every
point of `V` is within `ε₁` of the hull of `W`, every point of `W` within `ε₂` of the hull of `V`, and
`ε₁ + ε₂ < δ`. -/
def ClearanceStable : Prop :=
  ∀ (V W : Finset ℝ³) (δ ε₁ ε₂ : ℝ), HasClearance W δ →
    (∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ ε₁) →
    (∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ ε₂) →
    ε₁ + ε₂ < δ → IsRupert V

/-- **A Rupert passage has positive clearance.** -/
def RupertHasClearance : Prop :=
  ∀ W : Finset ℝ³, IsRupert W → ∃ δ > 0, HasClearance W δ

/-- Rupert is stable under small Hausdorff perturbations near a point set of at most six points
that is not collinear: for every `r > 0` there is `ε > 0` such that every `V` (of any size) whose
points are within `ε` of the hull of such a `W` (in the closed unit ball, with a triple of cross
norm at least `r`), and conversely, is Rupert. -/
def RupertNearFewPoints : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ε : ℝ, 0 < ε ∧ ∀ V W : Finset ℝ³, W.card ≤ 6 → (∀ w ∈ W, ‖w‖ ≤ 1) →
    (∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, r ≤ ‖cross (b - a) (c - a)‖) →
    (∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ ε) →
    (∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ ε) → IsRupert V

/-- **Close vertices make a 7-vertex polytope Rupert** (nonconstructive).  For every `r > 0` there
is `ε > 0` such that every set `V` of at most 7 points in the closed unit ball containing a triple
`a, b, c` with `r ≤ ‖(b - a) × (c - a)‖` and two distinct points at distance less than `ε` is
Rupert.

For Noperts this says: a 7-vertex Nopert in the unit ball with a triple of cross norm at least `r`
has all pairwise vertex distances at least `ε(r)`.  (The bound `ε(r)` is not made explicit, since
it comes from a compactness argument.) -/
def CloseVerticesRupert : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ε : ℝ, 0 < ε ∧ ∀ V : Finset ℝ³, V.card ≤ 7 → (∀ v ∈ V, ‖v‖ ≤ 1) →
    (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, r ≤ ‖cross (b - a) (c - a)‖) →
    (∃ x ∈ V, ∃ y ∈ V, x ≠ y ∧ dist x y < ε) → IsRupert V

/-- `PassesThrough L W`: some rotations and an offset put the shadow of `conv L` inside the
interior of the outer shadow of `conv W`. This is `IsRupert` with two point sets. -/
def PassesThrough (L W : Finset ℝ³) : Prop :=
  ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  let inner_shadow :=
    { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (L : Set ℝ³) }
  let outer_shadow :=
    { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (W : Set ℝ³) }
  inner_shadow ⊆ interior outer_shadow

/-- **Sandwich.** If `conv W ⊆ conv K ⊆ conv L` and `L` passes through `W`, then `K` is Rupert.
The same rotations and offset work for `K`: its inner shadow is inside that of `L`, and its outer
shadow contains that of `W`. -/
def RupertSandwich : Prop :=
  ∀ W K L : Finset ℝ³,
    convexHull ℝ (W : Set ℝ³) ⊆ convexHull ℝ (K : Set ℝ³) →
    convexHull ℝ (K : Set ℝ³) ⊆ convexHull ℝ (L : Set ℝ³) →
    PassesThrough L W → IsRupert K

/-- **Cylinder extension.** Let `K₀` pass through itself with rotations `Ri`, `Ro` and offset `o`
(inner shadow inside the interior of the outer shadow). Then every `y` whose inner-view image
`o + proj_xy (Ri y)` lies in the interior of the outer shadow gives a Rupert set `insert y K₀`. -/
def CylinderExtension : Prop :=
  ∀ (K₀ : Finset ℝ³) (Ri Ro : Matrix (Fin 3) (Fin 3) ℝ),
    Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ →
    Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ →
    ∀ o : EuclideanSpace ℝ (Fin 2),
    { o + proj_xy (Ri.toEuclideanLin p) | p ∈ convexHull ℝ (K₀ : Set ℝ³) } ⊆
      interior { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K₀ : Set ℝ³) } →
    ∀ y : ℝ³,
      o + proj_xy (Ri.toEuclideanLin y) ∈
        interior { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K₀ : Set ℝ³) } →
      IsRupert (insert y K₀)

end Stable

/-!
## Pairs of tests at every metric

`AngleLemma` and the invisibility statements say when two tests cannot both fail at one metric.
`TwoInteriorCornersNeverMetricFree` is the negative side: a rim with four consecutive non-coplanar
corners is not unimodal at some metric. Only one closing is treated here, not both at once.
-/

section TestPairs

open Matrix

/-- (Lemma 13.2, the angle lemma, rims of any size.)  Two crossing tests: rims
`x₁ : ZMod k₁ → ℝ³`, `x₂ : ZMod k₂ → ℝ³` (cyclic) with nonzero views `u₁, u₂`.  At a metric `G`
(positive definite) the depth of a point `y` along `u` is `(G u) ⬝ᵥ y`.  A *pattern* of a rim
is the set of pairs `(h, l)` with `z l < z h` of an injective depth sequence `z` that is not
cyclically unimodal (more than or fewer than one strict local maximum); it is *admissible* if
it occurs.  Its cone is the cone spanned by the differences `x h - x l`.  Suppose that for
every admissible pattern `s₁` of the first rim and `s₂` of the second there is a sign `ε = ±1`
with `ε u₂ ∈ cone(s₁)` and `-ε u₁ ∈ cone(s₂)`.  Then at every metric at which both rims have
injective depths, the depths of the first rim or those of the second are cyclically unimodal
(injective with exactly one strict local maximum). -/
def AngleLemma : Prop :=
  ∀ {k₁ k₂ : ℕ} [NeZero k₁] [NeZero k₂] (x₁ : ZMod k₁ → Fin 3 → ℝ) (x₂ : ZMod k₂ → Fin 3 → ℝ)
    (u₁ u₂ : Fin 3 → ℝ), u₁ ≠ 0 → u₂ ≠ 0 →
    (∀ (z₁ : ZMod k₁ → ℝ) (z₂ : ZMod k₂ → ℝ),
      Function.Injective z₁ → ¬ (Function.Injective z₁ ∧
        (Finset.univ.filter (fun i : ZMod k₁ => z₁ (i - 1) < z₁ i ∧ z₁ (i + 1) < z₁ i)).card = 1) →
      Function.Injective z₂ → ¬ (Function.Injective z₂ ∧
        (Finset.univ.filter (fun i : ZMod k₂ => z₂ (i - 1) < z₂ i ∧ z₂ (i + 1) < z₂ i)).card = 1) →
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        (∃ c : ZMod k₁ × ZMod k₁ → ℝ, (∀ q, 0 ≤ c q) ∧
          ε • u₂ = ∑ q ∈ Finset.univ.filter (fun q : ZMod k₁ × ZMod k₁ => z₁ q.2 < z₁ q.1),
            c q • (x₁ q.1 - x₁ q.2)) ∧
        (∃ c : ZMod k₂ × ZMod k₂ → ℝ, (∀ q, 0 ≤ c q) ∧
          -ε • u₁ = ∑ q ∈ Finset.univ.filter (fun q : ZMod k₂ × ZMod k₂ => z₂ q.2 < z₂ q.1),
            c q • (x₂ q.1 - x₂ q.2))) →
    ∀ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef →
      Function.Injective (fun i => (G *ᵥ u₁) ⬝ᵥ x₁ i) →
      Function.Injective (fun i => (G *ᵥ u₂) ⬝ᵥ x₂ i) →
      (Function.Injective (fun i => (G *ᵥ u₁) ⬝ᵥ x₁ i) ∧
        (Finset.univ.filter (fun i : ZMod k₁ =>
          (G *ᵥ u₁) ⬝ᵥ x₁ (i - 1) < (G *ᵥ u₁) ⬝ᵥ x₁ i ∧
          (G *ᵥ u₁) ⬝ᵥ x₁ (i + 1) < (G *ᵥ u₁) ⬝ᵥ x₁ i)).card = 1) ∨
      (Function.Injective (fun i => (G *ᵥ u₂) ⬝ᵥ x₂ i) ∧
        (Finset.univ.filter (fun i : ZMod k₂ =>
          (G *ᵥ u₂) ⬝ᵥ x₂ (i - 1) < (G *ᵥ u₂) ⬝ᵥ x₂ i ∧
          (G *ᵥ u₂) ⬝ᵥ x₂ (i + 1) < (G *ᵥ u₂) ⬝ᵥ x₂ i)).card = 1)

/-- The depth functionals at which a test with view `u` fails with the pattern `W` (the set of
difference vectors `W_T(s)` that the pattern forces to be positive in depth):
`Φ(W, u) = {φ | φ u > 0 ∧ φ w > 0 for all w ∈ W}`.  (A functional is `φ ⬝ᵥ ·`.) -/
def FailCone (W : Set (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {φ | 0 < φ ⬝ᵥ u ∧ ∀ w ∈ W, 0 < φ ⬝ᵥ w}

/-- (Lemma V (a), visibility.)  If the pattern `W` is *invisible* along `v` (no functional of
`Φ(W, u)` vanishes on `v`), then `φ v` has one and the same sign on all of `Φ(W, u)`.
(The Farkas reformulation `τ v ∈ cone(W ∪ {u})` is not included.) -/
def InvisibilitySign : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v : Fin 3 → ℝ), (∀ φ ∈ FailCone W u, φ ⬝ᵥ v ≠ 0) →
    ∀ φ₁ ∈ FailCone W u, ∀ φ₂ ∈ FailCone W u, 0 < (φ₁ ⬝ᵥ v) * (φ₂ ⬝ᵥ v)

/-- (Lemma V (b).)  Let `𝒲₁`, `𝒲₂` be the sets of admissible patterns of two tests with views
`u₁, u₂`.  Suppose every pattern of the first is invisible along `u₂`, every pattern of the
second is invisible along `u₁`, and the signs of `φ u₂` on `Φ(W₁, u₁)` and of `φ u₁` on
`Φ(W₂, u₂)` always differ.  Then at no metric `G` (positive definite) do both tests fail, i.e.
`G u₁ ∈ Φ(W₁, u₁)` and `G u₂ ∈ Φ(W₂, u₂)` for no `W₁ ∈ 𝒲₁`, `W₂ ∈ 𝒲₂`. -/
def InvisibilitySignPair : Prop :=
  ∀ (𝒲₁ 𝒲₂ : Set (Set (Fin 3 → ℝ))) (u₁ u₂ : Fin 3 → ℝ),
    (∀ W ∈ 𝒲₁, ∀ φ ∈ FailCone W u₁, φ ⬝ᵥ u₂ ≠ 0) →
    (∀ W ∈ 𝒲₂, ∀ φ ∈ FailCone W u₂, φ ⬝ᵥ u₁ ≠ 0) →
    (∀ W₁ ∈ 𝒲₁, ∀ φ₁ ∈ FailCone W₁ u₁, ∀ W₂ ∈ 𝒲₂, ∀ φ₂ ∈ FailCone W₂ u₂,
      SignType.sign (φ₁ ⬝ᵥ u₂) ≠ SignType.sign (φ₂ ⬝ᵥ u₁)) →
    ∀ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef →
      ∀ W₁ ∈ 𝒲₁, ∀ W₂ ∈ 𝒲₂, ¬ (G *ᵥ u₁ ∈ FailCone W₁ u₁ ∧ G *ᵥ u₂ ∈ FailCone W₂ u₂)

/-- (Corollary V1 (i), a rim edge parallel to `v`.)  If the edge vector `e = c • v`, `c ≠ 0`,
lies in the pattern `W` (an edge `X_{i+1} - X_i`, or the negated edge), then every functional of
`Φ(W, u)` has `c * φ v > 0`: the pattern is invisible along `v` and `φ v` has the sign of `c`. -/
def InvisibilityEdge : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v e : Fin 3 → ℝ) (c : ℝ), e ∈ W → e = c • v →
    ∀ φ ∈ FailCone W u, 0 < c * (φ ⬝ᵥ v)

/-- (Corollary V1 (ii), a middle corner on a flat triple.)  Let `x - ((1-t) y + t z) = κ v`
with `0 ≤ t ≤ 1` (the projection of `x` along `v` lies between those of `y` and `z`).  If `x`
is a strict local maximum of the pattern (`x - y, x - z ∈ W`) then `κ φ v > 0` on `Φ(W, u)`;
if a strict local minimum (`y - x, z - x ∈ W`) then `κ φ v < 0`. -/
def InvisibilityFlat : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v x y z : Fin 3 → ℝ) (t κ : ℝ), 0 ≤ t → t ≤ 1 →
    x - ((1 - t) • y + t • z) = κ • v →
    ((x - y ∈ W ∧ x - z ∈ W → ∀ φ ∈ FailCone W u, 0 < κ * (φ ⬝ᵥ v)) ∧
     (y - x ∈ W ∧ z - x ∈ W → ∀ φ ∈ FailCone W u, κ * (φ ⬝ᵥ v) < 0))

/-- (Lemma E′, two or more interior far corners: never metric-free.)  Let `p 0, …, p (k-1)`,
`k ≥ 4`, be pairwise distinct points of `ℝ³`, the cyclic sequence of the apex and the far
corners of a closing, and `u` a view.  Suppose four consecutive points `p i, …, p (i+3)` are
not coplanar and `det(p (i+2) - p i, p (i+3) - p (i+1), u) ≠ 0` (the projections of
`p (i+2) - p i` and `p (i+3) - p (i+1)` along `u` are the crossing diagonals of a convex
quadrilateral, hence independent).  Then some positive definite metric `G` gives injective
depths `⟪G u, p j⟫` with at least two strict cyclic local maxima: the closing is not
unimodal there. -/
def TwoInteriorCornersNeverMetricFree : Prop :=
  ∀ {k : ℕ} [NeZero k], 4 ≤ k → ∀ (p : ZMod k → Fin 3 → ℝ) (u : Fin 3 → ℝ) (i : ZMod k),
    Function.Injective p →
    tripleProduct (p (i + 1) - p i) (p (i + 2) - p i) (p (i + 3) - p i) ≠ 0 →
    tripleProduct (p (i + 2) - p i) (p (i + 3) - p (i + 1)) u ≠ 0 →
      ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
        Function.Injective (fun j => (G *ᵥ u) ⬝ᵥ p j) ∧
        2 ≤ (Finset.univ.filter (fun j : ZMod k =>
          (G *ᵥ u) ⬝ᵥ p (j - 1) < (G *ᵥ u) ⬝ᵥ p j ∧
          (G *ᵥ u) ⬝ᵥ p (j + 1) < (G *ᵥ u) ⬝ᵥ p j)).card

end TestPairs

/-!
## Core criteria

The unimodal criterion and the coplanar-silhouette theorem, stated with the definitions of this
file. Proofs in `ProofOfMinimalityExtra.lean`, from the repository's theorems.
-/

section Core

/-- **Unimodal view criterion (Theorem 7.3).** -/
def UnimodalViewIsRupert : Prop :=
  ∀ x : Fin 7 → ℝ³, HasUnimodalView x → IsRupert (Finset.univ.image x)

/-- **Coplanar silhouette theorem (Theorem 5).** -/
def CoplanarSilhouetteIsRupert : Prop :=
  ∀ (V W : Finset ℝ³) (u : ℝ³), W ⊆ V → ¬ Collinear ℝ (W : Set ℝ³) →
    Coplanar ℝ (W : Set ℝ³) → u ∉ (affineSpan ℝ (W : Set ℝ³)).direction →
    (∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))) →
    IsRupert V

/-- Triangle shadow special case. -/
def TriangleShadowIsRupert : Prop :=
  ∀ (V : Finset ℝ³) (a b c u : ℝ³), a ∈ V → b ∈ V → c ∈ V →
    AffineIndependent ℝ ![a, b, c] →
    u ∉ (affineSpan ℝ ({a, b, c} : Set ℝ³)).direction →
    (∀ v ∈ V, v ≠ a → v ≠ b → v ≠ c →
      ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ ({a, b, c} : Set ℝ³))) →
    IsRupert V

end Core

section RobustUnimodal

/-- A cyclic sequence is *robustly unimodal*: conditions (R1)–(R3), as `Minimality.IsRobustUnimodal`. Ties are allowed where they cannot create two peaks. -/
def IsRobustUnimodal {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  (∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    ¬ (z (B + b) < z (B + a) ∧ z (B + b) < z (B + c) ∧ z (B + d) < z (B + a) ∧
      z (B + d) < z (B + c))) ∧
  (∀ i j l : ZMod k, i ≠ j → j ≠ l → i ≠ l → z i = z j → z j = z l → False) ∧
  (∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    z (B + b) = z (B + c) →
      ¬ (z (B + a) < z (B + b) ∧ z (B + c) < z (B + d)) ∧
      ¬ (z (B + b) < z (B + a) ∧ z (B + d) < z (B + c)))

/-- Lemma AQ form: no weak alternation (`min (z a, z c) ≥ max (z b, z d)` in cyclic order). -/
def WeakAlternationFree {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    ¬ (z (B + b) ≤ z B ∧ z (B + b) ≤ z (B + c) ∧ z (B + d) ≤ z B ∧ z (B + d) ≤ z (B + c))

/-- **Lemma AQ.** For `k ≥ 4` a cyclic sequence is robustly unimodal iff it has no weak alternation. -/
def RobustUnimodalIffNoAlternation : Prop :=
  ∀ (k : ℕ) [NeZero k], 4 ≤ k → ∀ z : ZMod k → ℝ, IsRobustUnimodal z ↔ WeakAlternationFree z

end RobustUnimodal

/-!
## Metrics, spin, and the farthest vertex

`ThmFBijection` is Theorem F in full. `InwardMotionHasSpin` is Corollary 8.6, here at every view.
`AnchorCore` and `AnchorWidth` are the elementary core of the Anchor Lemma; its consequences for
witness sets are not stated here.
-/

section MetricSpin

open Matrix

/-- The annihilator of `v` among covectors: `{φ | φ ⬝ᵥ v = 0}`, a plane in `ℝ³` when `v ≠ 0`. -/
def annV (v : Fin 3 → ℝ) : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {φ | φ ⬝ᵥ v = 0}
  add_mem' := by intro a b ha hb; simp_all [add_dotProduct]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all [smul_dotProduct]

/-- Symmetric positive definite bilinear forms on the plane `annV v` (the screen metrics `H`). -/
def PD2 (v : Fin 3 → ℝ) : Type :=
  {B : LinearMap.BilinForm ℝ (annV v) // (∀ a b, B a b = B b a) ∧ ∀ a, a ≠ 0 → 0 < B a a}

/-- The bilinear form `(a, b) ↦ a ⬝ᵥ (M *ᵥ b)` on `annV v`. -/
def restrictForm (v : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : LinearMap.BilinForm ℝ (annV v) :=
  LinearMap.mk₂ ℝ (fun a b => (a : Fin 3 → ℝ) ⬝ᵥ (M *ᵥ (b : Fin 3 → ℝ)))
    (by intros; simp [add_dotProduct])
    (by intros; simp [smul_dotProduct])
    (by intros; simp [dotProduct_add, mulVec_add])
    (by intros; simp [dotProduct_smul, mulVec_smul])

theorem pos_dot (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosDef) (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < (G *ᵥ v) ⬝ᵥ v := by
  have := hG.dotProduct_mulVec_pos hv
  simpa [dotProduct_comm, star_trivial] using this

theorem pd_symm (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosDef) : Mᵀ = M := by
  have h := hM.isHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem sym_dot (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ = M) (a b : Fin 3 → ℝ) :
    a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
  have e : a ᵥ* M = M *ᵥ a := by
    conv_lhs => rw [← h]
    exact vecMul_transpose M a
  rw [dotProduct_mulVec, e, dotProduct_comm]

/-- The splitting map of Theorem F at an affine view `v ≠ 0`:
`G ↦ (ℓ, H) = (G v, G⁻¹ |_{ann v})`. -/
noncomputable def metricSplit (v : Fin 3 → ℝ) (hv : v ≠ 0) (G : {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef}) :
    {l : Fin 3 → ℝ // 0 < l ⬝ᵥ v} × PD2 v :=
  (⟨G.1 *ᵥ v, pos_dot G.1 G.2 v hv⟩,
   ⟨restrictForm v G.1⁻¹, by
      intro a b
      exact sym_dot _ (pd_symm _ G.2.inv) _ _,
    by
      intro a ha
      have hs : (G.1⁻¹).PosDef := G.2.inv
      have := hs.dotProduct_mulVec_pos (x := (a : Fin 3 → ℝ)) (by simpa using ha)
      simpa [restrictForm, star_trivial] using this⟩)

/-- (Theorem F, full.)  For every `v ≠ 0`, `G ↦ (ℓ, H) = (G v, G⁻¹|_{ann v})` is a bijection from
positive definite `3×3` matrices onto `{ℓ | ℓ(v) > 0} × {symmetric positive definite forms on ann v}`.
(Reading: the depths `⟪G v, ·⟫` depend only on `ℓ`; the inverse is
`G⁻¹ = v vᵀ/ℓ(v) + (ℓ-complement extension of H)`.) -/
def ThmFBijection : Prop :=
  ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0), Function.Bijective (metricSplit v hv)

/-- (Anchor Lemma, core.)  `V ⊆ ℝ³` finite, `ν ≠ 0`, `c = max_V ν⬝x` (so `F = {x ∈ V | ν⬝x = c}` is the
face of `conv V` with outward normal `ν`, here only assumed nonempty), and `v ∈ V` a vertex farthest
behind the plane `ν⬝x = c`, i.e. `ν⬝v = min_V ν⬝x`.  Let `p* = v + ((c - ν⬝v)/ν⬝ν) • ν`, its foot on the
plane.  Then (a) `p*` lies in the plane; (b) the force line of `v` is `v + ℝν`, which passes through `p*`
(`p* - v = λ ν`, `λ ≥ 0`), and `p*` is the orthogonal projection (every `y` in the plane has
`(p* - v) ⬝ (y - p*) = 0`); (c) at every view `u ⊥ ν` (projection along `u`, `π_u y = y - (u⬝y/u⬝u) u`,
and `u ≠ 0`) the vertex and the foot have equal depth `u⬝v = u⬝p*`, `ν` stays the screen direction
(`ν⬝π_u y = ν⬝y`), so `v` is a back extreme of the projected set: `ν⬝π_u v ≤ ν⬝π_u x` for all
`x ∈ V` while `F` is a front extreme; that is, `ν` lies in `v`'s normal cone (with sign) at every
view of the circle, and the width of the projected set in direction `ν` is `c - ν⬝v`, attained by the
pair `F, v`, independent of `u`.  The content is elementary (orthogonal projection plus
`ν ⊥ u`); the substance of the paper's lemma is the consequences for witness sets, not this core. -/
def AnchorCore : Prop :=
  ∀ (V : Finset (Fin 3 → ℝ)) (ν : Fin 3 → ℝ) (c : ℝ) (v : Fin 3 → ℝ), ν ≠ 0 → v ∈ V →
    (∀ x ∈ V, ν ⬝ᵥ x ≤ c) → (∃ f ∈ V, ν ⬝ᵥ f = c) → (∀ x ∈ V, ν ⬝ᵥ v ≤ ν ⬝ᵥ x) →
    let l := (c - ν ⬝ᵥ v) / (ν ⬝ᵥ ν)
    let p := v + l • ν
    0 ≤ l ∧ ν ⬝ᵥ p = c ∧ (∀ y, ν ⬝ᵥ y = c → (p - v) ⬝ᵥ (y - p) = 0) ∧
    ∀ u : Fin 3 → ℝ, u ≠ 0 → u ⬝ᵥ ν = 0 →
      u ⬝ᵥ p = u ⬝ᵥ v ∧
      (∀ y, ν ⬝ᵥ (y - ((u ⬝ᵥ y) / (u ⬝ᵥ u)) • u) = ν ⬝ᵥ y) ∧
      (∀ x ∈ V, ν ⬝ᵥ (v - ((u ⬝ᵥ v) / (u ⬝ᵥ u)) • u) ≤ ν ⬝ᵥ (x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u)) ∧
      (∀ x ∈ V, ν ⬝ᵥ (x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u) ≤ c) ∧
      (∃ f ∈ V, ν ⬝ᵥ (f - ((u ⬝ᵥ f) / (u ⬝ᵥ u)) • u) = c)

/-- (Anchor Lemma, width form, exact first-order version.)  With `ν`, `c`, `F = {x ∈ V | ν⬝x = c}`
as above and `v` the *unique* minimizer of `ν⬝·` on `V`, for all `δ` near `0` the width
`w(μ) = max_V μ⬝x - min_V μ⬝x` satisfies exactly
`w(ν + δ) = w(ν) + max_{x ∈ F} (x - v) ⬝ δ`.
(For `δ ⊥ ν` this reads `max_{x∈F} ⟨x - p*, δ⟩`, since `⟨p* - v, δ⟩ = λ⟨ν, δ⟩ = 0`; there is no
`O(δ²)` term because `w` is piecewise linear for unnormalised `μ`.) -/
def AnchorWidth : Prop :=
  ∀ (V : Finset (Fin 3 → ℝ)) (hV : V.Nonempty) (ν : Fin 3 → ℝ) (c : ℝ) (v : Fin 3 → ℝ), v ∈ V →
    (∀ x ∈ V, ν ⬝ᵥ x ≤ c) → (∀ x ∈ V, x ≠ v → ν ⬝ᵥ v < ν ⬝ᵥ x) →
    ∀ hF : (V.filter (fun x => ν ⬝ᵥ x = c)).Nonempty,
      ∀ᶠ δ in nhds (0 : Fin 3 → ℝ),
        (V.sup' hV (fun x => (ν + δ) ⬝ᵥ x) - V.inf' hV (fun x => (ν + δ) ⬝ᵥ x)) =
          (c - ν ⬝ᵥ v) + (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => (x - v) ⬝ᵥ δ)

/-- (Corollary 8.6, no genericity needed.)  Let `x i ∈ ℝ²` be the corners (screen positions) of a
silhouette with depths `z i`; the silhouette is `D = conv {x i}`.  A first-order motion of the inner
copy is a small rotation about a horizontal axis `g`, a translation `t`, and a spin `θ` about the view
axis; it moves corner `i` with velocity `t + z i • g + θ • J (x i)`, `J (a,b) = (-b, a)`.  The motion is
*inward* if every corner enters the interior of `D` along it (for all small `ε > 0`, the point
`x i + ε • velocity` lies in `interior D`).  Then every inward motion has `θ ≠ 0`.

Proof idea: take `n ⊥ g` (`n = J g`, or any `n ≠ 0` if `g = 0`).  The corners extreme in the
directions `n` and `-n` have velocities with `n`-component `n ⬝ t` (the `g` and, for `θ = 0`, the
`J x` terms vanish), and inwardness forces it `< 0` at one and `> 0` at the other.  The statement is
not just bilinearity, but it is elementary and holds at every view, generic or not. -/
def InwardMotionHasSpin : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x : ι → Fin 2 → ℝ) (z : ι → ℝ) (t g : Fin 2 → ℝ) (θ : ℝ),
    (∀ i, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      x i + ε • (t + z i • g + θ • ![-(x i 1), x i 0]) ∈ interior (convexHull ℝ (Set.range x))) →
    θ ≠ 0

end MetricSpin

end MinimalityExtra
