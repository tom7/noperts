module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.CrossProduct
public import MainTheorem
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Side results of the work on 7-vertex Noperts

`MainTheorem.lean` defines the Rupert property and states the target
`AnySevenVertexNopertIsSimplicial`: Every 7-vertex Nopert has only triangular faces. This file
collects results found along the way that are of interest on their own. Each is a `def ... : Prop`
in the style of `MainTheorem.lean`, using only Mathlib and that file. The proofs are in
`MinimalityExtra/`, tied together in `ProofOfMinimalityExtra.lean`.

## Terms

A polytope is *Rupert* if one copy can pass through a straight hole in another: Some shadow of it
fits, after a rotation and a translation, into the interior of another of its shadows. A *Nopert* is
a polytope that is not Rupert.

A *view* is a direction `u`. Along it the polytope casts a *shadow* (or silhouette), a convex
polygon. The *rim* is the cycle of vertices over the corners of the shadow, and the *depth* of a
point is its coordinate along `u`. A view is *unimodal* if the depths, read around the rim, have one
local maximum. It is *two-peaked* if they have two.

A *first-order passage* starts from two coincident copies at a view and moves one of them by an
infinitesimal rotation and translation so that every rim corner goes strictly into the shadow. A
small finite motion then gives a real passage. A view with such a motion is *free*, and otherwise
*rigid*. The obstruction to freedom at an otherwise good view is a *horizontal double normal* (HDN):
a chord of constant depth between two points of the rim, perpendicular to parallel support lines of
the shadow at both ends.

A *metric* is a positive definite matrix `G`. The Rupert property is not invariant under linear
maps, and applying `A` to a shape amounts to keeping the shape and measuring with `G = AᵀA`. The
depth of `x` along `v` is then `⟪G v, x⟫`. A claim made "at every metric" covers all linear images
of a shape at once.

A *type* is one of the combinatorial types of 7-vertex polytopes, in the numbering of the proof.

## Contents

- *Criteria:* Conditions that make a polytope Rupert or a view free, from depth patterns on the rim
  or from the position of faces, explicit Rupert shapes, and a depth lemma for an edge of a
  quadrilateral seen end-on (the quad-edge lemma).
- *Limits of the method:* Examples showing that these criteria have no converse and that natural
  shortcuts fail. What a rim looks like does not decide freedom, the chirotope does not decide the
  silhouette, and limits of views can mislead.
- *Metrics:* What holds at every metric, what fails at some metric, how two views can cover all
  metrics between them, and how a metric splits into depth data and screen data.
- *Passages in general:* Stability, monotonicity, symmetry and obstructions, with no first-order
  assumption.
- *Tools:* Facts about cyclic sequences, arrangements of great circles and combinatorial
  silhouettes.

Results appear in short sections by topic, not in order of importance, and each definition comes
just before its first use. Tags in parentheses, such as (Theorem U), are the names used in the
project's notes.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra

open scoped RealInnerProductSpace
open Finset

/-- The cross product in `ℝ³`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The determinant of `a`, `b`, `c` (the triple product `(a × b) · c`). All orientation tests in
this file have the form `0 < det3 (b - a) (c - a) w`, which says that `a`, `b`, `c` turn
counterclockwise in the shadow along `w`, with `w` pointing at the viewer. -/
noncomputable def det3 (a b c : ℝ³) : ℝ :=
  (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
    (a 0 * b 1 - a 1 * b 0) * c 2

/-- Distinct reals, read cyclically, with exactly one local maximum (hence exactly one local
minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The cycle `lab` is the *strict rim* of the view `u`: In the shadow along `u`, the points
`x (lab i)` are the corners, in counterclockwise order, of a strictly convex polygon with every
other point strictly inside. -/
def StrictRim {k : ℕ} [NeZero k] (x : Fin 7 → ℝ³) (u : ℝ³) (lab : ZMod k → Fin 7) : Prop :=
  ∀ (m : Fin 7) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- The points `x` have a *unimodal view*: A direction with a strict rim of at least three distinct
points whose depths `⟪x i, u⟫` are cyclically unimodal. Such a `u` is nonzero, since `StrictRim`
fails at `0`. -/
def HasUnimodalView (x : Fin 7 → ℝ³) : Prop :=
  ∃ (u : ℝ³) (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin 7),
    3 ≤ k ∧ Function.Injective lab ∧ StrictRim x u lab ∧
      IsCyclicUnimodal (fun i => ⟪x (lab i), u⟫)

/-- The local condition at the point `x` for the view `w` and the infinitesimal motion `(ω, τ)`,
which gives each point `y` the velocity `ω × y + τ`. Either the velocity of `x` points strictly into
the angle `y₀ x y₁` for two points of `V` (the case of a shadow corner), or `x` lies strictly inside
a projected triangle of points of `V`, so that it stays hidden. -/
def TiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, 0 < det3 (y₁ - x) (y₀ - x) w ∧
      0 < det3 (y₁ - x) (cross ω x + τ) w ∧ 0 < det3 (x - y₀) (cross ω x + τ) w) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
      0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w)

/-- `V` has a *first-order passage*: A nonzero view `w` and a motion `(ω, τ)` with a `TiltCert` at
every point. -/
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

/-!
## Depth at every metric

Results about metrics use coordinate vectors `Fin 3 → ℝ`, on which matrices act directly.
-/

section MetricUniform

open Matrix

/-- The depth of `x` along the view `v` in the metric `G`, written as the functional `G v` applied
to `x`. -/
def depth (G : Matrix (Fin 3) (Fin 3) ℝ) (v x : Fin 3 → ℝ) : ℝ := (G *ᵥ v) ⬝ᵥ x

/-- `det3` for coordinate vectors. -/
def tripleProduct (a b c : Fin 3 → ℝ) : ℝ :=
  (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
    (a 0 * b 1 - a 1 * b 0) * c 2

/-- Four reals, read cyclically, are *two-peaked*: Both entries of one diagonal are strictly above
both entries of the other. Unlike `IsCyclicTwoPeaked`, this allows a tie within a diagonal. -/
def TwoCyclicPeaks4 (z : ZMod 4 → ℝ) : Prop :=
  max (z 1) (z 3) < min (z 0) (z 2) ∨ max (z 0) (z 2) < min (z 1) (z 3)

/-- The cycle `x` is a strictly convex polygon in a plane with normal `n`, with its corners in
counterclockwise order as seen from the tip of `n`. -/
def IsStrictConvexPlanarCycle {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (n : Fin 3 → ℝ) :
    Prop :=
  (∀ i, n ⬝ᵥ x i = n ⬝ᵥ x 0) ∧
    ∀ i m : ZMod k, m ≠ i → m ≠ i + 1 → 0 < tripleProduct (x (i + 1) - x i) (x m - x i) n

/-- **Any depth functional occurs (Theorem F, easy half).** The only thing a metric forces on the
depths at a view `v` is that `v` itself has positive depth: Every linear functional positive on `v`
is the depth functional of some metric. -/
def ExistsMetricWithPrescribedDepth : Prop :=
  ∀ v l : Fin 3 → ℝ, 0 < l ⬝ᵥ v →
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ v = l

/-- **Four non-coplanar points are two-peaked at some metric (Theorem U, four points).** This holds
at every view and in every cyclic order, so no view with such a rim is unimodal at every metric. Two
peaks, not rigidity, which is stronger. `TwoPeakedRimOpenSetOfMetrics` is the version for rims of
any length. -/
def TwoPeakedDepthsAtSomeMetric : Prop :=
  ∀ (x : ZMod 4 → Fin 3 → ℝ) (v : Fin 3 → ℝ),
    LinearIndependent ℝ ![x 1 - x 0, x 2 - x 0, x 3 - x 0] → v ≠ 0 →
      ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
        TwoCyclicPeaks4 (fun i => depth G v (x i)) ∧
        ¬ IsCyclicUnimodal (fun i => depth G v (x i))

/-- **Coplanar rims are unimodal at every metric (Theorem C, depth part).** A plane meets the
boundary of a convex polygon in at most two points, so any linear functional with distinct values on
the corners goes up once and down once. The depth functional at any metric is such a functional. -/
def CoplanarRimDepthUnimodal : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ (x : ZMod k → Fin 3 → ℝ) (n : Fin 3 → ℝ),
    IsStrictConvexPlanarCycle x n → ∀ l : Fin 3 → ℝ,
      Function.Injective (fun i => l ⬝ᵥ x i) → IsCyclicUnimodal (fun i => l ⬝ᵥ x i)

/-- **A planar convex quadrilateral is never two-peaked.** The contrast to
`TwoPeakedDepthsAtSomeMetric`. The two diagonals cross, so no linear functional puts one strictly
above the other, even if ties are allowed. -/
def CoplanarConvexQuadrilateralNeverTwoPeaked : Prop :=
  ∀ (x : ZMod 4 → Fin 3 → ℝ) (n : Fin 3 → ℝ),
    IsStrictConvexPlanarCycle x n → ∀ l : Fin 3 → ℝ, ¬ TwoCyclicPeaks4 (fun i => l ⬝ᵥ x i)

end MetricUniform

/-! ## Rim shape against first-order freedom -/

section TetrahedronViews

/-- `StrictRim` for a family indexed by any `Fin n`. -/
def StrictRimN {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ (m : Fin n) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- Distinct reals, read cyclically, with exactly two local maxima (hence exactly two local minima).
For `k = 4` this is `TwoCyclicPeaks4` for distinct entries. -/
def IsCyclicTwoPeaked {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 2

/-- The view `w` of `V` is *free*: Some motion has a `TiltCert` at every point, as in
`HasFirstOrderPassage`. A view is *rigid* if it is not free. -/
def FreeAt (V : Finset ℝ³) (w : ℝ³) : Prop :=
  ∃ ω τ : ℝ³, ∀ y ∈ V, TiltCert V w ω τ y

/-- **Rim shape and first-order freedom are independent at a single view.** One tetrahedron has
three views with four-corner rims: unimodal and rigid, two-peaked and free, two-peaked and rigid. So
a unimodal rim alone does not make a view free (that also needs no horizontal double normal), and a
free view need not be unimodal. -/
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

/-- **First-order freedom depends on the metric; the combinatorics does not.** Same tetrahedron,
same affine view, same rim, same depth order, two metrics: free in one, rigid in the other. So
freedom at a two-peaked rim is not combinatorial. The statement moves the points rather than the
metric: `A` carries `x` and `v` to the same shape seen in the metric `G = AᵀA`. -/
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

/-! ## The chirotope -/

section Chirotope

open Matrix

/-- Two labeled 5-point configurations have the same *chirotope*: Every 4-point determinant has the
same sign in both. -/
def SameChirotope (x y : Fin 5 → Fin 3 → ℝ) : Prop :=
  ∀ i j k l : Fin 5,
    SignType.sign (tripleProduct (x j - x i) (x k - x i) (x l - x i)) =
      SignType.sign (tripleProduct (y j - y i) (y k - y i) (y l - y i))

/-- No four of the five points are coplanar. -/
def ChirotopeGeneric (x : Fin 5 → Fin 3 → ℝ) : Prop :=
  ∀ i j k l : Fin 5, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    tripleProduct (x j - x i) (x k - x i) (x l - x i) ≠ 0

/-- The directed pair `(a, b)` is a side of the shadow of `p` along `u`: All other points lie
strictly to its left. Used with `u` the direction from point `3` to point `4`, so point `4` is
exempt, since it projects onto point `3`. -/
def IsShadowSide (p : Fin 5 → Fin 3 → ℝ) (u : Fin 3 → ℝ) (a b : Fin 5) : Prop :=
  ∀ m : Fin 5, m ≠ a → m ≠ b → m ≠ 4 → 0 < tripleProduct (p b - p a) (p m - p a) u

/-- **The chirotope does not determine the silhouette.** Two generic 5-point configurations with the
same chirotope can have different shadows along the line through the same two of their points. That
direction depends on 5-point determinants such as `det(b - a, d - c, e - c)`, which the chirotope
does not record, so a certificate at such a view cannot depend on the chirotope alone. -/
def ChirotopeDoesNotDetermineSilhouette : Prop :=
  ∃ x y : Fin 5 → Fin 3 → ℝ, ChirotopeGeneric x ∧ ChirotopeGeneric y ∧ SameChirotope x y ∧
    ∃ a b : Fin 5, a ≠ 4 ∧ b ≠ 4 ∧ a ≠ b ∧
      IsShadowSide x (x 4 - x 3) a b ∧ ¬ IsShadowSide y (y 4 - y 3) a b

end Chirotope

/-! ## Arrangements of great circles -/

section ArrangementVertices

open Matrix

/-- **Arrangement vertices suffice.** Finitely many linear forms in the view cut the sphere of views
along great circles. If some view makes all the forms positive, then a vertex of this arrangement,
with a small tilt to break its ties, does too. So a search for a cell defined by the signs of linear
forms need only try arrangement vertices. Conditions of the opposite sign are handled by negating
the form. The two independent forms are what make a vertex exist, and a nonempty chamber does not supply them (see `ChamberNeedsRank`). -/
def ArrangementVerticesSuffice : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    (∃ i j, LinearIndependent ℝ ![l i, l j]) →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)

/-- **Arrangement vertices suffice (spanning forms).** `ArrangementVerticesSuffice` for forms that
span the dual of `ℝ³`. Spanning forms contain an independent pair, so this is a special case. -/
def ArrangementVerticesSufficeSpan : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    Submodule.span ℝ (Set.range l) = ⊤ →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)

/-- **Arrangement vertices suffice (explicit tilt).** `ArrangementVerticesSuffice` with its
lexicographic conclusion written out: `u₀ + ε • d` makes all the forms positive for every small
`ε > 0`. -/
def ArrangementVerticesSufficeLex : Prop :=
  ∀ (n : ℕ) (l : Fin n → Fin 3 → ℝ),
    (∃ i j, LinearIndependent ℝ ![l i, l j]) →
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) →
    ∃ (u₀ : Fin 3 → ℝ) (i j : Fin n) (d : Fin 3 → ℝ),
      u₀ ≠ 0 ∧ LinearIndependent ℝ ![l i, l j] ∧ l i ⬝ᵥ u₀ = 0 ∧ l j ⬝ᵥ u₀ = 0 ∧
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ k, 0 < l k ⬝ᵥ (u₀ + ε • d))

/-- **The independent pair is not automatic.** A nonempty family of forms can have a nonempty
chamber without containing two independent forms (one form, for instance), so the rank hypothesis
of `ArrangementVerticesSuffice` is a real condition and not a consequence of the chamber being
nonempty. -/
def ChamberNeedsRank : Prop :=
  ∃ (n : ℕ) (l : Fin n → Fin 3 → ℝ), 0 < n ∧
    (∃ d : Fin 3 → ℝ, ∀ k, 0 < l k ⬝ᵥ d) ∧
    ¬ ∃ i j, LinearIndependent ℝ ![l i, l j]

end ArrangementVertices

/-! ## Boxes -/

section Box

/-- The sign of coordinate `j` at corner `i` of a box: `1` exactly when bit `j` of `i` is set. -/
noncomputable def boxSign (j : ℕ) (i : Fin 8) : ℝ := if i.val / 2 ^ j % 2 = 1 then 1 else -1

/-- The eight corners of the box with half-sides `a`, `b`, `c`. -/
noncomputable def boxPts (a b c : ℝ) : Fin 8 → ℝ³ :=
  fun i => !₂[boxSign 0 i * a, boxSign 1 i * b, boxSign 2 i * c]

/-- **Rectangular boxes have no unimodal view.** At a generic view the six rim corners alternate
high and low. The cube is Rupert, so the unimodal criterion misses even the classical example.
Written out in full because `HasUnimodalView` is for seven points. -/
def BoxesHaveNoUnimodalView : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → ∀ (u : ℝ³) (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin 8),
    3 ≤ k → Function.Injective lab → StrictRimN (boxPts a b c) u lab →
      ¬ IsCyclicUnimodal (fun i => ⟪boxPts a b c (lab i), u⟫)

end Box

/-!
## Free views that are not unimodal

Two criteria for freedom at a single view that allow any number of peaks.
-/

section DepthSeparated

/-- The point at the depth of the corner `c` on the line through the edge `a`. Its chord to `c` is
horizontal. -/
noncomputable def levelPoint {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : ℝ³ :=
  X a + (⟪X c - X a, w⟫ / ⟪X (a + 1) - X a, w⟫) • (X (a + 1) - X a)

/-- Every point off the rim `lab` lies strictly inside a projected triangle of points, as `TiltCert`
asks of a hidden point. Only a hidden point on the boundary of every such triangle fails this, a
special position. -/
def HiddenInTriangles {n k : ℕ} (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ m, (∀ i, m ≠ lab i) → ∃ p ∈ Finset.univ.image x, ∃ q ∈ Finset.univ.image x, ∃ r ∈ Finset.univ.image x,
    0 < det3 (q - p) (r - p) w ∧ 0 < det3 (q - p) (x m - p) w ∧
    0 < det3 (r - q) (x m - q) w ∧ 0 < det3 (p - r) (x m - r) w

/-- (Edge `a`, corner `c`) is a *split antipodal level pair* of the cycle `X` at the view `w`: `c`
is the unique corner farthest across from the edge `a`, so the support lines at the two are
parallel, and the level of `c` splits the rim. The corners on the arc from `c` to `a` lie on one
side of that level, and those on the arc from `a + 1` back to `c` on the other. This is
`Minimality.IsDepthSeparatedPair`, without a frame and with a strict antipode. -/
def IsDepthSeparatedAt {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : Prop :=
  (∀ i, i ≠ c → det3 (X (a + 1) - X a) w (X c) < det3 (X (a + 1) - X a) w (X i)) ∧
    (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X c, w⟫ < ⟪X (c + s), w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∨
      ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + s), w⟫))

/-- **Depth-separated views are free (Theorem 8.10).** A rim can have any number of peaks: The view
is free as soon as an edge and its antipodal corner split the rim by depth and the horizontal chord
between them is not a double normal. On a unimodal rim every level splits the rim like this. The
version in a frame is `Minimality.exists_tiltCert_of_depthSeparated`. -/
def DepthSeparatedViewIsFree : Prop :=
  ∀ (n k : ℕ) [NeZero k] (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) (a c : ZMod k),
    3 ≤ k → Function.Injective lab → StrictRimN x w lab → HiddenInTriangles x w lab →
    IsDepthSeparatedAt (fun i => x (lab i)) w a c →
    ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c), x (lab (a + 1)) - x (lab a)⟫ ≠ 0 →
    FreeAt (Finset.univ.image x) w

/-- The spin part of a row of the Edge-Plane Lemma, for the end `X j` of the edge `i`: The rotation
about the vertical through `X a`, corrected so that the edge `a` keeps its line. -/
noncomputable def edgePlaneSpin {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k) : ℝ :=
  det3 (X (i + 1) - X i) (cross w (X j - X a)) w +
    (⟪X j - X a, w⟫ / ⟪X (a + 1) - X a, w⟫) *
      det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) w) w

/-- **Edge-Plane Lemma.** One way to show that a view is free is to turn about an axis in the plane
through a rim edge `a` normal to its support plane. Such motions have three parameters `(α, μ, s)`,
and the condition at each other edge asks the line `ρ = α + μ z` to separate two point sets in a
plane. If some choice of parameters meets all these conditions, the view is free. -/
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

/-! ## Limit rows -/

section LimitRows

/-- The row of the corner `X i` of the cycle `X` at the view `w` toward `X (i + 1)`, as a linear
form in the motion `(ω, τ)`: The velocity inequality of `TiltCert` for that side. -/
noncomputable def cornerRowNext {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w ω τ : ℝ³) (i : ZMod k) : ℝ :=
  det3 (X (i + 1) - X i) (cross ω (X i) + τ) w

/-- The row of the corner `X i` toward `X (i - 1)`: The velocity inequality of `TiltCert` for that
side. -/
noncomputable def cornerRowPrev {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w ω τ : ℝ³) (i : ZMod k) : ℝ :=
  det3 (X i - X (i - 1)) (cross ω (X i) + τ) w

/-- The `2k` corner rows of the cycle `X` at `w` are *rigid*, by a Farkas certificate: Nonnegative
weights, not all zero, whose combination vanishes for every motion. No motion then makes all the
rows positive. -/
def LimitRowsRigid {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∃ p q : ZMod k → ℝ, (∀ i, 0 ≤ p i ∧ 0 ≤ q i) ∧ (∃ i, 0 < p i ∨ 0 < q i) ∧
    ∀ ω τ : ℝ³, ∑ i, (p i * cornerRowNext X w ω τ i + q i * cornerRowPrev X w ω τ i) = 0

/-- **Limit rows can undercount.** Take a tetrahedron, a view `u` parallel to a face, and the rim of
the nearby tilted views `u + ε d`. Its corner rows evaluated at `u` itself, the *limit rows*, can be
rigid while every tilted view is free. So rigidity of the limiting first-order problem does not
imply rigidity of the nearby views. -/
def ExistsLimitRowsUndercount : Prop :=
  ∃ (x : Fin 4 → ℝ³) (lab : ZMod 3 → Fin 4) (u d : ℝ³) (ε₀ : ℝ),
    0 < ε₀ ∧ det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) ≠ 0 ∧
    Function.Injective lab ∧
    (∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      det3 (x b - x a) (x c - x a) u = 0 ∧ det3 (x b - x a) (x c - x a) d ≠ 0) ∧
    LimitRowsRigid (fun i => x (lab i)) u ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      StrictRimN x (u + ε • d) lab ∧ HiddenInTriangles x (u + ε • d) lab ∧
        FreeAt (Finset.univ.image x) (u + ε • d)

end LimitRows

/-! ## Metric identities and a sequence lemma -/

section Identities

open Matrix in
/-- **HDN equation.** Take a rim side `a b` and a further point `c`, and let `y` be the point of the
line `a b` at the depth of `c`. The chord from `y` to `c` is horizontal, and it is `G`-perpendicular
to the side exactly when `(u × e)ᵀ adj(G) (w × e)` vanishes, where `e = b - a` and `w = c - a`. So
at a fixed view the HDN condition is linear in `adj(G)`. -/
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
/-- **Single-view Farkas.** A pattern of depth inequalities `z h ≥ z l` is impossible at the view
`r`, at every metric, when `-r` is a nonnegative combination of the differences `P h - P l`: The
pattern would give `-r` nonnegative depth, while `r` has positive depth. Only this direction is
stated. -/
def SingleViewFarkas : Prop :=
  ∀ {ι : Type} (P : ι → Fin 3 → ℝ) (p : Finset (ι × ι)) (r : Fin 3 → ℝ), r ≠ 0 →
    (∃ c : ι × ι → ℝ, (∀ q ∈ p, 0 ≤ c q) ∧
        -r = ∑ q ∈ p, c q • (P q.1 - P q.2)) →
      ¬ ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
          ∀ q ∈ p, P q.2 ⬝ᵥ G *ᵥ r ≤ P q.1 ⬝ᵥ G *ᵥ r

open Matrix in
/-- **Circle reduction, identity part.** At any view, the depths of vectors `r` in the plane `n^⊥`
see a metric `G` only through two things: its restriction to that plane, and one vector `g = d - m`
in the plane. Here `d` is the `G`-normal of the plane and `m` a fixed reference vector, both scaled
to pair to `1` with `n`. -/
def CircleReduction : Prop :=
  ∀ (G : Matrix (Fin 3) (Fin 3) ℝ) (n d m v r : Fin 3 → ℝ), G.PosDef → n ≠ 0 →
    G *ᵥ d = n → n ⬝ᵥ d = 1 → n ⬝ᵥ m = 1 → n ⬝ᵥ r = 0 →
      r ⬝ᵥ G *ᵥ v = r ⬝ᵥ G *ᵥ (v - (n ⬝ᵥ v) • m) - (n ⬝ᵥ v) * (r ⬝ᵥ G *ᵥ (d - m))

open Matrix in
/-- **Circle reduction, existence part.** The two pieces of `CircleReduction` are independent: Every
metric on the plane `n^⊥` and every vector `g` in the plane come from one positive definite `G`. -/
def CircleReductionExists : Prop :=
  ∀ (Y : Matrix (Fin 3) (Fin 3) ℝ) (n m g : Fin 3 → ℝ),
    Y.IsSymm → n ⬝ᵥ m = 1 → n ⬝ᵥ g = 0 →
    (∀ r, n ⬝ᵥ r = 0 → r ≠ 0 → 0 < r ⬝ᵥ Y *ᵥ r) →
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ (m + g) = n ∧
      ∀ r s, n ⬝ᵥ r = 0 → n ⬝ᵥ s = 0 → r ⬝ᵥ G *ᵥ s = r ⬝ᵥ Y *ᵥ s

/-- **Merge lemma.** Move along a circle of views, so that rim depths are affine in the parameter
`λ`, until two adjacent corners cross in depth at `λ₀`. If the rim with those two corners merged
into one is unimodal at the crossing, then the rim is unimodal just before or just after it. The
adjacent pair is normalized to `0, 1`: Entry `j` merges to entry `j - 1` in natural subtraction, so
`0` and `1` both go to `0`. -/
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

A passage survives small changes of the hull, at a rate given by its clearance.
-/

section Stable

/-- `W` has a passage with *clearance* `δ`: A closed `δ`-ball about each point of the inner shadow
lies in the outer shadow. -/
def HasClearance (W : Finset ℝ³) (δ : ℝ) : Prop :=
  ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ p ∈ convexHull ℝ (W : Set ℝ³),
    Metric.closedBall (inner_offset + proj_xy (inner_rotation.toEuclideanLin p)) δ ⊆
      { proj_xy (outer_rotation.toEuclideanLin q) | q ∈ convexHull ℝ (W : Set ℝ³) }

/-- **Clearance is stable.** A passage of `W` with clearance `δ` gives a passage of any `V` that
differs from `W` by less than `δ`, where the difference is the sum of the two one-sided distances
between the point sets and the hulls. -/
def ClearanceStable : Prop :=
  ∀ (V W : Finset ℝ³) (δ ε₁ ε₂ : ℝ), HasClearance W δ →
    (∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ ε₁) →
    (∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ ε₂) →
    ε₁ + ε₂ < δ → IsRupert V

/-- **A Rupert passage has positive clearance.** The inner shadow is compact and lies in the open
interior of the outer shadow. -/
def RupertHasClearance : Prop :=
  ∀ W : Finset ℝ³, IsRupert W → ∃ δ > 0, HasClearance W δ

/-- **Rupert near few points.** Every finite set Hausdorff-close to a set of at most six points is
Rupert, whatever its size, unless those points are close to collinear. The distance `ε` depends only
on `r`, a lower bound on twice the area of a triangle of `W`, for `W` in the unit ball. -/
def RupertNearFewPoints : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ε : ℝ, 0 < ε ∧ ∀ V W : Finset ℝ³, W.card ≤ 6 → (∀ w ∈ W, ‖w‖ ≤ 1) →
    (∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, r ≤ ‖cross (b - a) (c - a)‖) →
    (∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ ε) →
    (∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ ε) → IsRupert V

/-- **Close vertices make a 7-vertex polytope Rupert.** Merging two nearly equal vertices leaves at
most six points, so `RupertNearFewPoints` applies. Hence a 7-vertex Nopert in the unit ball that
contains a triangle of area at least `r / 2` has all its vertices at least `ε(r)` apart. The bound
comes from compactness and is not explicit. -/
def CloseVerticesRupert : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ε : ℝ, 0 < ε ∧ ∀ V : Finset ℝ³, V.card ≤ 7 → (∀ v ∈ V, ‖v‖ ≤ 1) →
    (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, r ≤ ‖cross (b - a) (c - a)‖) →
    (∃ x ∈ V, ∃ y ∈ V, x ≠ y ∧ dist x y < ε) → IsRupert V

/-- `L` *passes through* `W`: Some pose puts the shadow of `conv L` inside the interior of a shadow
of `conv W`. `IsRupert` is the case `L = W`. -/
def PassesThrough (L W : Finset ℝ³) : Prop :=
  ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  let inner_shadow :=
    { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (L : Set ℝ³) }
  let outer_shadow :=
    { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (W : Set ℝ³) }
  inner_shadow ⊆ interior outer_shadow

/-- **Sandwich.** If `conv W ⊆ conv K ⊆ conv L` and `L` passes through `W`, then `K` is Rupert. The
same pose works, since `K` has a smaller inner shadow than `L` and a larger outer shadow than `W`.
-/
def RupertSandwich : Prop :=
  ∀ W K L : Finset ℝ³,
    convexHull ℝ (W : Set ℝ³) ⊆ convexHull ℝ (K : Set ℝ³) →
    convexHull ℝ (K : Set ℝ³) ⊆ convexHull ℝ (L : Set ℝ³) →
    PassesThrough L W → IsRupert K

/-- **Cylinder extension.** A passage of `K₀` through itself survives adding any point `y` that, in
the inner pose, still projects into the interior of the outer shadow. The inner shadow grows only by
its hull with that point, and the outer shadow does not shrink. -/
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

A *test* is a rim with its view, and it *fails* at a metric if its depths there are not unimodal. A
single non-coplanar test fails at some metric (Theorem U), but two tests can cover all metrics
between them. These results say when.
-/

section TestPairs

open Matrix

/-- **Angle lemma (Lemma 13.2).** Two tests can have failures that exclude each other. A failure of
the first rim orders its depths, and if `u₂` lies in the cone of differences that this order makes
positive, the failure fixes the sign of the `G`-inner product of `u₁` and `u₂`. If every failure of
the second rim fixes the opposite sign, the two cannot happen at one metric, because `G` is
symmetric. So at every metric with distinct depths on both rims, one of the two is unimodal.

In the formula a failure is any injective sequence `z` that is not cyclically unimodal, and the cone
is spanned by the differences `x h - x l` with `z l < z h`. The formula spells out
`IsCyclicUnimodal`. -/
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

/-- The depth functionals at which a test with view `u` fails with the pattern `W`, where `W` is the
set of differences that the pattern makes positive. A depth functional is also positive on its own
view. -/
def FailCone (W : Set (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {φ | 0 < φ ⬝ᵥ u ∧ ∀ w ∈ W, 0 < φ ⬝ᵥ w}

/-- **Invisibility gives a sign (Lemma V (a)).** The pattern `W` is *invisible* along `v` if no
functional of its fail cone vanishes at `v`. Then `v` has one sign on the whole fail cone, which is
convex. -/
def InvisibilitySign : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v : Fin 3 → ℝ), (∀ φ ∈ FailCone W u, φ ⬝ᵥ v ≠ 0) →
    ∀ φ₁ ∈ FailCone W u, ∀ φ₂ ∈ FailCone W u, 0 < (φ₁ ⬝ᵥ v) * (φ₂ ⬝ᵥ v)

/-- **Two invisible failures exclude each other (Lemma V (b)).** Suppose the pattern of each test
is invisible along the view of the other. If one functional of each fail cone is chosen and they
give opposite signs on the other test's view, then at no metric do both tests fail. By invisibility
the chosen functionals speak for their whole cones. This is the angle lemma in the language of fail
cones. -/
def InvisibilitySignPair : Prop :=
  ∀ (W₁ W₂ : Set (Fin 3 → ℝ)) (u₁ u₂ : Fin 3 → ℝ),
    (∀ φ ∈ FailCone W₁ u₁, φ ⬝ᵥ u₂ ≠ 0) →
    (∀ φ ∈ FailCone W₂ u₂, φ ⬝ᵥ u₁ ≠ 0) →
    ∀ φ₁ ∈ FailCone W₁ u₁, ∀ φ₂ ∈ FailCone W₂ u₂,
      SignType.sign (φ₁ ⬝ᵥ u₂) ≠ SignType.sign (φ₂ ⬝ᵥ u₁) →
    ∀ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef →
      ¬ (G *ᵥ u₁ ∈ FailCone W₁ u₁ ∧ G *ᵥ u₂ ∈ FailCone W₂ u₂)

/-- **A rim edge parallel to the view (Corollary V1 (i)).** If the pattern contains an edge parallel
to `v`, it is invisible along `v`, and the sign of `v` on the fail cone is the sign of `c`, where
the edge is `c • v`. -/
def InvisibilityEdge : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v e : Fin 3 → ℝ) (c : ℝ), e ∈ W → e = c • v →
    ∀ φ ∈ FailCone W u, 0 < c * (φ ⬝ᵥ v)

/-- **A middle corner on a flat triple (Corollary V1 (ii)).** Let the projection of `x` along `v`
lie between those of `y` and `z`, with `κ v` the offset of `x` from the segment. If `x` is a strict
local maximum of the pattern between `y` and `z`, then `v` has the sign of `κ` on the fail cone. If
it is a strict local minimum, the opposite sign. -/
def InvisibilityFlat : Prop :=
  ∀ (W : Set (Fin 3 → ℝ)) (u v x y z : Fin 3 → ℝ) (t κ : ℝ), 0 ≤ t → t ≤ 1 →
    x - ((1 - t) • y + t • z) = κ • v →
    ((x - y ∈ W ∧ x - z ∈ W → ∀ φ ∈ FailCone W u, 0 < κ * (φ ⬝ᵥ v)) ∧
     (y - x ∈ W ∧ z - x ∈ W → ∀ φ ∈ FailCone W u, κ * (φ ⬝ᵥ v) < 0))

/-- **Two interior far corners are never metric-free (Lemma E′).** Four consecutive non-coplanar
points of a cycle, with diagonals not parallel in the shadow, already let some metric put two peaks
on the whole cycle, however long. In the application the cycle is a *closing* of an edge view: the
apex followed by the far corners. So such a closing is not unimodal at every metric. Here
"metric-free" means unimodal at every metric, not `FreeAt`, and the conclusion is two peaks, not
rigidity. Only one closing is treated, not both at once. -/
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

The basic criteria in the vocabulary of this file, proved in `ProofOfMinimalityExtra.lean` from the
repository's theorems.
-/

section Core

/-- **Unimodal view criterion (Theorem 7.3).** Seven points with a unimodal view are Rupert. There
is no condition on horizontal double normals: One can make that view rigid, but the points are still
Rupert. `ExistsFirstOrderPassageWithoutUnimodalView` shows that the converse fails. -/
def UnimodalViewIsRupert : Prop :=
  ∀ x : Fin 7 → ℝ³, HasUnimodalView x → IsRupert (Finset.univ.image x)

/-- **Coplanar silhouette theorem (Theorem 5).** If a planar, non-collinear subset `W` of `V` has,
along some direction `u` out of its plane, all the other points projecting into the relative
interior of `conv W`, then `V` is Rupert. The hypotheses are affine, so this covers all linear
images of a shape at once. -/
def CoplanarSilhouetteIsRupert : Prop :=
  ∀ (V W : Finset ℝ³) (u : ℝ³), W ⊆ V → ¬ Collinear ℝ (W : Set ℝ³) →
    Coplanar ℝ (W : Set ℝ³) → u ∉ (affineSpan ℝ (W : Set ℝ³)).direction →
    (∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))) →
    IsRupert V

/-- **Triangle shadow.** Theorem 5 when `W` is a triangle: If some shadow is a triangle of three
points of `V`, with all the others strictly inside, then `V` is Rupert. -/
def TriangleShadowIsRupert : Prop :=
  ∀ (V : Finset ℝ³) (a b c u : ℝ³), a ∈ V → b ∈ V → c ∈ V →
    AffineIndependent ℝ ![a, b, c] →
    u ∉ (affineSpan ℝ ({a, b, c} : Set ℝ³)).direction →
    (∀ v ∈ V, v ≠ a → v ≠ b → v ≠ c →
      ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ ({a, b, c} : Set ℝ³))) →
    IsRupert V

/-- The hypotheses of Theorem 5 (`CoplanarSilhouetteIsRupert`), bundled. -/
def CoplanarSilhouetteHyp (V W : Finset ℝ³) (u : ℝ³) : Prop :=
  W ⊆ V ∧ ¬ Collinear ℝ (W : Set ℝ³) ∧
    Coplanar ℝ (W : Set ℝ³) ∧ u ∉ (affineSpan ℝ (W : Set ℝ³)).direction ∧
    (∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³)))

/-- The points of `V` over the corners of the shadow `π '' conv V`, where `π` is a linear map to the
plane whose kernel is the view direction. -/
def ShadowCorners (V : Finset ℝ³) (π : ℝ³ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) : Set ℝ³ :=
  {v | v ∈ V ∧ π v ∈ Set.extremePoints ℝ (π '' convexHull ℝ (V : Set ℝ³))}

/-- On a nonempty open set of views, the shadow is solid, the points over its corners are coplanar,
and every other point projects into the open shadow. For each view the projection `π` is any linear
map with kernel `ℝ u`. -/
def CoplanarShadowCorners (V : Finset ℝ³) : Prop :=
  ∃ U : Set ℝ³, IsOpen U ∧ U.Nonempty ∧ (0 : ℝ³) ∉ U ∧
    ∀ u ∈ U, ∀ π : ℝ³ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2), LinearMap.ker π = Submodule.span ℝ {u} →
      (interior (π '' convexHull ℝ (V : Set ℝ³))).Nonempty ∧
      Coplanar ℝ (ShadowCorners V π) ∧
      ∀ v ∈ V, π v ∉ Set.extremePoints ℝ (π '' convexHull ℝ (V : Set ℝ³)) →
        π v ∈ interior (π '' convexHull ℝ (V : Set ℝ³))

/-- **Theorem 5 is an open condition (Proposition 27.14, (i) ⇔ (ii)).** For points in convex
position, the hypotheses of Theorem 5 hold for some `W` and `u` exactly when `CoplanarShadowCorners`
holds. They look tied to one view, but they describe an open set of views. -/
def CoplanarSilhouetteIff : Prop :=
  ∀ V : Finset ℝ³, (∀ v ∈ V, v ∈ Set.extremePoints ℝ (convexHull ℝ (V : Set ℝ³))) →
    ((∃ (W : Finset ℝ³) (u : ℝ³), CoplanarSilhouetteHyp V W u) ↔ CoplanarShadowCorners V)

end Core

/-! ## Robust unimodality -/

section RobustUnimodal

/-- A cyclic sequence, possibly with ties, is *robustly unimodal*: conditions (R1)–(R3), as in
`Minimality.IsRobustUnimodal`. Ties are allowed where they cannot create two peaks. -/
def IsRobustUnimodal {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  (∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    ¬ (z (B + b) < z (B + a) ∧ z (B + b) < z (B + c) ∧ z (B + d) < z (B + a) ∧
      z (B + d) < z (B + c))) ∧
  (∀ i j l : ZMod k, i ≠ j → j ≠ l → i ≠ l → z i = z j → z j = z l → False) ∧
  (∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    z (B + b) = z (B + c) →
      ¬ (z (B + a) < z (B + b) ∧ z (B + c) < z (B + d)) ∧
      ¬ (z (B + b) < z (B + a) ∧ z (B + d) < z (B + c)))

/-- The cyclic sequence has no *weak alternation*: No four entries in cyclic order `a, b, c, d` have
`min (z a, z c) ≥ max (z b, z d)`. -/
def WeakAlternationFree {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    ¬ (z (B + b) ≤ z B ∧ z (B + b) ≤ z (B + c) ∧ z (B + d) ≤ z B ∧ z (B + d) ≤ z (B + c))

/-- **Robustly unimodal means no alternation (Lemma AQ).** For `k ≥ 4` the three conditions of
robust unimodality amount to one: no up-down-up-down quartet, even with ties. -/
def RobustUnimodalIffNoAlternation : Prop :=
  ∀ (k : ℕ) [NeZero k], 4 ≤ k → ∀ z : ZMod k → ℝ, IsRobustUnimodal z ↔ WeakAlternationFree z

end RobustUnimodal

/-! ## An edge of a quadrilateral seen end-on -/

section QuadEdge

open Matrix

/-- **The quad-edge lemma: Lemma E with a point in the middle.**  Look along an edge `ab` of a
convex quadrilateral `a b m f`, with two more points `c` and `g`, so that `b` is deeper than `a`.
Lemma E (`Minimality/EdgePair.lean`) says that when the segment through `f` and `g` pierces the
triangle `abc`, then dropping `a` or dropping `b` leaves a four-corner rim whose depths are
unimodal. Here the edge `ab` also has the point `m` of the quadrilateral behind it, so dropping
`a` leaves the five-corner rim `b, m, f, c, g` instead of four corners. The lemma says that Lemma
E's conclusion survives, at the price of one more inequality. Either `b` is at least as far from the
plane `acf` as `g` is, or `c` is no higher than `f` over the plane `bgm`. Then at every view along
which `b` is deeper than `a`, one of the two rims, `a, f, c, g` or `b, m, f, c, g`, has no weak
alternation, except at the three directions in which three of the depths coincide. The strict form
says that when both inequalities are strict, only the normal of the plane `cfg` can fail.

This is a statement about six points in space, not about a polytope. The cycles are unimodal
in the sense of `WeakAlternationFree`, which allows ties. -/
def QuadEdgeLemma : Prop :=
  ∀ a b m f c g : Fin 3 → ℝ,
    (∃ t u : ℝ, 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ (1 - t) • a + t • m = (1 - u) • b + u • f) →
    (∃ p q r s : ℝ, 0 < p ∧ 0 < q ∧ 0 < r ∧ p + q + r = 1 ∧ 0 < s ∧ s < 1 ∧
      p • a + q • b + r • c = (1 - s) • f + s • g) →
    ((∃ (n : Fin 3 → ℝ) (k : ℝ), n ⬝ᵥ a = k ∧ n ⬝ᵥ c = k ∧ n ⬝ᵥ f = k ∧
        k < n ⬝ᵥ g ∧ n ⬝ᵥ g ≤ n ⬝ᵥ b) ∨
     (∃ (n : Fin 3 → ℝ) (k : ℝ), n ⬝ᵥ b = k ∧ n ⬝ᵥ g = k ∧ n ⬝ᵥ m = k ∧
        k < n ⬝ᵥ f ∧ n ⬝ᵥ c ≤ n ⬝ᵥ f)) →
    ∀ w : Fin 3 → ℝ, 0 < w ⬝ᵥ (b - a) →
      WeakAlternationFree (fun i : ZMod 4 => w ⬝ᵥ (![a, f, c, g] : ZMod 4 → Fin 3 → ℝ) i) ∨
      WeakAlternationFree (fun i : ZMod 5 => w ⬝ᵥ (![b, m, f, c, g] : ZMod 5 → Fin 3 → ℝ) i) ∨
      (w ⬝ᵥ c = w ⬝ᵥ f ∧ w ⬝ᵥ f = w ⬝ᵥ g) ∨ (w ⬝ᵥ a = w ⬝ᵥ c ∧ w ⬝ᵥ c = w ⬝ᵥ f) ∨
      (w ⬝ᵥ b = w ⬝ᵥ g ∧ w ⬝ᵥ g = w ⬝ᵥ m)

/-- **The quad-edge lemma, strict form.**  With the two inequalities of `QuadEdgeLemma` strict, the
only direction (along which `b` is deeper than `a`) at which neither rim is unimodal can be the
normal of the plane `cfg`, where `c`, `f`, `g` have equal depth. So the failure set is one ray. -/
def QuadEdgeLemmaStrict : Prop :=
  ∀ a b m f c g : Fin 3 → ℝ,
    (∃ t u : ℝ, 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ (1 - t) • a + t • m = (1 - u) • b + u • f) →
    (∃ p q r s : ℝ, 0 < p ∧ 0 < q ∧ 0 < r ∧ p + q + r = 1 ∧ 0 < s ∧ s < 1 ∧
      p • a + q • b + r • c = (1 - s) • f + s • g) →
    ((∃ (n : Fin 3 → ℝ) (k : ℝ), n ⬝ᵥ a = k ∧ n ⬝ᵥ c = k ∧ n ⬝ᵥ f = k ∧
        k < n ⬝ᵥ g ∧ n ⬝ᵥ g < n ⬝ᵥ b) ∨
     (∃ (n : Fin 3 → ℝ) (k : ℝ), n ⬝ᵥ b = k ∧ n ⬝ᵥ g = k ∧ n ⬝ᵥ m = k ∧
        k < n ⬝ᵥ f ∧ n ⬝ᵥ c < n ⬝ᵥ f)) →
    ∀ w : Fin 3 → ℝ, 0 < w ⬝ᵥ (b - a) → ¬ (w ⬝ᵥ c = w ⬝ᵥ f ∧ w ⬝ᵥ f = w ⬝ᵥ g) →
      WeakAlternationFree (fun i : ZMod 4 => w ⬝ᵥ (![a, f, c, g] : ZMod 4 → Fin 3 → ℝ) i) ∨
      WeakAlternationFree (fun i : ZMod 5 => w ⬝ᵥ (![b, m, f, c, g] : ZMod 5 → Fin 3 → ℝ) i)

end QuadEdge

/-! ## Metrics, spin, and the farthest vertex -/

section MetricSpin

open Matrix

/-- The covectors that vanish on `v`: the covectors of the screen of the view `v`, a plane when
`v ≠ 0`. -/
def annV (v : Fin 3 → ℝ) : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {φ | φ ⬝ᵥ v = 0}
  add_mem' := by intro a b ha hb; simp_all [add_dotProduct]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all [smul_dotProduct]

/-- Symmetric positive definite bilinear forms on `annV v`: the metrics of the screen, written on
covectors. -/
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

/-- The splitting of Theorem F at a view `v ≠ 0`: A metric `G` goes to its depth functional `G v`
and to the restriction of `G⁻¹` to `annV v`. -/
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

/-- **A metric is a depth functional plus a screen metric (Theorem F).** At a fixed view `v`, every
pair of a functional positive on `v` and a metric on the screen comes from exactly one `G`. So the
depths at a view and the shape of its shadow can be chosen independently. -/
def ThmFBijection : Prop :=
  ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0), Function.Bijective (metricSplit v hv)

/-- **Anchor Lemma, core.** Let `v` be a vertex farthest behind a supporting plane with normal `ν`.
At every view `u` parallel to the plane, `v` and its foot on the plane have the same depth, and the
width of the shadow in the direction `ν` is attained by the plane and `v`, the same width for all
`u`. So `v` stays antipodal to the plane around the whole circle of views. The content is
elementary. The consequences of the Anchor Lemma for witness sets are not stated here. -/
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

/-- **Anchor Lemma, width form.** Near a supporting normal `ν` with a unique opposite vertex `v`,
the width of `V` in the unnormalized direction `ν + δ` is exactly the width at `ν` plus
`max_{x ∈ F} (x - v) ⬝ δ`, where `F` is the set of points on the supporting plane. There is no
second-order term, because width in an unnormalized direction is piecewise linear. -/
def AnchorWidth : Prop :=
  ∀ (V : Finset (Fin 3 → ℝ)) (hV : V.Nonempty) (ν : Fin 3 → ℝ) (c : ℝ) (v : Fin 3 → ℝ), v ∈ V →
    (∀ x ∈ V, ν ⬝ᵥ x ≤ c) → (∀ x ∈ V, x ≠ v → ν ⬝ᵥ v < ν ⬝ᵥ x) →
    ∀ hF : (V.filter (fun x => ν ⬝ᵥ x = c)).Nonempty,
      ∀ᶠ δ in nhds (0 : Fin 3 → ℝ),
        (V.sup' hV (fun x => (ν + δ) ⬝ᵥ x) - V.inf' hV (fun x => (ν + δ) ⬝ᵥ x)) =
          (c - ν ⬝ᵥ v) + (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => (x - v) ⬝ᵥ δ)

/-- **Inward motions spin (Corollary 8.6).** A first-order motion of the inner copy is a tilt `g`, a
translation `t` and a spin `θ` about the view axis. It moves a corner at screen position `x i` and
depth `z i` with velocity `t + z i • g + θ • J (x i)`, where `J` is the quarter turn of the screen.
At any view, generic or not, no motion takes every corner into the open shadow without spin. Without
spin all corners have the same velocity in a direction `n` perpendicular to `g`, while the corners
extreme in the directions `n` and `-n` need opposite signs. -/
def InwardMotionHasSpin : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x : ι → Fin 2 → ℝ) (z : ι → ℝ) (t g : Fin 2 → ℝ) (θ : ℝ),
    (∀ i, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      x i + ε • (t + z i • g + θ • ![-(x i 1), x i 0]) ∈ interior (convexHull ℝ (Set.range x))) →
    θ ≠ 0

end MetricSpin

/-- `i` is a strict cyclic local maximum of `z`. -/
def IsCyclicPeak {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (i : ZMod k) : Prop :=
  z (i - 1) < z i ∧ z (i + 1) < z i

/-- The metrics at which the depths along `v` of the cycle `x` have two distinct strict peaks, as a
subset of the positive definite matrices with the subspace topology. -/
def twoPeakMetrics {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    Set {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef} :=
  {G | ∃ i j : ZMod k, i ≠ j ∧ IsCyclicPeak (fun m => depth G.1 v (x m)) i ∧
    IsCyclicPeak (fun m => depth G.1 v (x m)) j}

/-- **Non-coplanar rims are two-peaked on an open set of metrics (Theorem U).** Take distinct
points, not all coplanar, read in any cyclic order, and any view. The metrics that put at least two
peaks on the depths form a nonempty open set. With Theorem C: At a single view, only a coplanar rim
is unimodal at every metric. Two peaks, not exactly two, and not rigidity. -/
def TwoPeakedRimOpenSetOfMetrics : Prop :=
  ∀ (k : ℕ) [NeZero k] (x : ZMod k → Fin 3 → ℝ) (v : Fin 3 → ℝ),
    Function.Injective x → (¬ ∃ n : Fin 3 → ℝ, n ≠ 0 ∧ ∀ i, n ⬝ᵥ x i = n ⬝ᵥ x 0) → v ≠ 0 →
      IsOpen (twoPeakMetrics x v) ∧ (twoPeakMetrics x v).Nonempty ∧
        ∀ G ∈ twoPeakMetrics x v, ¬ IsCyclicUnimodal (fun i => depth G.1 v (x i))

/-! ## Opposite views -/

section OppositeView

/-- **No isometric copy in its own interior.** A nonempty compact set in the plane cannot be mapped
into its interior by a map that preserves distances on it. No convexity is needed: The diameter
could not be preserved. -/
def NoIsometricCopyInInterior : Prop :=
  ∀ B : Set (EuclideanSpace ℝ (Fin 2)), IsCompact B → B.Nonempty →
    ∀ φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ x ∈ B, ∀ y ∈ B, dist (φ x) (φ y) = dist x y) → ¬ φ '' B ⊆ interior B

/-- **No passage has opposite views.** If the inner and outer copies are viewed along opposite
directions, the inner shadow is a congruent copy of the outer one, and a compact set has no
congruent copy in its interior. The views are opposite when the third coordinate of each inner
rotated point is the negative of the outer one. `vs` must be nonempty, since the empty set lies in
every interior. -/
def NoOppositeViewPassage : Prop :=
  ∀ vs : Finset ℝ³, vs.Nonempty →
  ∀ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∀ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    (∀ p : ℝ³, inner_rotation.toEuclideanLin p 2 = - outer_rotation.toEuclideanLin p 2) →
    ¬ ({ inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) })

end OppositeView

/-! ## Two explicit shapes -/

section ExplicitShapes

/-- **All face-pair views of an explicit type 24 polytope are rigid.** A *face-pair view* looks
along the line where two facet planes meet, so that both facets are edge-on. There are seven points
(the shape `fpfail_24_r1`, with an exactly planar quadrilateral and integer coordinates) with nine
listed facets, every face-pair view of which is first-order rigid. So are the 50 reduced tests `T`,
which keep only part of the points: They drop the middle vertices of the two edge-on faces and, for
a shared edge, one end of it, with one test per facet pair sharing at most a vertex and two per pair
sharing an edge.

This is rigidity at these exact views, in the Euclidean metric, and no more. It says nothing about
nearby tilted views, and it does not say that the shape fails to be Rupert: Numerically it has a
finite passage. The statement also does not say that the nine facets are all the facets, which is
what would make the polytope type 24. -/
def Type24FacePairViewsRigid : Prop :=
  ∃ (x : Fin 7 → ℝ³) (N : Fin 9 → ℝ³) (c : Fin 9 → ℝ) (T : Fin 50 → Fin 9 × Fin 9 × Finset (Fin 7)),
    (∀ j i, ⟪N j, x i⟫ ≤ c j) ∧
    (∀ j, ∃ a b d : Fin 7, ⟪N j, x a⟫ = c j ∧ ⟪N j, x b⟫ = c j ∧ ⟪N j, x d⟫ = c j ∧
      det3 (x b - x a) (x d - x a) (N j) ≠ 0) ∧
    (∀ j k, j < k → cross (N j) (N k) ≠ 0 ∧ ¬ FreeAt (Finset.univ.image x) (cross (N j) (N k))) ∧
    (∀ j k, j < k → ∃ t, (T t).1 = j ∧ (T t).2.1 = k) ∧
    (∀ t, (T t).1 < (T t).2.1 ∧
      ¬ FreeAt ((T t).2.2.image x) (cross (N (T t).1) (N (T t).2.1)))

/-- **A neighbor of the Septopert is Rupert, by an explicit pose.** The Septopert is a simplicial
polytope with no generic unimodal view. These seven points are the simplicial shape `strict7_sept`
(`data/hard/strict7_sept.xyz`), near the Septopert but without its symmetry, rounded to three
decimals. The passage is tight, with clearance `0.0036`, about `0.4` percent of the diameter.
Nothing is claimed about first-order rigidity or about other views. -/
def Strict7SeptIsRupert : Prop :=
  IsRupert (Finset.univ.image (![!₂[(-112/125 : ℝ), (157/500 : ℝ), (311/1000 : ℝ)], !₂[(157/500 : ℝ), (-179/200 : ℝ), (39/125 : ℝ)], !₂[(63/200 : ℝ), (31/100 : ℝ), (-897/1000 : ℝ)], !₂[(331/500 : ℝ), (47/1000 : ℝ), (11/200 : ℝ)], !₂[(1/25 : ℝ), (329/500 : ℝ), (29/500 : ℝ)], !₂[(11/250 : ℝ), (53/1000 : ℝ), (327/500 : ℝ)], !₂[(-477/1000 : ℝ), (-487/1000 : ℝ), (-123/250 : ℝ)]] : Fin 7 → ℝ³))

end ExplicitShapes

/-- **Patch-edge lemma, geometric part.** Look along the segment from `v` to `w`. Suppose that
`v a c` is a supporting plane of `V` with `w` strictly off it, and that `b` is off it too. Then `v`
lies strictly beyond the plane `a b c`. How `w` sits relative to that plane is a hypothesis of the
edge pair theorem (Lemma E), not something this lemma decides. -/
def PatchEdgeBeyondPlane : Prop :=
  ∀ (V : Finset ℝ³) (v w a b c : ℝ³), v ∈ V → w ∈ V → a ∈ V → b ∈ V → c ∈ V →
    0 < det3 (a - v) (c - v) (w - v) →
    ((∀ z ∈ V, 0 ≤ det3 (a - v) (c - v) (z - v)) ∨
      (∀ z ∈ V, det3 (a - v) (c - v) (z - v) ≤ 0)) →
    det3 (a - v) (c - v) (b - v) ≠ 0 →
    0 < det3 (b - a) (c - a) (v - a)

section BoxRule

/-- **Box rule (Lemma R).** A thin body passes through a wide shadow of itself. If `V` fits in a
`μ × w` box in two perpendicular directions `e`, `n`, and some shadow of `V` contains the corners of
a rectangle at least that large in its interior, then `V` is Rupert. The inner view looks along
`e × n`, edge-on to both widths, and only the outer view needs a check. This rule is behind the
closed-form passages of thin shapes. `V` is assumed solid. -/
def BoxRule : Prop :=
  ∀ (V : Finset ℝ³), (interior (convexHull ℝ (V : Set ℝ³))).Nonempty →
    ∀ (e n : ℝ³), ⟪e, e⟫ = 1 → ⟪n, n⟫ = 1 → ⟪e, n⟫ = 0 →
    ∀ (R₂ : Matrix (Fin 3) (Fin 3) ℝ), R₂ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ →
    ∀ (a b μ w c₀ c₁ L H : ℝ), 0 < L → 0 < H → μ ≤ L → w ≤ H →
    (∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w) →
    (∀ s t : ℝ, (s = 0 ∨ s = 1) → (t = 0 ∨ t = 1) →
      !₂[c₀ + s * L, c₁ + t * H] ∈
        interior { proj_xy (R₂.toEuclideanLin p) | p ∈ convexHull ℝ (V : Set ℝ³) }) →
    IsRupert V

end BoxRule

/-! ## The corner wedge -/

/-- The seven vertices of the corner wedge `{0 ≤ X ≤ A, 0 ≤ Z ≤ B, 0 ≤ y ≤ (H1/A) X + (H6/B) Z}`, in
coordinates `(X, y, Z)`: a box over the rectangle `[0,A] × [0,B]` cut by a plane through the base
corner `(0,0,0)`. -/
noncomputable def cornerWedgeVertices (A B H1 H6 : ℝ) : Fin 7 → ℝ³ :=
  ![!₂[A, 0, 0], !₂[A, H1, 0], !₂[0, 0, 0], !₂[A, 0, B], !₂[A, H1 + H6, B],
    !₂[0, 0, B], !₂[0, H6, B]]

open Classical in
/-- **Corner wedges are Rupert (Theorem 02.W).** Every box over a rectangle cut by a plane through a
base corner is Rupert, for all four parameters: a whole family of 7-vertex shapes with one proof, by
first-order freedom with spin at views near the `Z` axis. -/
def CornerWedgeRupert : Prop :=
  ∀ A B H1 H6 : ℝ, 0 < A → 0 < B → 0 < H1 → 0 < H6 →
    IsRupert (Finset.univ.image (cornerWedgeVertices A B H1 H6))

/-! ## Flat metrics and defeat sets -/

section FlatMetrics

open Matrix

/-- `StrictRim` in coordinates, for a family indexed by any `Fin n`. The condition is affine: It
does not depend on a metric. -/
def StrictRimF {n k : ℕ} [NeZero k] (x : Fin n → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (lab : ZMod k → Fin n) : Prop :=
  ∀ (m : Fin n) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < tripleProduct (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- The points `x` have a unimodal view *at the metric `G`*: A strict rim, which does not depend on
`G`, whose depths in `G` are cyclically unimodal. For `G = 1` this is `HasUnimodalView` in
coordinates. There is no condition on horizontal double normals. -/
def HasUnimodalViewAt (G : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 7 → Fin 3 → ℝ) : Prop :=
  ∃ (u : Fin 3 → ℝ) (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin 7),
    3 ≤ k ∧ Function.Injective lab ∧ StrictRimF x u lab ∧
      IsCyclicUnimodal (fun i => depth G u (x (lab i)))

/-- **Flat metrics are unimodal (Lemma FL).** Let `w` be a view with a strict rim, and let metrics
`G m` flatten, after scaling, onto a rank-2 limit that collapses `w`. Then `x` has a unimodal view
at all but finitely many of these metrics. Assuming a strict rim excludes three or more rim corners
on one line of the shadow, where the rim would be decided at second order. That case is not
formalized. -/
def FlatMetricsUnimodal : Prop :=
  ∀ (x : Fin 7 → Fin 3 → ℝ) (w : Fin 3 → ℝ) (k : ℕ) [NeZero k] (lab : ZMod k → Fin 7),
    w ≠ 0 → 3 ≤ k → Function.Injective lab → StrictRimF x w lab →
    ∀ (G : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (Gs : Matrix (Fin 3) (Fin 3) ℝ),
      (∀ m, (G m).PosDef) →
      Filter.Tendsto (fun m => (G m).trace⁻¹ • G m) Filter.atTop (nhds Gs) →
      Gs *ᵥ w = 0 → (∀ d, Gs *ᵥ d = 0 → ∃ t : ℝ, d = t • w) →
      ∀ᶠ m in Filter.atTop, HasUnimodalViewAt (G m) x

/-- **Defeat set of a view cell (Lemma DC).** A metric *defeats* a cell of views if no view of the
cell is unimodal at it. Take the open cone of views spanned by `u 0, u 1, u 2`, all with the strict
rim `lab`. The first part says that a unimodal view of the cell is a unimodal view of `x`. The
second turns defeat into separation: `G` defeats the cell exactly when, for each unimodal depth
order `l0`, a nonzero `w` separates the functionals with that order from the cone of depth
functionals `G (u i)`. These conditions are bilinear in `(w, G)`. `G` can be any matrix here. -/
def DefeatCellCriterion : Prop :=
  ∀ (x : Fin 7 → Fin 3 → ℝ) (k : ℕ) [NeZero k] (lab : ZMod k → Fin 7)
    (u : Fin 3 → Fin 3 → ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ),
    3 ≤ k → Function.Injective lab →
    (∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → StrictRimF x (∑ i, a i • u i) lab) →
    ((∃ a : Fin 3 → ℝ, (∀ i, 0 < a i) ∧
        IsCyclicUnimodal (fun j => depth G (∑ i, a i • u i) (x (lab j)))) →
      HasUnimodalViewAt G x) ∧
    ((¬ ∃ a : Fin 3 → ℝ, (∀ i, 0 < a i) ∧
        IsCyclicUnimodal (fun j => depth G (∑ i, a i • u i) (x (lab j)))) ↔
      ∀ l0 : Fin 3 → ℝ, IsCyclicUnimodal (fun j => l0 ⬝ᵥ x (lab j)) →
        ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
          (∀ l : Fin 3 → ℝ, (∀ i j, l0 ⬝ᵥ x (lab i) < l0 ⬝ᵥ x (lab j) →
              l ⬝ᵥ x (lab i) < l ⬝ᵥ x (lab j)) → 0 ≤ l ⬝ᵥ w) ∧
          ∀ i, (G *ᵥ u i) ⬝ᵥ w ≤ 0)

end FlatMetrics

/-!
## Combinatorial silhouette codes of types 24 and 29

A view splits the faces into the front faces `S` and the back faces `Sᶜ`. Which `S` are possible can
be bounded from the combinatorics alone.
-/

section SilhouetteCodes

/-- The edges of a polygon given by its cyclic vertex list, each as an ordered pair `(min, max)`. -/
def polyEdges (L : List (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  ((L.zip (L.rotate 1)).map fun p => (min p.1 p.2, max p.1 p.2)).toFinset

/-- Two faces, given by the cyclic vertex lists `F f`, share an edge. -/
def FacesAdjacent (F : Fin 9 → List (Fin 7)) (f g : Fin 9) : Bool :=
  decide (polyEdges (F f) ∩ polyEdges (F g)).Nonempty

/-- One step of exploring `S` through adjacent faces: `T` together with the faces of `S` adjacent to
a face of `T`. -/
def exploreFaces (adj : Fin 9 → Fin 9 → Bool) (S T : Finset (Fin 9)) :
    Finset (Fin 9) :=
  T ∪ S.filter (fun g => ∃ f ∈ T, adj f g = true)

/-- `S` is connected in the dual graph: Exploring from some face of `S` for 8 steps, enough for 9
faces, reaches all of `S`. The bounded search keeps this decidable. -/
def DualConnected (adj : Fin 9 → Fin 9 → Bool) (S : Finset (Fin 9)) : Prop :=
  ∃ f ∈ S, (exploreFaces adj S)^[8] {f} = S

/-- The edges lying on a face of `S` and on a face outside `S`. -/
def silhouetteEdges (F : Fin 9 → List (Fin 7)) (S : Finset (Fin 9)) : Finset (Fin 7 × Fin 7) :=
  (S.biUnion fun f => polyEdges (F f)) ∩ (Sᶜ.biUnion fun g => polyEdges (F g))

/-- One step of exploring the vertices touched by the edge set `B` along edges of `B`. -/
def exploreVertices (B : Finset (Fin 7 × Fin 7)) (T : Finset (Fin 7)) : Finset (Fin 7) :=
  T ∪ Finset.univ.filter (fun w => ∃ e ∈ B, (e.1 ∈ T ∧ w = e.2) ∨ (e.2 ∈ T ∧ w = e.1))

/-- The nonempty edge set `B` is one simple cycle: Every vertex lies on `0` or `2` edges of `B`, and
exploring along `B` from some touched vertex for 6 steps, enough for 7 vertices, reaches all touched
vertices. -/
def IsSingleCycle (B : Finset (Fin 7 × Fin 7)) : Prop :=
  B.Nonempty ∧ (∀ v : Fin 7, (B.filter (fun e => v = e.1 ∨ v = e.2)).card = 0 ∨
      (B.filter (fun e => v = e.1 ∨ v = e.2)).card = 2) ∧
    ∃ v : Fin 7, (∃ e ∈ B, v = e.1 ∨ v = e.2) ∧
      (exploreVertices B)^[6] {v} = Finset.univ.filter (fun w => ∃ e ∈ B, w = e.1 ∨ w = e.2)

/-- `S` is a combinatorial silhouette code of the polytope with faces `F`: `S` and its complement
are nonempty and connected in the dual graph, and the edges between them form one simple cycle. -/
def IsSilhouetteCode (F : Fin 9 → List (Fin 7)) (S : Finset (Fin 9)) : Prop :=
  S.Nonempty ∧ Sᶜ.Nonempty ∧ IsSingleCycle (silhouetteEdges F S) ∧
    DualConnected (FacesAdjacent F) S ∧ DualConnected (FacesAdjacent F) Sᶜ

instance (adj : Fin 9 → Fin 9 → Bool) (S : Finset (Fin 9)) :
    Decidable (DualConnected adj S) := by
  unfold DualConnected; infer_instance

instance (B : Finset (Fin 7 × Fin 7)) : Decidable (IsSingleCycle B) := by
  unfold IsSingleCycle; infer_instance

instance (F : Fin 9 → List (Fin 7)) (S : Finset (Fin 9)) : Decidable (IsSilhouetteCode F S) := by
  unfold IsSilhouetteCode; infer_instance

/-- The 9 faces of type 24 as cyclic vertex lists (`sevenTypeFaces 23` of the proof). -/
def type24Faces : Fin 9 → List (Fin 7) :=
  ![[0,1,2],[0,1,6],[0,2,5],[0,4,3,5],[0,4,6],[1,2,6],[2,3,5],[2,3,6],[3,4,6]]

/-- The 9 faces of type 29 as cyclic vertex lists (`sevenTypeFaces 28` of the proof). -/
def type29Faces : Fin 9 → List (Fin 7) :=
  ![[0,1,2],[0,1,5],[0,2,3],[0,3,5],[1,2,4],[1,4,6,5],[2,3,4],[3,4,6],[3,5,6]]

/-- **Counts of silhouette codes.** Of the `2^9` sets of front faces, exactly 174 are
combinatorially possible for type 24 and 198 for type 29. Reversing the view swaps `S` and `Sᶜ`, so
exactly 87 and 99 of them contain face 0. These are combinatorial possibilities: The count does not
claim that a code is realized by a view of a given polytope. -/
def SilhouetteCodeCounts : Prop :=
  (Finset.univ.filter (IsSilhouetteCode type24Faces)).card = 174 ∧
  (Finset.univ.filter (IsSilhouetteCode type29Faces)).card = 198 ∧
  (Finset.univ.filter (fun S => (0 : Fin 9) ∈ S ∧ IsSilhouetteCode type24Faces S)).card = 87 ∧
  (Finset.univ.filter (fun S => (0 : Fin 9) ∈ S ∧ IsSilhouetteCode type29Faces S)).card = 99

end SilhouetteCodes

/-! ## Torque forms -/

section TorqueForms

open Matrix

/-- The covector `ι_x ω = det (x, ·)` on the screen `ℝ²`, as a vector: `det (x, y) = tfJ x ⬝ᵥ y`. -/
def tfJ (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![-x 1, x 0]

/-- The area form `det (a, b)` of the screen `ℝ²`. -/
def tfDet (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The symmetric product `f ⊙ ι_x ω` as a matrix: the form
`(y, y') ↦ (f(y) det (x, y') + f(y') det (x, y)) / 2`. -/
noncomputable def torqueTerm (x f : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![f 0 * tfJ x 0, (f 0 * tfJ x 1 + f 1 * tfJ x 0) / 2;
     (f 0 * tfJ x 1 + f 1 * tfJ x 0) / 2, f 1 * tfJ x 1]

/-- The torque form `S_f = Σ_i f_i ⊙ ι_{x_i} ω` of covector loads `f i` at screen points `x i`. -/
noncomputable def torqueForm {n : ℕ} (x f : Fin n → Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ i, torqueTerm (x i) (f i)

/-- **Torque forms (Theorem T, algebraic content).** A *load* puts a force `f i` on each screen
point `x i` of depth `z i`. It is *balanced* if `Σ f i = 0` and `Σ z i • f i = 0`, so that
translations and tilts do no work on it, and only spin remains. One symmetric form `S_f` holds its
torque in every screen metric at once. In the order of the formula: `S_f` is symmetric; for a
balanced load it is unchanged by the shears `x i ↦ x i + z i • a + b`; the torque in the metric
`g = AᵀA` is `√(det g) · tr (g⁻¹ S_f)`; and two opposite parallel forces have indefinite `S_f`, with
zero torque at `g` exactly when they form a horizontal double normal in `g`.

This is the algebra only. The criterion it serves, that a view is free exactly when the torques of
the extreme balanced loads have one sign, is not stated here. -/
def TorqueForms : Prop :=
  (∀ (n : ℕ) (x f : Fin n → Fin 2 → ℝ), (torqueForm x f)ᵀ = torqueForm x f) ∧
  (∀ (n : ℕ) (x f : Fin n → Fin 2 → ℝ) (z : Fin n → ℝ),
    ∑ i, f i = 0 → ∑ i, z i • f i = 0 → ∀ a b : Fin 2 → ℝ,
      torqueForm (fun i => x i + z i • a + b) f = torqueForm x f) ∧
  (∀ (n : ℕ) (x f : Fin n → Fin 2 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ), 0 < A.det →
    ∑ i, tfDet (A *ᵥ x i) ((Aᵀ)⁻¹ *ᵥ f i) =
      Real.sqrt (Aᵀ * A).det * ((Aᵀ * A)⁻¹ * torqueForm x f).trace) ∧
  (∀ (nn q c : Fin 2 → ℝ) (m : ℝ), m ≠ 0 → nn ⬝ᵥ (q - c) ≠ 0 →
    (torqueForm ![q, c] ![m • nn, (-m) • nn]).det < 0 ∧
    ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.PosDef →
      (((g⁻¹ * torqueForm ![q, c] ![m • nn, (-m) • nn]).trace = 0) ↔
        tfJ nn ⬝ᵥ (g *ᵥ (q - c)) = 0))

end TorqueForms

/-- **Two disjoint faces (Lemma Q).** Look along the line where the planes of two disjoint faces
meet. Both faces are then edge-on. Suppose the shadow is a strictly convex quadrilateral with these
two faces as opposite sides, a single vertex over each corner, the other vertices of the faces over
the open sides, and every remaining vertex strictly inside. If the depths are distinct and the same
face is the deeper one across both remaining sides, then `V` is Rupert. The sign `σ = ±1` is the
orientation of the cycle `xa₁ xa₂ xb₂ xb₁`. -/
def LemmaQTwoDisjointFaces : Prop :=
  ∀ (V F₁ F₂ : Finset ℝ³) (n₁ n₂ u₀ : ℝ³) (h₁ h₂ σ : ℝ) (xa₁ xa₂ xb₁ xb₂ : ℝ³),
    (∀ p ∈ V, p ∉ convexHull ℝ ((V.erase p : Finset ℝ³) : Set ℝ³)) →
    F₁ ⊆ V → F₂ ⊆ V → Disjoint F₁ F₂ → 3 ≤ F₁.card → 3 ≤ F₂.card →
    (∀ p ∈ V, ⟪n₁, p⟫ ≤ h₁ ∧ (⟪n₁, p⟫ = h₁ ↔ p ∈ F₁)) →
    (∀ p ∈ V, ⟪n₂, p⟫ ≤ h₂ ∧ (⟪n₂, p⟫ = h₂ ↔ p ∈ F₂)) →
    cross n₁ n₂ ≠ 0 → u₀ ≠ 0 → ⟪n₁, u₀⟫ = 0 → ⟪n₂, u₀⟫ = 0 →
    xa₁ ∈ F₁ → xa₂ ∈ F₁ → xb₁ ∈ F₂ → xb₂ ∈ F₂ →
    (∀ y ∈ F₁, y ≠ xa₁ → y ≠ xa₂ →
      ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ y = xa₁ + t • (xa₂ - xa₁) + s • u₀) →
    (∀ y ∈ F₂, y ≠ xb₁ → y ≠ xb₂ →
      ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ y = xb₁ + t • (xb₂ - xb₁) + s • u₀) →
    (σ = 1 ∨ σ = -1) →
    (0 < σ * det3 (xa₂ - xa₁) (xb₂ - xa₁) u₀ ∧ 0 < σ * det3 (xa₂ - xa₁) (xb₁ - xa₁) u₀ ∧
     0 < σ * det3 (xb₂ - xa₂) (xb₁ - xa₂) u₀ ∧ 0 < σ * det3 (xb₂ - xa₂) (xa₁ - xa₂) u₀ ∧
     0 < σ * det3 (xb₁ - xb₂) (xa₁ - xb₂) u₀ ∧ 0 < σ * det3 (xb₁ - xb₂) (xa₂ - xb₂) u₀ ∧
     0 < σ * det3 (xa₁ - xb₁) (xa₂ - xb₁) u₀ ∧ 0 < σ * det3 (xa₁ - xb₁) (xb₂ - xb₁) u₀) →
    (∀ p ∈ V, p ∉ F₁ → p ∉ F₂ →
      0 < σ * det3 (xa₂ - xa₁) (p - xa₁) u₀ ∧ 0 < σ * det3 (xb₂ - xa₂) (p - xa₂) u₀ ∧
      0 < σ * det3 (xb₁ - xb₂) (p - xb₂) u₀ ∧ 0 < σ * det3 (xa₁ - xb₁) (p - xb₁) u₀) →
    Set.InjOn (fun x => ⟪u₀, x⟫) (V : Set ℝ³) →
    0 < (⟪u₀, xa₁⟫ - ⟪u₀, xb₁⟫) * (⟪u₀, xa₂⟫ - ⟪u₀, xb₂⟫) →
    IsRupert V

/-! ## Vertices over the boundary of a shadow -/

/-- **Vertices over the boundary (Lemma VF).** A vertex over the boundary of a shadow is a corner of
the shadow, and the only vertex over that corner, unless it lies on an edge or 2-face parallel to
the view. So at a view parallel to no edge or 2-face, the vertices over the boundary are exactly the
rim, with one vertex per corner. This holds for any polytope. -/
def VertexOverBoundaryOnFaceAlongView : Prop :=
  ∀ (V : Finset ℝ³) (u n y : ℝ³), n ≠ 0 → ⟪n, u⟫ = 0 →
    y ∈ (convexHull ℝ (V : Set ℝ³)).extremePoints ℝ →
    (∀ x ∈ convexHull ℝ (V : Set ℝ³), ⟪n, x⟫ ≤ ⟪n, y⟫) →
    ¬ ((y - (⟪y, u⟫ / ⟪u, u⟫) • u) ∈
          ((fun x : ℝ³ => x - (⟪x, u⟫ / ⟪u, u⟫) • u) '' convexHull ℝ (V : Set ℝ³)).extremePoints ℝ ∧
       ∀ y' ∈ (convexHull ℝ (V : Set ℝ³)).extremePoints ℝ,
          y' - (⟪y', u⟫ / ⟪u, u⟫) • u = y - (⟪y, u⟫ / ⟪u, u⟫) • u → y' = y) →
    u ∈ vectorSpan ℝ {x ∈ convexHull ℝ (V : Set ℝ³) | ⟪n, x⟫ = ⟪n, y⟫}

section Skeleton

/-- `IsCyclicUnimodal` for a nonempty list read as a cycle. -/
def ListCyclicUnimodal (L : List ℝ) : Prop :=
  ∃ h : L.length ≠ 0, @IsCyclicUnimodal L.length ⟨h⟩ (fun i => L.getD i.val 0)

/-- The skeleton of a chain from `a` to `c` with extreme entry `e`: the list `a, e, c`, with `e`
omitted when it equals an end. -/
noncomputable def chainSkeleton (a e c : ℝ) : List ℝ := if e = a ∨ e = c then [a, c] else [a, e, c]

/-- **Skeletons (Lemma SK).** A run of a cyclic sequence that goes down then up, or up then down,
can be shortened to its first, extreme and last entries without changing whether the cycle is
unimodal. -/
def SkeletonLemma : Prop :=
  ∀ (A B R : List ℝ) (a e c : ℝ), (A ++ B ++ R).Nodup → 2 ≤ (A ++ B).length →
    (A ++ B).head? = some a → (A ++ B).getLast? = some c → e ∈ A ++ B →
    ((A.Pairwise (· > ·) ∧ B.Pairwise (· < ·) ∧ ∀ x ∈ A ++ B, e ≤ x) ∨
     (A.Pairwise (· < ·) ∧ B.Pairwise (· > ·) ∧ ∀ x ∈ A ++ B, x ≤ e)) →
    (ListCyclicUnimodal (A ++ B ++ R) ↔ ListCyclicUnimodal (chainSkeleton a e c ++ R))

/-- **Face circle criterion (Corollary FC).** A view `u₀` parallel to a face sees it edge-on, and a
small tilt `v` opens a chain of its vertices on the rim. Those vertices share a line of the shadow
at `u₀`, so the rim is decided by the tilt, and the depths along the chain need not be checked one
by one: If they are V- or Λ-shaped and the rim with the chain replaced by its skeleton is unimodal,
then `V` is Rupert. The other rim edges pass the orientation test at `u₀` or, if edge-on there, at
the tilt. The sign `σ = ±1` is the orientation. -/
def FaceCircleSkeleton : Prop :=
  ∀ (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ), (σ = 1 ∨ σ = -1) → n ≠ 0 → u₀ ≠ 0 →
    ⟪n, u₀⟫ = 0 → (∀ y ∈ V, ⟪n, y⟫ ≤ h) →
    ∀ (N m : ℕ), 2 ≤ m → m ≤ N → ∀ (x : ZMod (N + 1) → ℝ³), (∀ i, x i ∈ V) →
    (∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h) →
    (∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀) →
    (∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n) →
    (∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      (0 < σ * det3 (x (i + 1) - x i) (y - x i) u₀ ∨
       (det3 (x (i + 1) - x i) (y - x i) u₀ = 0 ∧ 0 < σ * det3 (x (i + 1) - x i) (y - x i) v))) →
    Function.Injective (fun i => ⟪x i, u₀⟫) →
    ∀ (A B R : List ℝ) (a e c : ℝ),
      List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = A ++ B ++ R →
      A.length + B.length = m → (A ++ B).head? = some a → (A ++ B).getLast? = some c →
      e ∈ A ++ B →
      ((A.Pairwise (· > ·) ∧ B.Pairwise (· < ·) ∧ ∀ y ∈ A ++ B, e ≤ y) ∨
       (A.Pairwise (· < ·) ∧ B.Pairwise (· > ·) ∧ ∀ y ∈ A ++ B, y ≤ e)) →
      ListCyclicUnimodal (chainSkeleton a e c ++ R) → IsRupert V

end Skeleton

/-- **Face-normal views (Lemma FN (iii), the half-plane case).** Look straight at a face, placed at
depth `0`: Its vertices form the polygon, and the remaining vertices have positive depth and project
into the closed polygon, some perhaps onto its boundary. If a single tilt `d` moves all of those
strictly inside, that is, it has `det(e_i, u, d) > 0` for every side `e_i` touched by a remaining
vertex, then `x` has a unimodal view. The tilted view has the planar face as its rim. With
`UnimodalViewIsRupert`, `x` is Rupert. -/
def FaceNormalHalfPlane : Prop :=
  ∀ (x : Fin 7 → ℝ³) (k : ℕ) [NeZero k] (lab : ZMod k → Fin 7) (u d : ℝ³),
    3 ≤ k → Function.Injective lab →
    (∀ i, ⟪x (lab i), u⟫ = 0) →
    (∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) u) →
    (∀ m, (∀ j, m ≠ lab j) → 0 < ⟪x m, u⟫ ∧
      ∀ i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u) →
    d ≠ 0 → ⟪d, u⟫ = 0 →
    (∀ i, (∃ m, (∀ j, m ≠ lab j) ∧
        det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u = 0) →
      0 < det3 (x (lab (i + 1)) - x (lab i)) u d) →
    HasUnimodalView x

/-! ## Symmetry of passages -/

/-- The passage of `K` through itself with inner rotation `Ri`, offset `o` and outer rotation `Ro`
has *margin* `δ`: The closed `δ`-ball about each point of the inner shadow lies in the outer shadow.
`HasClearance K δ` says that some passage has this property. -/
def PassageMargin (K : Finset ℝ³) (Ri : Matrix (Fin 3) (Fin 3) ℝ) (o : EuclideanSpace ℝ (Fin 2))
    (Ro : Matrix (Fin 3) (Fin 3) ℝ) (δ : ℝ) : Prop :=
  ∀ p ∈ convexHull ℝ (K : Set ℝ³),
    Metric.closedBall (o + proj_xy (Ri.toEuclideanLin p)) δ ⊆
      { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K : Set ℝ³) }

/-- **The symmetry group acts on passages, on both bodies separately.** Replacing the inner body by
its image under one symmetry of `K`, and the outer body by its image under another, gives a passage
with the same shadows, so the same margin. Symmetries can have determinant `-1`: The factor
`diag(1,1,det)` flips the axis perpendicular to the screen, which does not change the projection and
keeps the rotation proper. -/
def PassageSymmetry : Prop :=
  ∀ (K : Finset ℝ³) (g h : Matrix (Fin 3) (Fin 3) ℝ),
    g ∈ Matrix.orthogonalGroup (Fin 3) ℝ → h ∈ Matrix.orthogonalGroup (Fin 3) ℝ →
    (∀ v ∈ K, g.toEuclideanLin v ∈ K) → (∀ v ∈ K, h.toEuclideanLin v ∈ K) →
    ∀ Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ o : EuclideanSpace ℝ (Fin 2),
    ∀ Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ Ri' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ Ro' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
        Ri' = Matrix.diagonal ![1, 1, h.det] * Ri * h.transpose ∧
        Ro' = Matrix.diagonal ![1, 1, g.det] * Ro * g.transpose ∧
        { o + proj_xy (Ri'.toEuclideanLin p) | p ∈ convexHull ℝ (K : Set ℝ³) } =
          { o + proj_xy (Ri.toEuclideanLin p) | p ∈ convexHull ℝ (K : Set ℝ³) } ∧
        { proj_xy (Ro'.toEuclideanLin q) | q ∈ convexHull ℝ (K : Set ℝ³) } =
          { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K : Set ℝ³) } ∧
        ∀ δ : ℝ, PassageMargin K Ri' o Ro' δ ↔ PassageMargin K Ri o Ro δ

/-- **Mirror case: four passages from one.** If `K` has a symmetry `S` of determinant `-1`, such as
a mirror, a passage of margin `δ` gives three more of margin `δ` with the same offset: the flip
(inner body mirrored), the tip (outer body mirrored), and both. This is `PassageSymmetry` with `g`
and `h` in `{1, S}`. -/
def MirrorFourPassages : Prop :=
  ∀ (K : Finset ℝ³) (S : Matrix (Fin 3) (Fin 3) ℝ),
    S ∈ Matrix.orthogonalGroup (Fin 3) ℝ → S.det = -1 → (∀ v ∈ K, S.toEuclideanLin v ∈ K) →
    ∀ Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ o : EuclideanSpace ℝ (Fin 2),
    ∀ Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ Ri' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ Ro' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
        Ri' = Matrix.diagonal ![1, 1, -1] * Ri * S.transpose ∧
        Ro' = Matrix.diagonal ![1, 1, -1] * Ro * S.transpose ∧
        ∀ δ : ℝ, PassageMargin K Ri o Ro δ →
          PassageMargin K Ri' o Ro δ ∧ PassageMargin K Ri o Ro' δ ∧ PassageMargin K Ri' o Ro' δ

/-- The seven points have a quadrilateral face: `x 0, .., x 3` lie on a plane and
`x 4, x 5, x 6` strictly below it. -/
def HasQuadFace (x : Fin 7 → ℝ³) : Prop :=
  ∃ (n : ℝ³) (h : ℝ), n ≠ 0 ∧ (∀ i : Fin 7, i.val < 4 → ⟪n, x i⟫ = h) ∧
    (∀ i : Fin 7, 4 ≤ i.val → ⟪n, x i⟫ < h)

/-- **The failure of the converse is not confined to one shape.** There are seven points in `ℝ³`
with a quadrilateral face, and a tolerance, such that every nearby seven points that still have a
quadrilateral face (the same four kept coplanar, the other three strictly below) have all vertices
exposed, a first-order passage, and no unimodal view. Closeness is measured in each point
separately. So the failure of `ExistsFirstOrderPassageWithoutUnimodalView` holds on a whole
neighborhood inside the family of point sets with a planar quadrilateral. -/
def ExistsOpenFamilyWithoutUnimodalView : Prop :=
  ∃ (x₀ : Fin 7 → ℝ³) (ε : ℝ), 0 < ε ∧ HasQuadFace x₀ ∧
    ∀ x : Fin 7 → ℝ³, (∀ i, dist (x i) (x₀ i) < ε) → HasQuadFace x →
      (∀ i, ∃ c : ℝ³, ∀ j, j ≠ i → ⟪c, x j⟫ < ⟪c, x i⟫) ∧
      HasFirstOrderPassage (univ.image x) ∧ ¬ HasUnimodalView x

-- At the end of MinimalityExtra/NoUnimodalOpen.lean (namespace MinimalityExtra):
-- theorem existsOpenFamilyWithoutUnimodalView : ExistsOpenFamilyWithoutUnimodalView :=
--   NoUniO.open_family

/-- **The Septopert is a limit of Rupert shapes.** Take the seven points of the Septopert, with the
exact integer coordinates of `septopert.md` (the scale is `2^20` times that of the main
development). Every neighborhood of them contains seven different points that are Rupert. So the
Septopert is not in the interior of the set of Noperts. The nearby shapes move the last vertex in
the first coordinate. -/
def SeptopertIsLimitOfRupert : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : Fin 7 → ℝ³,
    (∀ i j, |x i j - (![!₂[-940638, 327651, 327651], !₂[327651, -940638, 327651],
      !₂[327651, 327651, -940638], !₂[703968, 47788, 47788], !₂[47788, 703968, 47788],
      !₂[47788, 47788, 703968], !₂[-514207, -514207, -514207]] : Fin 7 → ℝ³) i j| < ε) ∧
    x ≠ ![!₂[-940638, 327651, 327651], !₂[327651, -940638, 327651],
      !₂[327651, 327651, -940638], !₂[703968, 47788, 47788], !₂[47788, 703968, 47788],
      !₂[47788, 47788, 703968], !₂[-514207, -514207, -514207]] ∧
    IsRupert (Finset.univ.image x)

section EqualWidth

/-- **No passage with equal widths.** If the inner and outer shadows of a nonempty convex body have
the same width in some direction of the screen, then the inner shadow, however it is translated,
does not fit in the interior of the outer one. -/
def NoEqualWidthPassage : Prop :=
  ∀ vs : Finset ℝ³, vs.Nonempty →
  ∀ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∀ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ m : EuclideanSpace ℝ (Fin 2), ‖m‖ = 1 →
    Metric.diam { inner ℝ m (proj_xy (inner_rotation.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) } =
      Metric.diam { inner ℝ m (proj_xy (outer_rotation.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) } →
    ¬ ({ inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) })

/-- **No picture-symmetric passage.** Call a pair of poses picture-symmetric about a unit vector
`n` of space if both rotations send `n` into the screen, to the same direction up to sign, or both
send `n` to the view axis, so that both views are along `n`. For any nonempty convex body, such a
pair is never a passage. The body need not have a mirror with normal `n`. -/
def PictureSymmetricPoseNoPassage : Prop :=
  ∀ vs : Finset ℝ³, vs.Nonempty →
  ∀ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ inner_offset : EuclideanSpace ℝ (Fin 2),
  ∀ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
  ∀ n : ℝ³, ‖n‖ = 1 →
    ((outer_rotation.toEuclideanLin n 2 = 0 ∧ inner_rotation.toEuclideanLin n 2 = 0 ∧
        (proj_xy (inner_rotation.toEuclideanLin n) = proj_xy (outer_rotation.toEuclideanLin n) ∨
         proj_xy (inner_rotation.toEuclideanLin n) = - proj_xy (outer_rotation.toEuclideanLin n))) ∨
     ((outer_rotation.toEuclideanLin n 2) ^ 2 = 1 ∧ (inner_rotation.toEuclideanLin n 2) ^ 2 = 1)) →
    ¬ ({ inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) })

end EqualWidth

end MinimalityExtra
