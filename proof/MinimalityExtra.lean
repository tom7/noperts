module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Basic

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

end MinimalityExtra
