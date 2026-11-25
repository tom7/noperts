module

public import MinimalityExtra.DepthSeparated
public import Minimality.EdgePlane

/-!
# The Edge-Plane Lemma

The proofs live in `Minimality.EdgePlane` (namespace `Minimality.Split`), so that the minimality proof can
use them; this file restates them under their old names.

Rotations whose axis lies in the plane through a rim edge normal to its support plane: freedom of
this form is the separation of two point sets in a plane. The depth-separated view theorem
(`DepthSeparatedViewIsFree`) is its steep case.
-/

@[expose] public section

namespace MinimalityExtra

open scoped RealInnerProductSpace
open Finset

/-! ## The Edge-Plane Lemma: axis in the plane of an edge -/

/-- **Edge-Plane Lemma, explicit motion.**  The rows are affine in `(α, μ)`: each row asks the
line `ρ = α + μ z` to pass on one side of a point of the `(z, ρ)` plane.  Geometrically the axis
lies in the plane through the edge `a` normal to its support plane. -/
theorem exists_motion_of_edgePlane {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a : ZMod k) (s α μ : ℝ) (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w :=
  Minimality.Split.exists_motion_of_edgePlane hk x w lab hinj hrim a s α μ hD hrows

/-- **Edge-Plane Lemma.** -/
theorem freeAt_of_edgePlane {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a : ZMod k) (s α μ : ℝ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    FreeAt (univ.image x) w :=
  Minimality.Split.freeAt_of_edgePlane hk x w lab hinj hrim hhid a s α μ hD hrows

/-- **Vertex form (the Dip Test).**  A candidate `(α, μ, s)` with two rows exactly tight, the two
tight rows independent, and every other row strictly positive.  Rows are homogeneous in
`(α, μ, s)`, so the tight rows are opened by adding a small direction. -/
theorem freeAt_of_edgePlane_vertex {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a : ZMod k) (s α μ : ℝ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0) (i₁ j₁ i₂ j₂ : ZMod k)
    (hdet : det3 (x (lab (i₁ + 1)) - x (lab i₁)) (x (lab (a + 1)) - x (lab a)) w ≠ 0 ∧
      det3 (x (lab (i₂ + 1)) - x (lab i₂)) (x (lab (a + 1)) - x (lab a)) w ≠ 0 ∧
      ⟪x (lab j₁) - x (lab a), w⟫ ≠ ⟪x (lab j₂) - x (lab a), w⟫)
    (ht₁ : (α + μ * ⟪x (lab j₁) - x (lab a), w⟫) *
        det3 (x (lab (i₁ + 1)) - x (lab i₁)) (x (lab (a + 1)) - x (lab a)) w +
      s * edgePlaneSpin (fun i => x (lab i)) w a i₁ j₁ = 0)
    (ht₂ : (α + μ * ⟪x (lab j₂) - x (lab a), w⟫) *
        det3 (x (lab (i₂ + 1)) - x (lab i₂)) (x (lab (a + 1)) - x (lab a)) w +
      s * edgePlaneSpin (fun i => x (lab i)) w a i₂ j₂ = 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → (i, j) ≠ (i₁, j₁) → (i, j) ≠ (i₂, j₂) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    FreeAt (univ.image x) w :=
  Minimality.Split.freeAt_of_edgePlane_vertex hk x w lab hinj hrim hhid a s α μ hD i₁ j₁ i₂ j₂ hdet ht₁ ht₂ hrows

theorem edgePlaneFreedom : EdgePlaneFreedom :=
  fun _ _ _ hk x w lab hinj hrim hhid a s α μ hD hrows =>
    freeAt_of_edgePlane hk x w lab hinj hrim hhid a s α μ hD hrows

#print axioms edgePlaneFreedom
#print axioms freeAt_of_edgePlane_vertex

end MinimalityExtra
