module

public import SmallRupert.Prism

@[expose] public section

/-!
# L8 framework: tilting off a degenerate view (frame-free)

Everything is stated with the triple product `det3 a b c = ⟪a × b, c⟫` at a
view `w` (no rotation needed): for a rotation `R` with `R w = r e_z`, `r > 0`,
`cross2 (P R a) (P R b) = det3 a b w / r`.

* `isRupert_of_tiltCert`: Lemma 1 at the view `w` with *local certificates*:
  every point is either a corner whose velocity points strictly into the
  angle formed with two other points, or lies strictly inside a triangle of
  three other points.
* `eventually_pos_affine`: `A + εB > 0` for small `ε > 0` when `A > 0`, or
  `A = 0` and `B > 0` (the determinant form of Lemma 8.0 in L8_REVIEW §1).
* `eventually_tilted_cycle` (Lemma 8.0, instance-wise): the sign facts
  `D0 ≥ 0`, `D0 = 0 ⇒ D1 > 0` for a predicted cycle give that cycle as the
  silhouette at `u0 + εv` for all small `ε > 0`, with (G1).
* `isRupert_of_tilted_unimodal` (Corollary 8.0′): the same, with an open
  condition on the limit depths that forces unimodality.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The triple product `det (a, b, c) = ⟪a × b, c⟫`. -/
noncomputable def det3 (a b c : ℝ³) : ℝ := ⟪cross a b, c⟫

/-- A local certificate for Lemma 1 at `x`, view `w`, motion `(ω, τ)`:
either `x` is a corner between `y₀` (before) and `y₁` (after) and its
velocity points strictly into the angle `y₀ x y₁`, or `x` lies strictly inside
the triangle `abc`. -/
def TiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, 0 < det3 (y₁ - x) (y₀ - x) w ∧
      0 < det3 (y₁ - x) (cross ω x + τ) w ∧ 0 < det3 (x - y₀) (cross ω x + τ) w) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
      0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w)

/-- **Lemma 1, frame-free, with local certificates.** -/
theorem isRupert_of_tiltCert (V : Finset ℝ³) (w : ℝ³) (hw : w ≠ 0) (ω τ : ℝ³)
    (h : ∀ x ∈ V, TiltCert V w ω τ x) : IsRupert V := by
  sorry

/-- The sign facts of Lemma 8.0 for one determinant test. -/
def TiltSign (a b u₀ v : ℝ³) : Prop :=
  0 < det3 a b u₀ ∨ (det3 a b u₀ = 0 ∧ 0 < det3 a b v)

theorem eventually_pos_affine {A B : ℝ} (h : 0 < A ∨ (A = 0 ∧ 0 < B)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A + ε * B := by
  sorry

/-- **Lemma 8.0, instance-wise (determinant form).**  If the predicted cycle
`x` passes every determinant test in the limit (`D0 ≥ 0`, and `D1 > 0` when
`D0 = 0`), then for all small `ε > 0` it is the silhouette at the view
`u₀ + εv`: strictly convex, counterclockwise, with every other point of `V`
strictly inside (in particular (G1)). -/
theorem eventually_tilted_cycle (V : Finset ℝ³) (u₀ v : ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ R ∈ SO3, ∀ r : ℝ, 0 < r → R.toEuclideanLin (u₀ + ε • v) = r • ez →
      IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) ∧
      ∀ y ∈ V, (∀ j, y ≠ x j) → proj_xy (R.toEuclideanLin y) ∈
        interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) := by
  sorry

/-- **Corollary 8.0′ (robust unimodality).**  In Lemma 8.0, if the limit depths
`⟪x i, u₀⟫` satisfy an open, scale-invariant condition `Q` that forces cyclic
unimodality once the depths are distinct, then `V` is Rupert. -/
theorem isRupert_of_tilted_unimodal (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQ : Q fun i => ⟪x i, u₀⟫)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  sorry

end SmallRupert

end
