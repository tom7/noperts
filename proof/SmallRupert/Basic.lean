module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Topology
public import Noperthedron.Rupert.Basic

@[expose] public section

/-!
# Small Rupert polyhedra: shared definitions

Setting of `notes/LEMMAS.md` §0, in the conventions of `IsRupert`
(`Noperthedron/MainTheorem.lean`): the screen is the xy-plane, a point
`x : ℝ³` has screen position `proj_xy x` and depth `x 2`, and the *standard
view* is the direction `ez = e₂` (LEMMAS.md's `e_z`).  A general view `u` is
reduced to the standard one by a rotation (`exists_rotation_to_ez`,
`isRupert_of_isRupert_image_rotation`).

Main definitions:
* `rot90` — LEMMAS.md's `J`, rotation of the screen by +90°.
* `crossMatrix ω` — `[ω]×`, the matrix of `x ↦ ω × x`.
* `screenVel ω τ x` — the screen velocity `ν(x) = P(ω × x + τ)` of the
  first-order motion `(ω, τ)`.
* `IsInwardAt S p d` — `d` points strictly into `S` at `p`, i.e.
  `d ∈ int T_S(p)` for a convex polygon `S` (`isInwardAt_iff_forall_normal`).
* `IsDoubleNormalDir F u` — `u` is the direction of a double normal of `F`
  (LEMMAS.md L3).
* `innerShadow`, `outerShadow` — the two shadows of `IsRupert`, so that
  `isRupert_iff_shadows` is `Iff.rfl`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The standard view direction `e₂` (LEMMAS.md's `e_z`): `proj_xy` forgets it. -/
noncomputable def ez : ℝ³ := EuclideanSpace.single 2 1

/-- LEMMAS.md's `J`: rotation of the screen by +90°, `J (x, y) = (-y, x)`. -/
noncomputable def rot90 (p : ℝ²) : ℝ² := !₂[-p 1, p 0]

/-- `[ω]×`, the skew matrix of the linear map `x ↦ ω × x`. -/
def crossMatrix (ω : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω 2, ω 1;
     ω 2, 0, -ω 0;
     -ω 1, ω 0, 0]

/-- The screen velocity `ν(x) = P(ω × x + τ)` of the first-order motion
`(ω, τ)` at the point `x`, in the standard view (LEMMAS.md §0). -/
noncomputable def screenVel (ω τ x : ℝ³) : ℝ² :=
  proj_xy ((crossMatrix ω).toEuclideanLin x + τ)

/-- `d` points strictly into `S` at `p`: some positive step along `d` lands in
the interior of `S`.  For a closed convex `S` with nonempty interior and
`p ∈ S` this is `d ∈ int T_S(p)`, i.e. `n ⬝ d < 0` for every nonzero outward
normal `n` at `p` (`isInwardAt_iff_forall_normal`); in particular it holds for
every `d` when `p ∈ interior S`. -/
def IsInwardAt {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (S : Set E) (p d : E) : Prop :=
  ∃ ε > (0 : ℝ), p + ε • d ∈ interior S

/-- `u` is a *double-normal direction* of `F` (LEMMAS.md L3): there is a chord
`[a, b]`, `a ≠ b`, parallel to `u`, with `b - a ∈ N_F(b)` and `a - b ∈ N_F(a)`
(the lines through `a` and `b` perpendicular to `ab` both support `F`).  The
sign of `u` is irrelevant, and `u ≠ 0` is forced. -/
def IsDoubleNormalDir {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Set E) (u : E) : Prop :=
  ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ (∃ t : ℝ, b - a = t • u) ∧
    (∀ q ∈ F, ⟪b - a, q - b⟫ ≤ 0) ∧ (∀ q ∈ F, ⟪a - b, q - a⟫ ≤ 0)

/-- The inner shadow of `IsRupert`: `o + P(R p)` for `p ∈ S`. -/
def innerShadow (R : Matrix (Fin 3) (Fin 3) ℝ) (o : ℝ²) (S : Set ℝ³) : Set ℝ² :=
  { o + proj_xy (R.toEuclideanLin p) | p ∈ S }

/-- The outer shadow of `IsRupert`: `P(R p)` for `p ∈ S`. -/
def outerShadow (R : Matrix (Fin 3) (Fin 3) ℝ) (S : Set ℝ³) : Set ℝ² :=
  { proj_xy (R.toEuclideanLin p) | p ∈ S }

/-- `IsRupert`, restated with `innerShadow`/`outerShadow`. -/
theorem isRupert_iff_shadows (V : Finset ℝ³) :
    IsRupert V ↔ ∃ R₁ ∈ SO3, ∃ o : ℝ², ∃ R₂ ∈ SO3,
      innerShadow R₁ o (convexHull ℝ (V : Set ℝ³)) ⊆
        interior (outerShadow R₂ (convexHull ℝ (V : Set ℝ³))) :=
  Iff.rfl

/-- `IsRupert V` depends only on `convexHull ℝ V`. -/
theorem isRupert_congr_hull {V V' : Finset ℝ³}
    (h : convexHull ℝ (V : Set ℝ³) = convexHull ℝ (V' : Set ℝ³)) :
    IsRupert V ↔ IsRupert V' := by
  simp only [isRupert_iff_shadows, h]

/-- The standard-view outer shadow is `proj_xy '' S`. -/
theorem outerShadow_one (S : Set ℝ³) : outerShadow 1 S = proj_xy '' S := by
  ext x; simp [outerShadow]

/-- Rupertness is invariant under rotating the vertex set.  (Proved as
`_root_.isRupert_image_rotation` in
`Noperthedron/PentagonalHexecontahedron/IcoInstance.lean`, applied to `Qᵀ`;
that file is too heavy to import here, so the proof is to be moved to a light
module.) -/
theorem isRupert_of_isRupert_image_rotation (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ SO3)
    (V : Finset ℝ³) (h : IsRupert (V.image Q.toEuclideanLin)) : IsRupert V := by
  sorry

/-- Every nonzero direction is taken to the standard view axis by some
rotation. -/
theorem exists_rotation_to_ez (u : ℝ³) (hu : u ≠ 0) :
    ∃ R ∈ SO3, ∃ r : ℝ, r ≠ 0 ∧ R.toEuclideanLin u = r • ez := by
  sorry

/-- `IsInwardAt` is the interior of the tangent cone, described by normals:
for a convex set with nonempty interior in a finite-dimensional space and
`p ∈ closure S`, `d` is inward at `p` iff `⟪n, d⟫ < 0` for every nonzero
`n ∈ N_S(p)`. (For a polygon `N_S(p)` is spanned by the outward normals of
the one or two edges at `p`, which is LEMMAS.md's `int T_S(p)`.) -/
theorem isInwardAt_iff_forall_normal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) {p : E} (hp : p ∈ closure S) (d : E) :
    IsInwardAt S p d ↔ ∀ n : E, n ≠ 0 → (∀ q ∈ S, ⟪n, q - p⟫ ≤ 0) → ⟪n, d⟫ < 0 := by
  sorry

/-- Once some step along `d` enters the interior, all smaller steps do. -/
theorem IsInwardAt.eventually {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {S : Set E} (hS : Convex ℝ S) {p d : E}
    (hp : p ∈ closure S) (h : IsInwardAt S p d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • d ∈ interior S := by
  sorry

/-- Every point of the interior is inward in every direction. -/
theorem isInwardAt_of_mem_interior {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {S : Set E} {p : E}
    (hp : p ∈ interior S) (d : E) : IsInwardAt S p d := by
  sorry

/-- `IsDoubleNormalDir` is invariant under linear isometries. -/
theorem isDoubleNormalDir_image_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E ≃ₗᵢ[ℝ] E) (F : Set E) (u : E) :
    IsDoubleNormalDir (f '' F) (f u) ↔ IsDoubleNormalDir F u := by
  sorry

end SmallRupert

end
