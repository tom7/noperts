module

public import Minimality.FirstOrder

@[expose] public section

/-!
# A rotation axis threading the quarter-turned inward wedges

FEWER-FACES-PROOFS.md, Proposition 8.7 (line-transversal form of first-order
freedom), the direction used to prove Rupertness. A small rotation, in the sense
`σ`, about the non-horizontal line `L = {(c₀ + z c₁, z)}` moves a point
`x = (p, z)` on the screen by `σ J (p − c₀ − z c₁)` (`J` the quarter turn
`rot90`): it turns about the point where `L` meets the point's depth level
(`screenVel_axis`). If this velocity points strictly into the shadow at every
point of `V`, i.e. if `L` meets each vertex's depth level inside the vertex's
inward cone turned by a quarter turn, `V` is Rupert (`isRupert_of_axis`, via
Lemma 1, `isRupert_of_firstOrderInward`).
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- The rotation vector `σ (c₁, 1)` of the axis `{(c₀ + z c₁, z)}`. -/
noncomputable def axisOmega (σ : ℝ) (c₁ : ℝ²) : ℝ³ := !₂[σ * c₁ 0, σ * c₁ 1, σ]

/-- The translation that makes the rotation `axisOmega σ c₁` fix the point
`(c₀, 0)` of the axis: `τ = −ω × (c₀, 0)`. -/
noncomputable def axisTau (σ : ℝ) (c₀ : ℝ²) : ℝ³ := !₂[σ * c₀ 1, -(σ * c₀ 0), 0]

/-- **The screen motion of a rotation about a line.** -/
theorem screenVel_axis (σ : ℝ) (c₀ c₁ : ℝ²) (x : ℝ³) :
    screenVel (axisOmega σ c₁) (axisTau σ c₀) x = σ • rot90 (proj_xy x - c₀ - x 2 • c₁) := by
  ext i; fin_cases i <;>
    simp [screenVel, crossMatrix, axisOmega, axisTau, rot90, proj_xy, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- **Proposition 8.7, sufficient direction** (standard view): if a small rotation
about some non-horizontal line `{(c₀ + z c₁, z)}` moves every point of `V` strictly
into the shadow, then `V` is Rupert. -/
theorem isRupert_of_axis (V : Finset ℝ³) (σ : ℝ) (c₀ c₁ : ℝ²)
    (h : ∀ v ∈ V, IsInwardAt (proj_xy '' convexHull ℝ (V : Set ℝ³)) (proj_xy v)
      (σ • rot90 (proj_xy v - c₀ - v 2 • c₁))) :
    IsRupert V :=
  isRupert_of_firstOrderInward V (axisOmega σ c₁) (axisTau σ c₀) fun v hv => by
    rw [screenVel_axis]; exact h v hv

/-- **Proposition 8.7, sufficient direction**, at the view of a rotation `Q`. -/
theorem isRupert_of_axis_image (V : Finset ℝ³) (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ SO3)
    (σ : ℝ) (c₀ c₁ : ℝ²)
    (h : ∀ v ∈ V.image Q.toEuclideanLin,
      IsInwardAt (proj_xy '' convexHull ℝ ((V.image Q.toEuclideanLin : Finset ℝ³) : Set ℝ³))
        (proj_xy v) (σ • rot90 (proj_xy v - c₀ - v 2 • c₁))) :
    IsRupert V :=
  isRupert_of_isRupert_image_rotation Q hQ V (isRupert_of_axis _ σ c₀ c₁ h)

end Minimality

end
