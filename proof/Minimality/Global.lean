module

public import Minimality.Forces
public import Minimality.Planes

@[expose] public section

/-!
# Global passages from vertex certificates

Every other Rupert criterion in `Minimality/` is local (a first-order motion
from the identity pose, or a crossing). This file is the generic global
form: a pose `(R₁, o, R₂)` is a passage as soon as every rotated, translated
inner vertex is a combination of the outer projected vertices with all
weights positive. It is the exact (LP) formulation of a passage at a fixed
pose, with no convex hull computed: anchored poses such as the corner
placement (FEWER-FACES.md, "Anchored global passages") produce such weights.
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- The outer shadow of a hull is the hull of the projected vertices. -/
theorem outerShadow_convexHull (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    outerShadow R (convexHull ℝ (V : Set ℝ³)) =
      convexHull ℝ ((V.image (fun w => proj_xy (R.toEuclideanLin w)) : Finset ℝ²) : Set ℝ²) := by
  classical
  set g : ℝ³ →ₗ[ℝ] ℝ² := projL ∘ₗ R.toEuclideanLin
  have e : outerShadow R (convexHull ℝ (V : Set ℝ³)) = g '' convexHull ℝ (V : Set ℝ³) := by
    ext x; simp [outerShadow, g, projL_apply]
  rw [e, LinearMap.image_convexHull, Finset.coe_image]
  rfl

/-- **Global passage, barycentric form.** If every inner vertex
`o + P(R₁ v)` is a combination of the outer vertices `P(R₂ w)` with all
weights positive, `V` is Rupert. -/
theorem isRupert_of_pos_combinations (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    {R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ} (hR₁ : R₁ ∈ SO3) (hR₂ : R₂ ∈ SO3) (o : ℝ²)
    (h : ∀ v ∈ V, ∃ μ : ℝ³ → ℝ, (∀ w ∈ V, 0 < μ w) ∧ ∑ w ∈ V, μ w = 1 ∧
      o + proj_xy (R₁.toEuclideanLin v) = ∑ w ∈ V, μ w • proj_xy (R₂.toEuclideanLin w)) :
    IsRupert V := by
  classical
  set φ : ℝ³ → ℝ² := fun w => proj_xy (R₂.toEuclideanLin w)
  set I := interior (convexHull ℝ ((V.image φ : Finset ℝ²) : Set ℝ²))
  have hint : I.Nonempty := by
    have h0 := interior_proj_convexHull_nonempty V hR₂ hsol
    have e : proj_xy '' convexHull ℝ ((V.image R₂.toEuclideanLin : Finset ℝ³) : Set ℝ³) =
        convexHull ℝ ((V.image φ : Finset ℝ²) : Set ℝ²) := by
      have : proj_xy '' convexHull ℝ ((V.image R₂.toEuclideanLin : Finset ℝ³) : Set ℝ³) =
          projL '' convexHull ℝ ((V.image R₂.toEuclideanLin : Finset ℝ³) : Set ℝ³) := rfl
      rw [this, LinearMap.image_convexHull, Finset.coe_image, Finset.coe_image, Set.image_image]
      rfl
    rwa [e] at h0
  have hvert : ∀ v ∈ V, o + proj_xy (R₁.toEuclideanLin v) ∈ I := by
    intro v hv
    obtain ⟨μ, hμ, hμ1, hμv⟩ := h v hv
    rw [hμv]
    exact sum_smul_mem_interior_convexHull_image V φ μ hμ hμ1 hint
  have hconv : Convex ℝ {p : ℝ³ | o + proj_xy (R₁.toEuclideanLin p) ∈ I} := by
    intro p hp q hq a b ha hb hab
    have e : o + proj_xy (R₁.toEuclideanLin (a • p + b • q)) =
        a • (o + proj_xy (R₁.toEuclideanLin p)) + b • (o + proj_xy (R₁.toEuclideanLin q)) := by
      rw [map_add, map_smul, map_smul, proj_xy_add', proj_xy_smul', proj_xy_smul']
      linear_combination (norm := module) (-hab) • o
    show o + proj_xy (R₁.toEuclideanLin (a • p + b • q)) ∈ I
    rw [e]
    exact (convex_convexHull ℝ _).interior hp hq ha hb hab
  have hhull : convexHull ℝ (V : Set ℝ³) ⊆ {p : ℝ³ | o + proj_xy (R₁.toEuclideanLin p) ∈ I} :=
    convexHull_min (fun v hv => hvert v hv) hconv
  refine (isRupert_iff_shadows V).mpr ⟨R₁, hR₁, o, R₂, hR₂, ?_⟩
  rw [outerShadow_convexHull]
  rintro x ⟨p, hp, rfl⟩
  exact hhull hp

end Minimality

end
