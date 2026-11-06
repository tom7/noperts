module

public import Mathlib
public import MinimalityExtra

/-!
# Sandwich and cylinder: monotonicity of passages
-/

@[expose] public section

open scoped Classical

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra

/-- The shadow map `p ↦ proj_xy (R p)` as a linear map (local copy of `RupertStab.gL`). -/
noncomputable def shadowL (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ³ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := proj_xy (R.toEuclideanLin p)
  map_add' x y := by ext i; fin_cases i <;> simp [proj_xy]
  map_smul' c x := by ext i; fin_cases i <;> simp [proj_xy]

theorem rupertSandwich : RupertSandwich := by
  intro W K L hWK hKL hpass
  obtain ⟨Ri, hRi, o, Ro, hRo, h⟩ := hpass
  refine ⟨Ri, hRi, o, Ro, hRo, ?_⟩
  dsimp only at h ⊢
  rintro x ⟨p, hp, rfl⟩
  have hpL : p ∈ convexHull ℝ (L : Set ℝ³) := hKL hp
  have hx := h ⟨p, hpL, rfl⟩
  have hsub : { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (W : Set ℝ³) } ⊆
      { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K : Set ℝ³) } := by
    rintro z ⟨q, hq, rfl⟩
    exact ⟨q, hWK hq, rfl⟩
  exact interior_mono hsub hx

theorem cylinderExtension : CylinderExtension := by
  intro K₀ Ri Ro hRi hRo o h y hy
  set O := { proj_xy (Ro.toEuclideanLin q) | q ∈ convexHull ℝ (K₀ : Set ℝ³) } with hO
  have hOconv : Convex ℝ O := by
    have e : O = (shadowL Ro) '' convexHull ℝ (K₀ : Set ℝ³) := rfl
    rw [e]
    exact (convex_convexHull ℝ _).linear_image (shadowL Ro)
  have hC : Convex ℝ { q : ℝ³ | o + proj_xy (Ri.toEuclideanLin q) ∈ interior O } := by
    have e : { q : ℝ³ | o + proj_xy (Ri.toEuclideanLin q) ∈ interior O } =
        (shadowL Ri) ⁻¹' ((fun x => o + x) ⁻¹' interior O) := rfl
    rw [e]
    exact ((hOconv.interior).translate_preimage_right o).linear_preimage (shadowL Ri)
  have hK : ∀ v ∈ K₀, o + proj_xy (Ri.toEuclideanLin v) ∈ interior O := fun v hv =>
    h ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.2 hv), rfl⟩
  have hins : ((insert y K₀ : Finset ℝ³) : Set ℝ³) ⊆
      { q : ℝ³ | o + proj_xy (Ri.toEuclideanLin q) ∈ interior O } := by
    intro z hz
    rw [Finset.coe_insert, Set.mem_insert_iff] at hz
    rcases hz with rfl | hz
    · exact hy
    · exact hK z (Finset.mem_coe.1 hz)
  have hconvH := convexHull_min hins hC
  refine ⟨Ri, hRi, o, Ro, hRo, ?_⟩
  dsimp only
  have hO' : O ⊆ { proj_xy (Ro.toEuclideanLin q) |
      q ∈ convexHull ℝ ((insert y K₀ : Finset ℝ³) : Set ℝ³) } := by
    rintro z ⟨q, hq, rfl⟩
    exact ⟨q, convexHull_mono (Finset.coe_subset.2 (Finset.subset_insert _ _)) hq, rfl⟩
  rintro x ⟨p, hp, rfl⟩
  exact interior_mono hO' (hconvH hp)

#print axioms rupertSandwich
#print axioms cylinderExtension

end MinimalityExtra
