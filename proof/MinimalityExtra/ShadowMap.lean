module

public import Mathlib
public import MainTheorem

/-!
# The shadow map as a linear map

Light file (imports only `MainTheorem`): `RupertStab.gL R` is `p ↦ proj_xy (R p)`, shared by
`RupertStable` and `Sandwich`.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace RupertStab

/-- The shadow map `p ↦ proj_xy (R p)` as a linear map. -/
noncomputable def gL (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ³ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := proj_xy (R.toEuclideanLin p)
  map_add' x y := by ext i; fin_cases i <;> simp [proj_xy]
  map_smul' c x := by ext i; fin_cases i <;> simp [proj_xy]

theorem gL_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³) :
    gL R p = proj_xy (R.toEuclideanLin p) := rfl

end RupertStab
