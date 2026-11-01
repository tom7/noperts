module

public import Minimality.Type16UC

@[expose] public section


/-!
# U1: TT leaves, `HasLexCell` / `IsRupert` forms and the σ-images
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

theorem image_sigma16 (x : Fin 7 → ℝ³) : univ.image (x ∘ sigma16) = univ.image x := by
  ext y
  simp only [mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    have : ∀ i : Fin 7, ∃ j, sigma16 j = i := by decide
    obtain ⟨j, rfl⟩ := this i
    exact ⟨j, rfl⟩

/-- Transfer of a `HasLexCell` along σ. -/
theorem hasLexCell_of_sigma (h : HasLexCell (univ.image (x ∘ sigma16))) : HasLexCell (univ.image x) := by
  rwa [image_sigma16] at h

/-- **TT leaf `LBE (6,1,4)`**: `φE(1,5) > 0`. -/
theorem h16u_tt_LBE (T : Type16 x) (h : T.ff 4 (x 1) < T.ff 4 (x 5))
    (hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 1, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 6 1 4) :
    HasLexCell (univ.image x) := by
  obtain ⟨r, hr, h1, h2⟩ := exists_kernel2 (T.fN 1) (T.fN 4)
  exact ⟨r, hr, h16u_tt_LBE_cell T h hr h1 h2 (hdep r hr h1 h2)⟩

theorem h16u_tt_LBE_isRupert (T : Type16 x) (h : T.ff 4 (x 1) < T.ff 4 (x 5))
    (hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 1, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 6 1 4) :
    IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_tt_LBE T h hdep)

/-- **TT leaf `LAE (0,2,4)`** (σ-image of `LBE`): `φE(2,5) > 0`. -/
theorem h16u_tt_LAE (T : Type16 x) (h : T.ff 4 (x 2) < T.ff 4 (x 5))
    (hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 0, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 0 2 4) :
    HasLexCell (univ.image x) :=
  hasLexCell_of_sigma (h16u_tt_LBE T.sigma h (fun r hr h1 h2 => hdep r hr h1 h2))

theorem h16u_tt_LAE_isRupert (T : Type16 x) (h : T.ff 4 (x 2) < T.ff 4 (x 5))
    (hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 0, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 0 2 4) :
    IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_tt_LAE T h hdep)

end H16U
end Minimality
