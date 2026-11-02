module

public import Minimality.Type16VC

@[expose] public section


/-! # H16/V: leaves L1, L7 with only the depth-pattern hypothesis `hnp` -/
set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

/-- The only depth pattern of the pentagon `(6,3,5,2,4)` that the leaf cannot exclude: peaks at `3` and `4`. -/
def H16VPat1 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 6, x 6 - x 0⟫ < ⟪x 3, x 6 - x 0⟫ ∧ ⟪x 5, x 6 - x 0⟫ < ⟪x 3, x 6 - x 0⟫ ∧
    ⟪x 2, x 6 - x 0⟫ < ⟪x 4, x 6 - x 0⟫ ∧ ⟪x 6, x 6 - x 0⟫ < ⟪x 4, x 6 - x 0⟫
/-- Same for the sigma-image `(0,3,5,1,4)`, `u = x0 - x6`. -/
def H16VPat7 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 0, x 0 - x 6⟫ < ⟪x 3, x 0 - x 6⟫ ∧ ⟪x 5, x 0 - x 6⟫ < ⟪x 3, x 0 - x 6⟫ ∧
    ⟪x 1, x 0 - x 6⟫ < ⟪x 4, x 0 - x 6⟫ ∧ ⟪x 0, x 0 - x 6⟫ < ⟪x 4, x 0 - x 6⟫

theorem h16v_ev1_L1' (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : 0 < T.ff 7 (x 6) - T.ff 7 (x 0))
    (hnp : ¬ H16VPat1 x)
    (d63 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d65 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d62 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d64 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d32 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d34 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d52 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d54 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d24 : ⟪x 2, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) :
    HasLexCell (univ.image x) :=
  ⟨x 6 - x 0, u06_ne T, h16v_ev1_L1p_cell T hζ hF hH hnp d63 d65 d62 d64 d32 d34 d52 d54 d24⟩

theorem h16v_ev1_L7' (T : Type16 x) (hζ : 0 < ⟪x 5 - x 3, x 6 - x 0⟫)
    (hF : T.ff 5 (x 6) - T.ff 5 (x 0) < 0) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (hnp : ¬ H16VPat7 x)
    (d63 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 3, x 0 - x 6⟫) (d65 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 5, x 0 - x 6⟫)
    (d62 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d64 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d32 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d34 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d52 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d54 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d24 : ⟪x 1, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) :
    HasLexCell (univ.image x) := by
  refine hasLexCell_of_sigma (h16v_ev1_L1' T.sigma ?_ ?_ ?_ hnp d63 d65 d62 d64 d32 d34 d52 d54 d24)
  · show ⟪x 5 - x 3, x 0 - x 6⟫ < 0
    have : ⟪x 5 - x 3, x 0 - x 6⟫ = -⟪x 5 - x 3, x 6 - x 0⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  · show 0 < T.ff 7 (x 0) - T.ff 7 (x 6)
    linarith
  · show 0 < T.ff 5 (x 0) - T.ff 5 (x 6)
    linarith

end H16U
end Minimality
