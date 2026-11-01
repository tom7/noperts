module

public import Minimality.Type16UL
public import Minimality.Type16UH

@[expose] public section


/-!
# U1: EV1 leaf `LDE (6,3,5,2,4)` as `HasLexCell` / `IsRupert`, and its σ-image `LDE (0,3,5,1,4)`
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

/-- **Leaf `LDE (6,3,5,2,4)`** (EV1 at `s06`, `e = 6`, pentagon): `ζ < 0`, `φF(0,6) > 0`, `φH(0,6) > 0`.
Extra hypotheses (not implied by `Type16`): `hG : fE(5) < fE(3)` and `hX : z0 ≤ z3` along `u = x6 - x0`. -/
theorem h16u_ev1_L1 (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : 0 < T.ff 7 (x 6) - T.ff 7 (x 0))
    (hG : T.ff 4 (x 5) < T.ff 4 (x 3)) (hX : ⟪x 0, x 6 - x 0⟫ ≤ ⟪x 3, x 6 - x 0⟫)
    (d63 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d65 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d62 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d64 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d32 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d34 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d52 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d54 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d24 : ⟪x 2, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) :
    HasLexCell (univ.image x) :=
  ⟨x 6 - x 0, u06_ne T, h16u_ev1_L1_cell T hζ hF hH hG hX d63 d65 d62 d64 d32 d34 d52 d54 d24⟩

theorem h16u_ev1_L1_isRupert (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : 0 < T.ff 7 (x 6) - T.ff 7 (x 0))
    (hG : T.ff 4 (x 5) < T.ff 4 (x 3)) (hX : ⟪x 0, x 6 - x 0⟫ ≤ ⟪x 3, x 6 - x 0⟫)
    (d63 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d65 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d62 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d64 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d32 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d34 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d52 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d54 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d24 : ⟪x 2, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_ev1_L1 T hζ hF hH hG hX d63 d65 d62 d64 d32 d34 d52 d54 d24)

/-- **Leaf `LDE (0,3,5,1,4)`** (σ-image; EV1 at `s06`, `e = 0`, pentagon): `ζ > 0`, `φH(0,6) < 0`, `φF(0,6) < 0`.
Extra hypotheses: `hG : fE(5) < fE(3)` and `hX : ⟪x6, u⟫ ≤ ⟪x3, u⟫` along `u = x0 - x6`. -/
theorem h16u_ev1_L7 (T : Type16 x) (hζ : 0 < ⟪x 5 - x 3, x 6 - x 0⟫)
    (hF : T.ff 5 (x 6) - T.ff 5 (x 0) < 0) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (hG : T.ff 4 (x 5) < T.ff 4 (x 3)) (hX : ⟪x 6, x 0 - x 6⟫ ≤ ⟪x 3, x 0 - x 6⟫)
    (d63 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 3, x 0 - x 6⟫) (d65 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 5, x 0 - x 6⟫)
    (d62 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d64 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d32 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d34 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d52 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d54 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d24 : ⟪x 1, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) :
    HasLexCell (univ.image x) := by
  refine hasLexCell_of_sigma (h16u_ev1_L1 T.sigma ?_ ?_ ?_ hG hX d63 d65 d62 d64 d32 d34 d52 d54 d24)
  · show ⟪x 5 - x 3, x 0 - x 6⟫ < 0
    have : ⟪x 5 - x 3, x 0 - x 6⟫ = -⟪x 5 - x 3, x 6 - x 0⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  · show 0 < T.ff 7 (x 0) - T.ff 7 (x 6)
    linarith
  · show 0 < T.ff 5 (x 0) - T.ff 5 (x 6)
    linarith

theorem h16u_ev1_L7_isRupert (T : Type16 x) (hζ : 0 < ⟪x 5 - x 3, x 6 - x 0⟫)
    (hF : T.ff 5 (x 6) - T.ff 5 (x 0) < 0) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (hG : T.ff 4 (x 5) < T.ff 4 (x 3)) (hX : ⟪x 6, x 0 - x 6⟫ ≤ ⟪x 3, x 0 - x 6⟫)
    (d63 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 3, x 0 - x 6⟫) (d65 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 5, x 0 - x 6⟫)
    (d62 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d64 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d32 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d34 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d52 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 1, x 0 - x 6⟫) (d54 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d24 : ⟪x 1, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_ev1_L7 T hζ hF hH hG hX d63 d65 d62 d64 d32 d34 d52 d54 d24)

end H16U
end Minimality
