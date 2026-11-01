module

public import Minimality.Type16UG
public import Minimality.Type16UD

@[expose] public section


/-!
# U1: EV1 leaf `LDE (6,3,5,4)` as `HasLexCell` / `IsRupert`, and its σ-image `LDE (0,3,5,4)`
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

theorem u06_ne (T : Type16 x) : x 6 - x 0 ≠ 0 :=
  sub_ne_zero.2 (fun e => by have := T.inj e; revert this; decide)

/-- **Leaf `LDE (6,3,5,4)`** (EV1 at `s06`, `e = 6`): `ζ < 0`, `φF(0,6) > 0`, `φH(0,6) < 0`; the five depth ties
`6/3`, `6/5`, `6/4`, `3/4`, `5/4` along `u = x6 - x0` are excluded (`ζ ≠ 0` is the `3/5` tie). -/
theorem h16u_ev1_L2 (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (d1 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d2 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d3 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) (d4 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d5 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) :
    HasLexCell (univ.image x) :=
  ⟨x 6 - x 0, u06_ne T, h16u_ev1_L2_cell T hζ hF hH d1 d2 d3 d4 d5⟩

theorem h16u_ev1_L2_isRupert (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (d1 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d2 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d3 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) (d4 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d5 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_ev1_L2 T hζ hF hH d1 d2 d3 d4 d5)

/-- **Leaf `LDE (0,3,5,4)`** (σ-image of `LDE (6,3,5,4)`; EV1 at `s06`, `e = 0`): `ζ > 0`, `φF(0,6) > 0`,
`φH(0,6) < 0`.  Depth ties along `u = x0 - x6`. -/
theorem h16u_ev1_L6 (T : Type16 x) (hζ : 0 < ⟪x 5 - x 3, x 6 - x 0⟫)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (d1 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 3, x 0 - x 6⟫) (d2 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 5, x 0 - x 6⟫)
    (d3 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) (d4 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d5 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) :
    HasLexCell (univ.image x) := by
  refine hasLexCell_of_sigma (h16u_ev1_L2 T.sigma ?_ ?_ ?_ d1 d2 d3 d4 d5)
  · show ⟪x 5 - x 3, x 0 - x 6⟫ < 0
    have : ⟪x 5 - x 3, x 0 - x 6⟫ = -⟪x 5 - x 3, x 6 - x 0⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  · show 0 < T.ff 7 (x 0) - T.ff 7 (x 6)
    linarith
  · show T.ff 5 (x 0) - T.ff 5 (x 6) < 0
    linarith

theorem h16u_ev1_L6_isRupert (T : Type16 x) (hζ : 0 < ⟪x 5 - x 3, x 6 - x 0⟫)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (d1 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 3, x 0 - x 6⟫) (d2 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 5, x 0 - x 6⟫)
    (d3 : ⟪x 0, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) (d4 : ⟪x 3, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫)
    (d5 : ⟪x 5, x 0 - x 6⟫ ≠ ⟪x 4, x 0 - x 6⟫) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (h16u_ev1_L6 T hζ hF hH d1 d2 d3 d4 d5)

end H16U
end Minimality
