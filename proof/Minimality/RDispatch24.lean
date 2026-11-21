module

public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Q45

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Q45

namespace Minimality.T24

/-- Inside the closed `C̄` region: `ω3, ω4, ω5 > 0` and `Δ24 ≥ 0`
(complement of `isRupert_type24_outside_Cbar'`, `Type24.lean`). -/
def CbarIn (x : Fin 7 → ℝ³) : Prop :=
  0 < Minimality.omega3 x ∧ 0 < Minimality.omega4 x ∧ 0 < Minimality.omega5 x ∧
    0 ≤ Minimality.Delta24 x

/-- Universal `Q45HalfHyp` over all positive Lemma-M decompositions `x 3 - x 0 = s (x 4 - x 0) + t (x 5 - x 0)`
with `1 < s + t`. -/
def Q45HalfPred {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t

end Minimality.T24
