module

public import Minimality.Type08S.P2PF4
public import Minimality.Type08S.P2QWP2NP1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, N2 `K_c`: extra picture facts (`Y_g > 0`, `Y_d = 0`, `d` not on the line `c b`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem extra_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hce : c - a' = κ • e3) (hb2 : ⟪b - a', e2⟫ = 0)
    (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫) :
    0 < ⟪b' - a', e2⟫ ∧ ⟪d - a', e2⟫ = 0 ∧
      ⟪b - a', e1⟫ * (⟪d - a', e3⟫ - κ) - ⟪d - a', e1⟫ * (⟪b - a', e3⟫ - κ) ≠ 0 :=
  W5.extra_N2 N.toW hreg hF hκ hce hb2 hL hr

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.extra_N2
