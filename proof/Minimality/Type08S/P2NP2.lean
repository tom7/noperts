module

public import Minimality.Type08S.P2NP1
public import Minimality.Type08S.P2QWP2NP2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, T4 `K_b` and `K_2`: extra picture facts
(`Y_g > 0`, `Y_p = 0`, `p` not on the line `x f`, `q` on the chord `x g` strictly between, chord sign).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem extra_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : b - d = κ • e3) (hf2 : ⟪c - d, e2⟫ = 0)
    (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    (hcg : 0 < ⟪c' - d, e2⟫ * ⟪b' - d, e1⟫ - ⟪c' - d, e1⟫ * ⟪b' - d, e2⟫)
    (hlam : ⟪a - d, e2⟫ / ⟪c' - d, e2⟫ < 1) :
    0 < ⟪c' - d, e2⟫ ∧ ⟪a' - d, e2⟫ = 0 ∧
      ⟪c - d, e1⟫ * (⟪a' - d, e3⟫ - κ) - ⟪a' - d, e1⟫ * (⟪c - d, e3⟫ - κ) ≠ 0 ∧
      0 < ⟪a - d, e2⟫ ∧ ⟪a - d, e2⟫ < ⟪c' - d, e2⟫ ∧
      ⟪a - d, e1⟫ * ⟪c' - d, e2⟫ = ⟪a - d, e2⟫ * ⟪c' - d, e1⟫ ∧
      0 < κ * ((0 - ⟪c' - d, e2⟫) * (⟪a - d, e3⟫ - ⟪c' - d, e3⟫) -
        (κ - ⟪c' - d, e3⟫) * (⟪a - d, e2⟫ - ⟪c' - d, e2⟫)) :=
  W5.extra_Kb N.toW hreg hF hκ hxe hf2 hL hr hcg hlam

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.extra_Kb
