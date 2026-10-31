module

public import Minimality.Type08S.P2NP2
public import Minimality.Type08S.P2QWP2NP3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, T4 `K_2`: extra picture facts.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem extra_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    (hcg : 0 < ⟪c - b, e2⟫ * ⟪b' - b, e1⟫ - ⟪c - b, e1⟫ * ⟪b' - b, e2⟫)
    (hlam : ⟪a' - b, e2⟫ / ⟪c - b, e2⟫ < 1) :
    0 < ⟪c - b, e2⟫ ∧ ⟪a - b, e2⟫ = 0 ∧
      ⟪c' - b, e1⟫ * (⟪a - b, e3⟫ - κ) - ⟪a - b, e1⟫ * (⟪c' - b, e3⟫ - κ) ≠ 0 ∧
      0 < ⟪a' - b, e2⟫ ∧ ⟪a' - b, e2⟫ < ⟪c - b, e2⟫ ∧
      ⟪a' - b, e1⟫ * ⟪c - b, e2⟫ = ⟪a' - b, e2⟫ * ⟪c - b, e1⟫ ∧
      0 < κ * ((0 - ⟪c - b, e2⟫) * (⟪a' - b, e3⟫ - ⟪c - b, e3⟫) -
        (κ - ⟪c - b, e3⟫) * (⟪a' - b, e2⟫ - ⟪c - b, e2⟫)) :=
  W5.extra_K2 N.toW hreg hF hκ hxe hf2 hL hr hcg hlam

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.extra_K2
