module

public import Minimality.Type08S.P2PF1
public import Minimality.Type08S.P2QWP2PF2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F, T4 `K_b` (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`, F-middle `a'`, G-middle `a`):
the picture facts of `Norm08 + RegT4`, and `ClsT4 d b c b' c' a' a` from the top-vertex class `TopP` alone.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem pic_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : b - d = κ • e3) (hf2 : ⟪c - d, e2⟫ = 0)
    (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫) :
    PicT4 ⟪c - d, e1⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪a' - d, e1⟫
      (⟪a - d, e2⟫ / ⟪c' - d, e2⟫) :=
  W5.pic_Kb N.toW hreg hF hκ hxe hf2 hL hr

theorem ClsT4_Kb_of_top {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : b - d = κ • e3) (hf2 : ⟪c - d, e2⟫ = 0)
    (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    (htop : TopP 0 ⟪c - d, e1⟫ ⟪b - d, e3⟫ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫
      ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫) : ClsT4 d b c b' c' a' a :=
  W5.ClsT4_Kb_of_top N.toW hreg hF hκ hxe hf2 hL hr htop

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.pic_Kb
#print axioms Minimality.Type08Sp.ClsT4_Kb_of_top
