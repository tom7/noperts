module

public import Minimality.Type08S.P2PF2
public import Minimality.Type08S.P2QWP2PF3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F, T4 `K_2` (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`, F-middle `a`, G-middle `a'`):
the picture facts of `Norm08 + RegT4`, and `ClsT4 b d c' b' c a a'` from the top-vertex class `TopP` alone.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem pic_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫) :
    PicT4 ⟪c' - b, e1⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪a - b, e1⟫
      (⟪a' - b, e2⟫ / ⟪c - b, e2⟫) :=
  W5.pic_K2 N.toW hreg hF hκ hxe hf2 hL hr

theorem ClsT4_K2_of_top {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    (htop : TopP 0 ⟪c' - b, e1⟫ ⟪d - b, e3⟫ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫
      ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫) : ClsT4 b d c' b' c a a' :=
  W5.ClsT4_K2_of_top N.toW hreg hF hκ hxe hf2 hL hr htop

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.pic_K2
#print axioms Minimality.Type08Sp.ClsT4_K2_of_top
