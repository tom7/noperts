module

public import Minimality.Type08S.P2PF0
public import Minimality.Type08S.P2QWP2PF1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F, N2 `K_c` (view `c - a'`): the picture facts of `Norm08 + RegN2`.

In the canonical frame at `a'` (`c - a' = κ e3`, `b - a'` edge-on with `X_b = L > 0`, `Y_{c'} > 0`):
the screen quadrilateral `(x̄, f̄, r̄, ḡ) = (0, b̄, c̄', b̄')` is strictly convex at `r` and `g`, the F-middle
`d` is over the open chord (`0 < X_d < L`), and `a` is strictly inside the screen quadrilateral
(four strict inequalities).  NOTE (D5): `a` is NOT always inside the triangle `(x̄, f̄, ḡ)`
(true for ~5% of N2 samples); it lies in the triangle `(f̄, r̄, ḡ)` or on the diagonal `f̄ḡ` otherwise.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem pic_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hce : c - a' = κ • e3) (hb2 : ⟪b - a', e2⟫ = 0)
    (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫) :
    PicN2 ⟪b - a', e1⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪d - a', e1⟫
      ⟪a - a', e1⟫ ⟪a - a', e2⟫ :=
  W5.pic_N2 N.toW hreg hF hκ hce hb2 hL hr

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.pic_N2
