module

public import Minimality.Type08S.P2F8
public import Minimality.Type08S.P2I9b

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- **`Tp_far`, in the form of the residual `TpFarH`**: the weak far triple at `T'` is Rupert. -/
theorem Tp_far_of_H (N : Norm08 a a' b b' c c' d) (h : TpFarH N) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  Tp_far N h.1 h.2

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.Tp_far_of_H
#print axioms Minimality.Type08Sp.Tp_far
