module

public import Minimality.Type08S.G6H8
public import Minimality.Type08S.G6J5
public import Minimality.Type08S.G6K3

@[expose] public section

set_option autoImplicit true

/-!
# G6' final closings at `T` and `T'`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **T closing** (29.12 + §41): H1 by `close_T_H1`, H2 by `close_T_H2'`, off both by `close_T_off'`.
`¬RTouch` is not needed on this route. -/
theorem close_T2_final {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hco : ¬ CoT2 a a' b b' c c' d) (hnt : ¬ RTouch a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  by_cases h1 : H1 b b' c c' d
  · exact close_T_H1 N hT h1 hco hnt
  · by_cases h2 : H2 a b b' c d
    · exact close_T_H2' N hT h2 hco
    · exact close_T_off' N hT h1 h2 hco

/-- **T' closing** (29.13). -/
theorem close_T'2_final {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) (hco : ¬ CoT'2 a a' b b' c c' d) (hnt : ¬ RTouch a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_T'2' N hT' hco

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T2_final
#print axioms Minimality.Type08Sp.close_T'2_final
