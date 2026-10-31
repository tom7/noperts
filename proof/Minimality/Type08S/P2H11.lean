module

public import Minimality.Type08S.P2H8
public import Minimality.Type08S.P2QWP2H11

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H11: Lemma E (iii) (D6) as a culJ determinant inequality — proved on every `Norm08` shape

In culJ coordinates (`a = e₁`, `b = e₂`, `c = e₃`, `d = 0`, `a' = (0, β6, γ6)`, `b' = (α4, 0, γ4)`,
`c' = (α1, β1, 0)`, `θ = (α1, β1, α4, γ4, β6, γ6)`):
* `K_b`, `K_2` (plane `c b' c'`, points `b`, `d`): the two determinants are `gWa` and `-α4 β1`;
* `K_c` (plane `b c' b'`, points `c`, `a'`): `gWa` and `α1 γ4 (1 - β6) - α1 γ6 + α4 γ6 (1 - β1)`, the negative of
  a `common08` entry.
So the products are strictly negative on `Norm08` (no region hypothesis needed); `x ∉ Π'` is automatic too.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem lemE_all {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    LemE3 a' c b c' b' ∧ LemE3 d b c b' c' ∧ LemE3 b d c' b' c :=
  W5.lemE_all N.toW

end Type08Sp
end Minimality
