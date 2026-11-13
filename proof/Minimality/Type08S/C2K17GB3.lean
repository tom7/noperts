module

public import Minimality.Type08S.C2K17GB2

@[expose] public section

/-!
# K17GB / GB3: S1.4a, S1.4b (A41, `ζ(d,b) = 0`, `β6 = 1`), view `d - b`, frame `(a-d, c-d, d-b)`.
* S1.4a (`ζ_{a-c'}(a,b') > 0 ⟺ pr > 0`): cycle `(c',b',c,d,b)`, tilt `(rr, -λ pr)`.
* S1.4b (`< 0 ⟺ pr < 0`): cycle `(c',b',a',b)`, tilt `(-1, -λ η)`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `β6 = 1` from the determinant tie. -/
theorem k17gb_b61 {a a' b c d : ℝ³} {β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (h : det3 (a' - b) (c - d) (a - d) = 0) : β6 = 1 := by
  rw [k17gb_det_beta6 ha'] at h
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · exact absurd h hdet

end C2
end Type08Sp
end Minimality
