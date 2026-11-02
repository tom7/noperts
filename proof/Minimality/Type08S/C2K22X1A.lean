module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Triangle `(a, c', b')` in the frame `(b-d, c-d, a-d)` with extras `d, b, c, a'=(1,γ6,0)` (reuses `k19_tri_tsc`,
`α4 = 1`, `β6 = 1`). -/
theorem k22x1_tsc {D β1 γ4 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 1 < β1) (hγ4 : 1 < γ4) (hγ6 : 0 < γ6)
    (hin : 0 < β1 * γ4 - β1 * γ6 - γ4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      TSc D (k19Tri 1 β1 γ4 (i + 1) - k19Tri 1 β1 γ4 i) (k19Tri 1 β1 γ4 j - k19Tri 1 β1 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0), (1, γ6, 0)], ∀ i : ZMod 3,
      TSc D (k19Tri 1 β1 γ4 (i + 1) - k19Tri 1 β1 γ4 i) (t - k19Tri 1 β1 γ4 i) (v1, v2, 0)) :=
  k19_tri_tsc (β6 := 1) hD one_pos hβ1 hγ4 one_pos hγ6 (by linarith) hv1 hv2

end C2
end Type08Sp
end Minimality
