module

public import Minimality.Type08S.C2K8H

@[expose] public section

/-! # K8I: `tpA1iiK_hasLexCell`: the K3 leftover `TpA1iiK` has a lex cell except in an explicit codim-6 leftover. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **`TpA1iiK` has a lex cell** unless (with `C = ⟪c - d, b - d⟫`, `X = det3 (a' - b) (c - d) (a - d)`,
`E = det3 (b - d) (c - d) (a - d)`, `t = a'` if `X E ≥ 0`, `t = b` if `X E < 0`, `s = ⟪t - c', c - d⟫`):
* `C = 0` and `X = 0`; or
* `C = 0`, `X ≠ 0`, `s = 0`, `⟪t - c', a - d⟫ ≤ 0` and `⟪t - c', b - d⟫ ≤ 0`; or
* `0 < C`, `s = 0` and `⟪t - c', b - d⟫ = 0`. -/
theorem tpA1iiK_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1iiK a a' b b' c c' d)
    (hL1 : ⟪c - d, b - d⟫ = 0 → det3 (a' - b) (c - d) (a - d) ≠ 0)
    (hL2 : ⟪c - d, b - d⟫ = 0 →
      (0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
        0 < ⟪a' - c', a - d⟫ ∨ 0 < ⟪a' - c', b - d⟫) ∧
      (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
        0 < ⟪b - c', a - d⟫ ∨ 0 < ⟪b - c', b - d⟫))
    (hL3 : 0 < ⟪c - d, b - d⟫ →
      (0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
        ⟪a' - c', b - d⟫ ≠ 0) ∧
      (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
        ⟪b - c', b - d⟫ ≠ 0)) :
    HasLexCell (V8 a a' b b' c c' d) :=
  C2.tpA1ii_hasLexCell_K8 N h.1 hL1 hL2 hL3


end Type08Sp
end Minimality
