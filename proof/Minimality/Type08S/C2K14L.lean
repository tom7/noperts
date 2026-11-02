module

public import Minimality.Type08S.C2K14K

@[expose] public section


/-!
# K14 / L: Pa(1) (`ζ(a,c) = ζ(a,d) = 0`) with `α4 > 1`: face `Q_ac` at `b - d` (closed for any depth ties)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- `K6t3LeftPa` with the codim-6 piece `a ≡ c ≡ d` cut to `α4 ≤ 1` (`α4 > 1` is the face `Q_ac`, `k5c_qpc_gt_hasLexCell`). -/
def K14LeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪a - c, d - b⟫ = 0 ∧ ⟪a - d, d - b⟫ = 0 ∧
    det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≤ 0) ∨
  (⟪b' - c, d - b⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
    0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ ⟪a - d, d - b⟫ = 0)) ∨
  (det3 (b' - a) (b - d) (c - d) = 0 ∧ 0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ ⟪b' - c, d - b⟫ = 0))

theorem k14_Pa {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h : K5ZsPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14LeftPa a a' b b' c c' d := by
  rcases k6t3_Pa W hfar h with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · obtain ⟨h2, h3⟩ := h1
    rcases le_or_gt (det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d)) 0 with hα | hα
    · exact Or.inr (Or.inl ⟨h2, h3, hα⟩)
    · exact Or.inl (k5c_qpc_gt_hasLexCell W h.1 hfar hα)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

end Type08Sp
end Minimality
