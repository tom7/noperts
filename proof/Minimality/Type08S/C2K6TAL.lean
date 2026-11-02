module

public import Minimality.Type08S.C2K6TAK

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-! ## QTc -/

/-- Tc, `α4 = 1` (task 2a, not done): the slice itself. -/
def K6tTcA41 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (b - a) (a' - a) (b' - a) = 0 ∧ det3 (b' - a) (b - d) (c - d) = 0

/-- **Leftover of QTc**: `α4 = 1` (task 2a, unfinished) or the `ζ(d,b) = 0` tie without an admissible tilt. -/
def K6tLeftTc (a a' b b' c c' d : ℝ³) : Prop := K6tTcA41 a a' b b' c c' d ∨ K6tLeftZdb a a' b b' c c' d

/-- **Final wrapper for QTc** (`K5ZsTc`).  `α4 < 1`: K5c's face cell (no tie used); `α4 > 1`: K5c's cells if `ζ(d,b) ≠ 0`,
else `k6t1_Tc_zdb`; `α4 = 1`: `K6tTcA41` (unfinished).  The far end and `κ_b > 0` are derived from `¬T'`. -/
theorem k6t1_Tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsTc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTc a a' b b' c c' d := by
  obtain ⟨hT, hT', hκc, hs⟩ := h
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    obtain ⟨_, _, _, _, _, hd, _⟩ := norm08w_coordsT W hT
    exact hd
  have hne : ∀ {x : ℝ}, x ≠ 0 → x * det3 (a - d) (b - d) (c - d) ≠ 0 := fun hx => mul_ne_zero hx hdet
  have hfar := k5z_far2 W hT hT'
  have hκb := k5z_kb_pos W hT hT'
  by_cases h4 : det3 (b' - a) (b - d) (c - d) = 0
  · exact Or.inr (Or.inl ⟨hT, hκc, h4⟩)
  · rcases lt_or_gt_of_ne (hne h4) with h4' | h4'
    · exact Or.inl (k5c_qtc_lt_hasLexCell W hT hκc h4')
    · by_cases hz : ⟪d - b, a - b'⟫ = 0
      · rcases k6t1_Tc_zdb W hT hκc h4' hfar hκb hz with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inl (k5c_qtc_gt_hasLexCell W hT hκc h4' hfar hκb hz)

end C2
end Type08Sp
end Minimality
