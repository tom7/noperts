module

public import Minimality.Type08S.C2K6TCQ
public import Minimality.Type08S.C2K6TCK
public import Minimality.Type08S.C2K6TCC

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

/-- **Leftover of QTT after K6TL3**: only the codim-6 coincidence `ζ(a,d) = ζ(c,d) = 0`. -/
def K6t3LeftTT (a a' b b' c c' d : ℝ³) : Prop := ⟪a - d, d - b⟫ = 0 ∧ ⟪c - d, d - b⟫ = 0

open C2 in
theorem k6t3_TT {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsTT a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6t3LeftTT a a' b b' c c' d := by
  have hT := h.1
  have hT' := h.2.1
  rcases k6t2_TT W h with h1 | h1 | ⟨h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exact Or.inl (k6t3_tt5b_le W hT hT' h2 h3 h4)

/-- **Leftover of QPa after K6TL3** (`Δ = det3 (a-d)(b-d)(c-d)`): as `K6tLeftPa`, with `ζ(a,d) ≥ 0` resp. `ζ(b',c) ≥ 0`
sharpened to `= 0` (the tie `u = 0` with `⟪b - d, c - d⟫ ≤ 0`, resp. `ζ(b',c) = 0`). -/
def K6t3LeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪a - c, d - b⟫ = 0 ∧ ⟪a - d, d - b⟫ = 0) ∨
  (⟪b' - c, d - b⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
    0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ ⟪a - d, d - b⟫ = 0)) ∨
  (det3 (b' - a) (b - d) (c - d) = 0 ∧ 0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ ⟪b' - c, d - b⟫ = 0))

open C2 in
theorem k6t3_Pa {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h : K5ZsPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6t3LeftPa a a' b b' c c' d := by
  have hT' := h.1
  have hnT := h.2.1
  have hκ := h.2.2.1
  rcases k6t2_Pa W hfar h with h1 | h1 | ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · by_cases hb0 : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h3, h4, Or.inl hb0⟩))
    · have hβ := lt_of_le_of_ne h4 (Ne.symm hb0)
      rcases h5 with h5 | h5
      · exact absurd h5 hb0
      · rcases h5.lt_or_eq with h6 | h6
        · exact Or.inl (k6t3_pa6b W hT' hnT hκ hβ h2 h6)
        · exact Or.inr (Or.inr (Or.inl ⟨h2, h3, h4, Or.inr h6.symm⟩))
  · by_cases hb0 : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0
    · exact Or.inr (Or.inr (Or.inr ⟨h2, h3, Or.inl hb0⟩))
    · have hβ := lt_of_le_of_ne h3 (Ne.symm hb0)
      rcases h4 with h4 | h4
      · exact absurd h4 hb0
      · rcases h4.lt_or_eq with h6 | h6
        · exact Or.inl (k6t3_pa6c W hT' hnT hκ hβ h6)
        · exact Or.inr (Or.inr (Or.inr ⟨h2, h3, Or.inr h6.symm⟩))

end Type08Sp
end Minimality
