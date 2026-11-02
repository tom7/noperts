module

public import Minimality.Type08S.C2K16C

@[expose] public section


/-!
# K16 / D: with the region data, the M `α1 = 1` boundary piece of N2 closes under `RegN2` and is empty for Kb under `RegT4`.
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
namespace C2

/-- `K14mBoundary` with the `α1 = 1` piece restricted to `¬ reg` (`reg` = the region of the closing: `RegN2` for N2,
`RegT4` for Kb). -/
def K16mBoundary (reg : Prop) (a b d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  β1 = 1 ∨ (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ α1 = 1 ∧ ¬ reg ∧ (0 ≤ ⟪a - d, b - d⟫ ∨ (β6 ≤ 1 ∧ γ6 ≤ 1))) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

/-- N2 boundary step: `K14mBoundary`, and the third piece under `RegN2` is closed by the pentagon cell. -/
theorem k16_n2_boundary {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hN2 : ParEndN2 a a' b b' c c')
    {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : K14mBoundary a b d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16mBoundary (RegN2 W.F) a b d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  rcases h with h | h | ⟨h1', h2', h3', h4'⟩ | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · by_cases hR : RegN2 W.F
    · left
      have hγ : 1 < γ6 :=
        (k16_reg_coords W ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩).1 hR
      have hs := k16_n2_s_neg W hκ hN2 hM.1 hdet hc' ha' hα1' h1' hγ6' h3
      subst h3'
      exact k14_A1_hasLexCell_mirror hdet hc' hb' ha' h1' hγ hβ6' h2' hM hs
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1', h2', h3', hR, h4'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Kb boundary step: the `α1 = 1` piece contradicts `RegT4`. -/
theorem k16_kb_boundary {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : K14mBoundary a b d α1 β1 β6 γ6) : K16mBoundary (RegT4 W.F) a b d α1 β1 β6 γ6 := by
  rcases h with h | h | ⟨h1', h2', h3', h4'⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨h1', h2', h3', ?_, h4'⟩))
    intro hR
    have := (k16_reg_coords W hC).2 hR
    linarith [this.1]
  · exact Or.inr (Or.inr (Or.inr h))

end C2
end Type08Sp
end Minimality
