module

public import Minimality.Type08S.C2K16I

@[expose] public section


/-!
# K16 / J: the H5 leftover cut by the rules r1, r9 (given the Coll5 relation).
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

/-- `K14mH5` with the rules r1 (`ζ_{d-c}(c, a') < 0`) and r9 (`ζ_{d-b}(b, a') < 0`) removed. -/
def K16mH5 (a a' b c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K14mH5 a c' d α1 β1 β6 γ6 ∧ 0 ≤ ⟪c - a', d - c⟫ ∧ 0 ≤ ⟪b - a', d - b⟫

theorem k16_h5_step {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K14mH5 a c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16mH5 a a' b c c' d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl4⟩ := h
  have hR := hrel hβ1
  by_cases l1 : ⟪c - a', d - c⟫ < 0
  · exact Or.inl (k16_r1_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM hR l1)
  by_cases l9 : ⟪b - a', d - b⟫ < 0
  · exact Or.inl (k16_r9_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM hR l9)
  exact Or.inr ⟨⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl4⟩, not_lt.1 l1, not_lt.1 l9⟩

end C2
end Type08Sp
end Minimality
