module

public import Minimality.Type08S.C2K14C

@[expose] public section


/-!
# K14 / D: the H4 tie (mirror) and the shrunken tie leftover `K14mTie`
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

/-- H4 tie (mirror of the H2 tie, view `a - c'`): `ζ(b, a') = 0`, `ζ(b', a') ≠ 0`. -/
theorem k14_H4tie_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hlit : ⟪b - a', a - c'⟫ = 0) (hlit2 : ⟪b' - a', a - c'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have := k14_H2tie_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hβ6 hβ61
    (k6m_M_swap hM) hlit hlit2
  rwa [k6m_V8_swap] at this

/-- Residual literal ties of H2 and H4: also `ζ(c', a') = 0` (resp. `ζ(b', a') = 0`) at the same view. -/
def K14mTie (a a' b b' c c' : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < α1 ∧ 1 < β1 ∧ 1 < β6 ∧ γ6 < 1 ∧ ⟪c - a', a - b'⟫ = 0 ∧ ⟪c' - a', a - b'⟫ = 0) ∨
    (1 < α1 ∧ 1 < β1 ∧ β6 < 1 ∧ 1 < γ6 ∧ ⟪b - a', a - c'⟫ = 0 ∧ ⟪b' - a', a - c'⟫ = 0)

theorem k14_tie_step {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : K6mTie a a' b b' c c' α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  rcases h with ⟨ha, hb, h6, g6, hl⟩ | ⟨ha, hb, h6, g6, hl⟩
  · by_cases h2 : ⟪c' - a', a - b'⟫ = 0
    · exact Or.inr (Or.inl ⟨ha, hb, h6, g6, hl, h2⟩)
    · exact Or.inl (k14_H2tie_hasLexCell hdet hc' hb' ha' ha hb h6 hγ6' g6 hM hl h2)
  · by_cases h2 : ⟪b' - a', a - c'⟫ = 0
    · exact Or.inr (Or.inr ⟨ha, hb, h6, g6, hl, h2⟩)
    · exact Or.inl (k14_H4tie_hasLexCell hdet hc' hb' ha' ha hb hβ6' h6 g6 hM hl h2)

end C2
end Type08Sp
end Minimality
