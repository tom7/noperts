module

public import Minimality.Type08S.C2K17GB7

@[expose] public section


/-!
# K18 / D: S1.8 (TaC, `⟪a-d,b-d⟫ = 0`) closed: S1.8a on the closed side `⟪a-b',a-c'⟫ ≥ 0`

`k17gb_s18a` uses `ζ_{a-c'}(a,b') > 0` only for `pr > 0`; by `k17gb_tac_frame`
`ζ = (α1-1)(γ4 pr - (1-α4) pp)`, so `ζ ≥ 0` already gives `γ4 pr ≥ (1-α4) pp > 0`.  With S1.8b (`ζ < 0`) no leftover.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **S1.8a, closed side**. -/
theorem k18_s18a {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K14TaC a a' b b' c c' d) (hpq : ⟪a - d, b - d⟫ = 0) (hle : 0 ≤ ⟪a - b', a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hα4, hα41, hγ4, hβ6, hpl, hqr, hL⟩ :=
    k17gb_tac_frame W hT' h hpq
  have hpp : 0 < ⟪a - d, a - d⟫ := by
    apply real_inner_self_pos.2
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpr : 0 < ⟪a - d, c - d⟫ := by
    rw [hL] at hle
    have h1 : 0 < α1 - 1 := by linarith
    have h2 : 0 ≤ γ4 * ⟪a - d, c - d⟫ - (1 - α4) * ⟪a - d, a - d⟫ := by
      by_contra hh; push Not at hh; nlinarith [mul_pos h1 (neg_pos.2 hh)]
    have h3 : 0 < γ4 * ⟪a - d, c - d⟫ := by nlinarith [mul_pos (sub_pos.2 hα41) hpp]
    exact pos_of_mul_pos_right h3 (by linarith)
  exact k17gb_s18a_cell hdet hc' hb' ha' hα1 hβ1 hα4 hα41 hγ4 hβ6 hqr hpq hpr

/-- **S1.8 closed**: `K14TaC` (with `¬ T'`) and `⟪a-d,b-d⟫ = 0` have a lex cell. -/
theorem k18_s18 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K14TaC a a' b b' c c' d) (hpq : ⟪a - d, b - d⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  rcases le_or_gt 0 ⟪a - b', a - c'⟫ with hl | hl
  · exact k18_s18a W hT' h hpq hl
  · rcases k17gb_s18b W hT' h hpq with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 hl)

end C2
end Type08Sp
end Minimality
