module

public import Minimality.Type08S.C2K14G

@[expose] public section


/-!
# K14 / H: the box boundary with `α1 = 1` (needs `⟪a - d, b - d⟫ < 0` and `β6 > 1` or `γ6 > 1`) and the shrunken `K14mBoundary`
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

theorem k14_A1_hasLexCell_mirror {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1:ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1:ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hβ1 : 1 < β1) (hγ6 : 1 < γ6) (hβ6 : 0 < β6) (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hs : ⟪a - d, b - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have hs' : ⟪a - d, c - d⟫ < 0 := by
    obtain ⟨m1, -, -⟩ := hM
    have : ⟪a - d, b - c⟫ = ⟪a - d, b - d⟫ - ⟪a - d, c - d⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    linarith
  have := k14_A1_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hβ1 hγ6 hβ6 (by linarith)
    (k6m_M_swap hM) hs'
  rwa [k6m_V8_swap] at this

/-- `K6mBoundary` with the `α1 = 1` piece cut to its leftover: `⟪a - d, b - d⟫ ≥ 0` or `β6, γ6 ≤ 1`. -/
def K14mBoundary (a b d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  β1 = 1 ∨ (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ α1 = 1 ∧ (0 ≤ ⟪a - d, b - d⟫ ∨ (β6 ≤ 1 ∧ γ6 ≤ 1))) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

theorem k14_boundary_step {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : K6mBoundary α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14mBoundary a b d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  rcases h with h | h | ⟨h1', h2', h3'⟩ | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · by_cases hs : ⟪a - d, b - d⟫ < 0
    · by_cases h6 : 1 < β6
      · subst h3'
        exact Or.inl (k14_A1_hasLexCell hdet hc' hb' ha' h1' h6 hγ6' h2' hM hs)
      · by_cases g6 : 1 < γ6
        · subst h3'
          exact Or.inl (k14_A1_hasLexCell_mirror hdet hc' hb' ha' h1' g6 hβ6' h2' hM hs)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1', h2', h3', Or.inr ⟨not_lt.1 h6, not_lt.1 g6⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1', h2', h3', Or.inl (not_lt.1 hs)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end C2
end Type08Sp
end Minimality
