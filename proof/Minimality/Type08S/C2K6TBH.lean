module

public import Minimality.Type08S.C2K6TBE

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

/-- **5b, `ζ(a,b') < 0` half**: the K5d QTT cells 8 / 1 do not use `ζ(b',a')`; needs only `ζ(a,d) ≠ 0`. -/
theorem k6t2_tt5b_neg {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : IsT' a b c' d) (hζ1 : ⟪a - b', d - b⟫ < 0) (hζ3 : ⟪a - d, d - b⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  have hz1 : ⟪a - b', d - b⟫ = ⟪a - d, d - b⟫ - (α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫) := by
    rw [hb']; simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
  rcases lt_or_gt_of_ne hζ3 with h3 | h3
  · exact k5d_c1_tt_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hγ6 (Or.inr hg6) (by linarith) (by linarith)
      (hmemX (k5dX1_mem α4 γ4 β1 β6 γ6)) hVall
  · exact k5d_c8_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hg6 (by linarith) (by linarith)
      (hmemX (k5dX5_mem α4 γ4 β1 β6 γ6)) hVall

end C2
end Type08Sp
end Minimality
