module

public import Minimality.Type08S.C2K6TBA

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

/-- **6a** QPa, `ζ(a,c) = 0`: `α4 > 1` face `Q_ac`, `α4 < 1` the pentagon `(c',b',c,d,b)`.
Extra hypotheses: `hu0 : ζ(a,d) ≠ 0` (else `a ≡ c ≡ d ≡ b'` in depth), `hα4 : α4 ≠ 1`. -/
theorem k6t2_pa6a {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (hζ : ⟪a - c, d - b⟫ = 0) (hu0 : ⟪a - d, d - b⟫ ≠ 0)
    (hα4 : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hγ61 := hfar' hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [one_mul] at hκ'
  have hz1 : ⟪a - c, d - b⟫ = ⟪a - d, d - b⟫ - ⟪c - d, d - b⟫ := by
    simp only [inner_sub_left]; ring
  rw [det_alpha4 hb'] at hα4
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  have hne : α4 - 1 ≠ 0 := by
    intro h; apply hα4; rw [h]; ring
  rcases lt_or_gt_of_ne hne with h2 | h2
  · refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
    exact k6t2_c1_pa0_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hγ6 (Or.inl hγ61) hκ' (by linarith) hu0
      (hmemX (k5dX1_mem α4 γ4 β1 β6 γ6)) hVall
  · refine k5c_qpc_gt_hasLexCell W hT' hfar ?_
    rw [det_alpha4 hb']
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith

end C2
end Type08Sp
end Minimality
