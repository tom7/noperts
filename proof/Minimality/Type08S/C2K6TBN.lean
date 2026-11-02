module

public import Minimality.Type08S.C2K6TBM

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

/-- `γ4 - 1` as a point-form determinant. -/
theorem k6t2_det_gamma4 {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hb' : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    det3 (a - d) (b - d) (b' - c) = (γ4 - 1) * det3 (a - d) (b - d) (c - d) := by
  rw [hb']
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **5b, `γ4 > 1`**: QTT, `ζ(b',a') = 0`: the pentagon `(a,c',b',c,d)` at `d - b`; no other hypothesis. -/
theorem k6t2_tt5b_gt {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : IsT' a b c' d) (hζ2 : ⟪b' - a', d - b⟫ = 0)
    (hγ : 0 < det3 (a - d) (b - d) (b' - c) * det3 (a - d) (b - d) (c - d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  have hz2 : ⟪b' - a', d - b⟫ = (α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫) -
      (γ6 * ⟪c - d, d - b⟫ - β6 * ⟪d - b, d - b⟫) := by
    rw [hb', ha']; simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
  rw [k6t2_det_gamma4 hb'] at hγ
  have hγ41 : 1 < γ4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hA := k5d_hA (P := a - d) (Q := c - d) (R := d - b) hΔ
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
  refine k6t2_c4g_frame _ _ _ _ _ hΔ hα4p hγ41 hαγ hβ1 hβ6 hγ6 (Or.inr hg6) (Or.inl ?_)
    (hmemX (k5dX4_mem α4 γ4 β1 β6 γ6)) hVall
  rw [hg6] at hz2
  nlinarith [mul_pos hβ6 hA]

/-- **5c**: QTT, `ζ(a,d) = 0`, `ζ(c,d) ≠ 0` (`ζ(c,d) = ⟪c - d, d - b⟫`).
`ζ(c,d) > 0`: `(c',b',c,d,b)`; `ζ(c,d) < 0`: `γ4 > 1` the pentagon `(a,c',b',c,d)`, `γ4 ≤ 1` the pentagon `(b',a',b,d,a)`. -/
theorem k6t2_tt5c {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : IsT' a b c' d) (hu : ⟪a - d, d - b⟫ = 0) (ht : ⟪c - d, d - b⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
  rcases lt_or_gt_of_ne ht with h | h
  · rcases le_or_gt γ4 1 with hg | hg
    · exact k6t2_c5u0_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hg6 hg hu h
        (hmemX (k5dX5_mem α4 γ4 β1 β6 γ6)) hVall
    · refine k6t2_c4g_frame _ _ _ _ _ hΔ hα4p hg hαγ hβ1 hβ6 hγ6 (Or.inr hg6) (Or.inl ?_)
        (hmemX (k5dX4_mem α4 γ4 β1 β6 γ6)) hVall
      rw [hu]; nlinarith
  · exact k6t2_c1u0_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hγ6 (Or.inr hg6) hu h
      (hmemX (k5dX1_mem α4 γ4 β1 β6 γ6)) hVall

end C2
end Type08Sp
end Minimality
