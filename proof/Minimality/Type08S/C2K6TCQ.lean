module

public import Minimality.Type08S.C2K6TCP

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6t3_inner_dmb (x b d : ℝ³) : ⟪x, d - b⟫ = -⟪b - d, x⟫ := by
  have : d - b = -(b - d) := by abel
  rw [this, inner_neg_right, real_inner_comm]

/-- Shared setup of the Pa wrappers: coordinates, `γ6 < 1`, `β1 > 1`, `b' - c = α4 R`. -/
theorem k6t3_pa_setup {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hnT : ¬ IsT a' b c d) (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d)) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 1 < β1 ∧ 0 < α4 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧
      α4 * (1 - β1) = 1 - γ4 ∧ b' - c = α4 • ((a - d) + (β1 - 1) • (c - d)) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hg61 : γ6 < 1 := hfa (k5z_far1 W hT' hnT)
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  have hb1 : 1 < β1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) this.le]
  have hγ4' : γ4 = 1 + α4 * (β1 - 1) := by linarith
  refine ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hb1, hα4p, hβ6, hγ6, hg61, hγ6s, by linarith, ?_⟩
  rw [hb', hγ4']; module

/-- `⟪b - d, R⟫` where `R = (a - d) + (β1 - 1)(c - d)`: the depth `u` of `b` at the view `b' - c`. -/
theorem k6t3_pa6c {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hnT : ¬ IsT a' b c d) (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hζ : 0 < ⟪b' - c, d - b⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hb1, hα4, hβ6, hγ6, hg61, hcv, hκ', hbc⟩ :=
    k6t3_pa_setup W hT' hnT hκ hβ
  have hu : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ < 0 := by
    rw [hbc, inner_smul_left] at hζ
    have e : ⟪(a - d) + (β1 - 1) • (c - d), d - b⟫ = -⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ := by
      exact k6t3_inner_dmb _ _ _
    simp only [conj_trivial] at hζ
    rw [e] at hζ
    nlinarith
  exact k6t3_pa_core hdet hc' hb' ha' hb1 hα4 hβ6 hγ6 hg61 hcv hκ' hu.le (n := 1) le_rfl
    (fun h => absurd h hu.ne) (fun h => absurd h hu.ne)

/-- 6b (`ζ(b',c) = 0`) with `ζ(a,d) = ⟪a - d, d - b⟫ > 0`. -/
theorem k6t3_pa6b {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hnT : ¬ IsT a' b c d) (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hζ : ⟪b' - c, d - b⟫ = 0) (hζ2 : 0 < ⟪a - d, d - b⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hb1, hα4, hβ6, hγ6, hg61, hcv, hκ', hbc⟩ :=
    k6t3_pa_setup W hT' hnT hκ hβ
  have e : ⟪(a - d) + (β1 - 1) • (c - d), d - b⟫ = -⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ := by
    exact k6t3_inner_dmb _ _ _
  have hu0 : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ = 0 := by
    rw [hbc, inner_smul_left] at hζ
    simp only [conj_trivial] at hζ
    rw [e] at hζ
    rcases mul_eq_zero.1 hζ with h | h
    · exact absurd h hα4.ne'
    · linarith
  have hexp : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ = ⟪b - d, a - d⟫ + (β1 - 1) * ⟪b - d, c - d⟫ := by
    rw [inner_add_right, real_inner_smul_right]
  have hba : ⟪b - d, a - d⟫ < 0 := by
    have : ⟪a - d, d - b⟫ = -⟪b - d, a - d⟫ := by
      have := k6t3_inner_dmb (a - d) b d
      rw [this, real_inner_comm]
    linarith
  have hDc : 0 < ⟪b - d, c - d⟫ := by
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg (sub_pos.2 hb1).le (neg_nonneg.2 hh)]
  have hDb : 0 ≤ ⟪b - d, b - d⟫ := real_inner_self_nonneg
  refine k6t3_pa_core (n := β6 * ⟪b - d, b - d⟫ / ⟪b - d, c - d⟫ + 1) hdet hc' hb' ha' hb1 hα4 hβ6 hγ6 hg61 hcv hκ'
    hu0.le ?_ (fun _ => hDc) ?_
  · have : 0 ≤ β6 * ⟪b - d, b - d⟫ / ⟪b - d, c - d⟫ := by positivity
    linarith
  · intro _
    have : (β6 * ⟪b - d, b - d⟫ / ⟪b - d, c - d⟫ + 1) * ⟪b - d, c - d⟫ = β6 * ⟪b - d, b - d⟫ + ⟪b - d, c - d⟫ := by
      field_simp
    rw [this]; linarith

end C2
end Type08Sp
end Minimality
