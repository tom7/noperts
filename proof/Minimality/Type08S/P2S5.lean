module

public import Minimality.Type08S.P2S4
public import Minimality.Type08S.P2F9

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {a a' b b' c c' d : ℝ³}

/-- Frame data at `T'` with the given representation `b' = d + α4 (a-d) + γ4 (c-d)`. -/
theorem Tp_frame (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) {α4 γ4 : ℝ}
    (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    ∃ β1 β6 γ6 : ℝ, det3 (a - d) (c - d) (b - d) ≠ 0 ∧ c' = d + (a - d) + β1 • (b - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β1 ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 := by
  obtain ⟨α4', β1, γ4', β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  have hne : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = - det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand]; ring
    rw [e, h0, neg_zero]
  have hv : (α4' - α4) • (a - d) + (γ4' - γ4) • (c - d) = 0 := by
    have h1 : d + α4' • (a - d) + γ4' • (c - d) = d + α4 • (a - d) + γ4 • (c - d) := by
      rw [← hb', ← hb'rep]
    have : (α4' - α4) • (a - d) + (γ4' - γ4) • (c - d) =
        (d + α4' • (a - d) + γ4' • (c - d)) - (d + α4 • (a - d) + γ4 • (c - d)) := by module
    rw [this, h1, sub_self]
  have hz1 : det3 ((α4' - α4) • (a - d) + (γ4' - γ4) • (c - d)) (c - d) (b - d) =
      (α4' - α4) * det3 (a - d) (c - d) (b - d) := by
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hz2 : det3 (a - d) ((α4' - α4) • (a - d) + (γ4' - γ4) • (c - d)) (b - d) =
      (γ4' - γ4) * det3 (a - d) (c - d) (b - d) := by
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have z1 : det3 (0 : ℝ³) (c - d) (b - d) = 0 := by simp [det3_expand]
  have z2 : det3 (a - d) (0 : ℝ³) (b - d) = 0 := by simp [det3_expand]
  rw [hv, z1] at hz1
  rw [hv, z2] at hz2
  have hα : α4' = α4 := by
    have : (α4' - α4) * det3 (a - d) (c - d) (b - d) = 0 := by rw [← hz1]
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hne
  have hγ : γ4' = γ4 := by
    have : (γ4' - γ4) * det3 (a - d) (c - d) (b - d) = 0 := by rw [← hz2]
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hne
  subst hα; subst hγ
  refine ⟨β1, β6, γ6, hne, ?_, ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩
  rw [hc']; module

/-- **Lemma T′S** (separation case), in the frame of `Norm08`. -/
theorem Tp_sep (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : α4 < 1)
    (hsep : max (max ⟪d, b - d⟫ ⟪a, b - d⟫) (max ⟪b', b - d⟫ ⟪c, b - d⟫)
      < min ⟪b, b - d⟫ ⟪c', b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨β1, β6, γ6, hne, hc', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ := Tp_frame N hT' hb'rep
  have hH : det3 (a - d) (c - d) (b - d) ≠ 0 := hne
  have key := Tp_sep_core_any d (a - d) (b - d) (c - d) (β1 := β1) (β6 := β6) (γ6 := γ6)
    (α4 := α4) (γ4 := γ4) hH hα4 hα hγ4 hαγ hβ1 hβ6 hγ6 hγ61 (by
      have e1 : ⟪a - d, b - d⟫ = ⟪a, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e2 : ⟪c - d, b - d⟫ = ⟪c, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e3 : ⟪b - d, b - d⟫ = ⟪b, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e4 : ⟪b' - d, b - d⟫ = ⟪b', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e5 : ⟪c' - d, b - d⟫ = ⟪c', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e6 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
        have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb'rep]; module
        rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have e7 : ⟪c' - d, b - d⟫ = ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
        have : c' - d = (a - d) + β1 • (b - d) := by rw [hc']; module
        rw [this, inner_add_left, real_inner_smul_left]
      rw [← e6, ← e7]
      simp only [max_lt_iff, lt_min_iff] at hsep ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨⟨h5, h6⟩, h7, h8⟩⟩ := hsep
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  have ea : d + (a - d) = a := by abel
  have eb : d + (b - d) = b := by abel
  have ec : d + (c - d) = c := by abel
  rw [← hc', ea, eb, ec, ← ha', ← hb'rep] at key
  exact key

end Type08Sp
end Minimality
