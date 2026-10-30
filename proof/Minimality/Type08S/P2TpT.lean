module

public import Minimality.Type08S.P2TpC1
public import Minimality.Type08S.P2TpC2
public import Minimality.Type08S.P2TpSetup

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X: choice of the tilt in the cells `C1`, `C2` (pure real lemmas)
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- A tilt `(t1, 1)` in the cell `C1`, with `t1 ≠ 0`. -/
theorem exists_t_C1 {σ v1 ha w1 α4 γ4 : ℝ} (hσ : σ * σ = 1) (hv : σ * v1 < 0) (hha : 0 < ha)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) :
    ∃ t1 : ℝ, t1 ≠ 0 ∧ 0 < σ * (ha * t1 - w1 * 1) ∧
      0 < σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * 1) := by
  have hr : 0 < -(σ * v1) := by linarith
  have good : ∀ p : ℝ, 0 < p → p ≤ -(σ * v1) * γ4 / 2 →
      0 < σ * (ha * ((σ * p + w1) / ha) - w1 * 1) ∧
      0 < σ * ((α4 - 1) * ha * ((σ * p + w1) / ha) - (γ4 * v1 + (α4 - 1) * w1) * 1) := by
    intro p hp0 hp1
    have e1 : ha * ((σ * p + w1) / ha) = σ * p + w1 := by field_simp
    have e2 : (α4 - 1) * ha * ((σ * p + w1) / ha) = (α4 - 1) * (σ * p + w1) := by
      rw [mul_assoc, e1]
    rw [e1, e2]
    constructor
    · have : σ * (σ * p + w1 - w1 * 1) = p := by
        have : σ * (σ * p) = p := by rw [← mul_assoc, hσ, one_mul]
        linarith [this]
      linarith
    · have h3 : σ * ((α4 - 1) * (σ * p + w1) - (γ4 * v1 + (α4 - 1) * w1) * 1) =
          (α4 - 1) * p - γ4 * (σ * v1) := by
        have : σ * (σ * p) = p := by rw [← mul_assoc, hσ, one_mul]
        linear_combination (α4 - 1) * this
      rw [h3]
      nlinarith [mul_pos hγ4 hr]
  set p1 := -(σ * v1) * γ4 / 2 with hp1
  have hp1pos : 0 < p1 := by positivity
  by_cases h0 : (σ * p1 + w1) / ha = 0
  · refine ⟨(σ * (p1 / 2) + w1) / ha, ?_, good (p1 / 2) (by positivity) (by linarith)⟩
    have h1 : σ * p1 + w1 = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h hha.ne'
    intro h
    have h2 : σ * (p1 / 2) + w1 = 0 := by
      rcases div_eq_zero_iff.1 h with h | h
      · exact h
      · exact absurd h hha.ne'
    have : σ * p1 = 0 := by linarith
    have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
    exact hp1pos.ne' ((mul_eq_zero.1 this).resolve_left hσ0)
  · exact ⟨_, h0, good p1 hp1pos le_rfl⟩

/-- A tilt `(t1, -1)` in the cell `C2`, with nonvanishing slope of the `c' - b'` tie. -/
theorem exists_t_C2 {σ v1 ha w1 α4 γ4 : ℝ} (hσ : σ * σ = 1) (hv : σ * v1 < 0) (hha : 0 < ha)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) :
    ∃ t1 : ℝ, 0 < σ * (ha * t1 - w1 * (-1)) ∧
      σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * (-1)) < 0 ∧
      (1 - α4) * (t1 * w1 + (-1) * ha) - γ4 * (t1 * v1) ≠ 0 := by
  have hr : 0 < -(σ * v1) := by linarith
  have good : ∀ p : ℝ, 0 < p → p ≤ -(σ * v1) * γ4 / (1 + α4) →
      0 < σ * (ha * ((σ * p - w1) / ha) - w1 * (-1)) ∧
      σ * ((α4 - 1) * ha * ((σ * p - w1) / ha) - (γ4 * v1 + (α4 - 1) * w1) * (-1)) < 0 := by
    intro p hp0 hp1
    have e1 : ha * ((σ * p - w1) / ha) = σ * p - w1 := by field_simp
    have e2 : (α4 - 1) * ha * ((σ * p - w1) / ha) = (α4 - 1) * (σ * p - w1) := by
      rw [mul_assoc, e1]
    rw [e1, e2]
    have hσp : σ * (σ * p) = p := by rw [← mul_assoc, hσ, one_mul]
    constructor
    · rw [show σ * (σ * p - w1 - w1 * (-1)) = σ * (σ * p) by ring, hσp]; exact hp0
    · have h3 : σ * ((α4 - 1) * (σ * p - w1) - (γ4 * v1 + (α4 - 1) * w1) * -1) =
          (α4 - 1) * p + γ4 * (σ * v1) := by
        linear_combination (α4 - 1) * hσp
      rw [h3]
      have : p * (1 + α4) ≤ -(σ * v1) * γ4 := by
        rw [le_div_iff₀ (by linarith)] at hp1; exact hp1
      nlinarith [mul_pos hp0 hα4]
  set p1 := -(σ * v1) * γ4 / (1 + α4) with hp1
  have hp1pos : 0 < p1 := by positivity
  have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  by_cases h0 : (1 - α4) * ((σ * p1 - w1) / ha * w1 + (-1) * ha) - γ4 * ((σ * p1 - w1) / ha * v1) = 0
  · refine ⟨(σ * (p1 / 2) - w1) / ha, (good (p1 / 2) (by positivity) (by linarith)).1,
      (good (p1 / 2) (by positivity) (by linarith)).2, ?_⟩
    intro h
    -- both slopes vanish: κ = 0 and (1 - α4) ha = 0, then v1 = 0
    have d : σ * p1 / (2 * ha) * ((1 - α4) * w1 - γ4 * v1) = 0 := by
      have e : (σ * p1 - w1) / ha - (σ * (p1 / 2) - w1) / ha = σ * p1 / (2 * ha) := by
        field_simp; ring
      calc σ * p1 / (2 * ha) * ((1 - α4) * w1 - γ4 * v1)
          = ((σ * p1 - w1) / ha - (σ * (p1 / 2) - w1) / ha) * ((1 - α4) * w1 - γ4 * v1) := by rw [e]
        _ = ((1 - α4) * ((σ * p1 - w1) / ha * w1 + (-1) * ha) - γ4 * ((σ * p1 - w1) / ha * v1)) -
            ((1 - α4) * ((σ * (p1 / 2) - w1) / ha * w1 + (-1) * ha) -
              γ4 * ((σ * (p1 / 2) - w1) / ha * v1)) := by ring
        _ = 0 := by rw [h0, h]; ring
    have hκ : (1 - α4) * w1 - γ4 * v1 = 0 := by
      have : σ * p1 / (2 * ha) ≠ 0 := by positivity
      exact (mul_eq_zero.1 d).resolve_left this
    have hα : (1 - α4) * ha = 0 := by
      have e2 : (1 - α4) * ((σ * p1 - w1) / ha * w1 + (-1) * ha) - γ4 * ((σ * p1 - w1) / ha * v1) =
          ((σ * p1 - w1) / ha) * ((1 - α4) * w1 - γ4 * v1) - (1 - α4) * ha := by ring
      rw [e2, hκ] at h0; linarith
    have hα1 : 1 - α4 = 0 := (mul_eq_zero.1 hα).resolve_right hha.ne'
    rw [hα1] at hκ
    have : v1 = 0 := by
      have : γ4 * v1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hγ4.ne'
    rw [this] at hv; simp at hv
  · exact ⟨_, (good p1 hp1pos le_rfl).1, (good p1 hp1pos le_rfl).2, h0⟩

end Type08Sp
end Minimality
