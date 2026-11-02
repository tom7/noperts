module

public import Minimality.Type08S.C2K6MM

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Gram expansion of an inner product in the frame `(p, q, r)`. -/
theorem k6m_ip (p q r : ℝ³) (x1 y1 z1 x2 y2 z2 : ℝ) :
    ⟪x1 • p + y1 • q + z1 • r, x2 • p + y2 • q + z2 • r⟫ =
      x1 * x2 * ⟪p, p⟫ + x1 * y2 * ⟪p, q⟫ + x1 * z2 * ⟪p, r⟫ + y1 * x2 * ⟪p, q⟫ + y1 * y2 * ⟪q, q⟫ +
      y1 * z2 * ⟪q, r⟫ + z1 * x2 * ⟪p, r⟫ + z1 * y2 * ⟪q, r⟫ + z1 * z2 * ⟪r, r⟫ := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_comm q p, real_inner_comm r p, real_inner_comm r q]
  ring

/-- The shape conditions of the H2 cells, from `κ (1 - α1) = β1`, `σ (1 - α1) = 1`. -/
theorem k6m_H2_conds {κ σ α1 β1 β6 γ6 : ℝ} (hκ : κ * (1 - α1) = β1) (hσ : σ * (1 - α1) = 1)
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) :
    κ < 0 ∧ σ < 0 ∧ 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1) ∧
      0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1) ∧
      0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1) ∧
      (σ - 1) * (1 - β1) ≤ α1 * (σ - κ) := by
  have A : 0 < α1 - 1 := by linarith
  have hκ' : κ * (α1 - 1) = -β1 := by linarith
  have hσ' : σ * (α1 - 1) = -1 := by linarith
  have k0 : κ < 0 := by nlinarith
  have s0 : σ < 0 := by nlinarith
  refine ⟨k0, s0, ?_, ?_, ?_, ?_⟩
  · have e : (α1 - 1) * (-κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1)) =
        β1 * α1 * (β6 - 1) + (α1 - 1) * γ6 * (β1 - 1) := by
      linear_combination (α1 * (β6 - β1) - α1 * (1 - β1)) * (-hκ')
    have : 0 < β1 * α1 * (β6 - 1) + (α1 - 1) * γ6 * (β1 - 1) := by
      have := mul_pos (mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < α1)) (sub_pos.2 hb6)
      have := mul_pos (mul_pos A hγ6) (sub_pos.2 hβ1)
      nlinarith
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg A.le (neg_nonneg.2 hh)]
  · nlinarith [mul_pos (by linarith : (0:ℝ) < β1) hγ6, mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < β1),
      mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < β6)]
  · have e : (α1 - 1) * ((β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1)) =
        (α1 - 1) * (β6 - β1 + β1 * γ6) + β6 * β1 * α1 := by
      linear_combination (β6 * α1) * (-hκ')
    have : 0 < (α1 - 1) * (β6 - β1 + β1 * γ6) + β6 * β1 * α1 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < β6) (by linarith : (0:ℝ) < β1),
        mul_pos A (by linarith : (0:ℝ) < β1), mul_pos A hγ6, mul_pos (mul_pos A (by linarith : (0:ℝ) < β1)) hγ6,
        mul_pos (mul_pos (by linarith : (0:ℝ) < β6) (by linarith : (0:ℝ) < β1)) (by linarith : (0:ℝ) < α1)]
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg A.le (neg_nonneg.2 hh)]
  · have e : (α1 - 1) * (α1 * (σ - κ) - (σ - 1) * (1 - β1)) = 0 := by
      linear_combination (α1 - (1 - β1)) * hσ' - α1 * hκ'
    have := (mul_eq_zero.1 e).resolve_left A.ne'
    linarith

end C2
end Type08Sp
end Minimality
