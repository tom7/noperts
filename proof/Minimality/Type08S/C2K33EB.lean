module

public import Minimality.Type08S.C2K33EA

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
open C2

theorem k32e_ipP (P Q R : ℝ³) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (x1 x2 x3 : ℝ) :
    ⟪x1 • P + x2 • Q + x3 • R, P⟫ = x1 * ⟪P, P⟫ + (x2 + x3) * ⟪P, Q⟫ := by
  have h := k32e_ip P Q R hPR x1 x2 x3 1 0 0
  simp only [one_smul, zero_smul, add_zero] at h
  rw [h]; simp only [k32e_G]; ring

theorem k32e_ipQ (P Q R : ℝ³) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (x1 x2 x3 : ℝ) :
    ⟪x1 • P + x2 • Q + x3 • R, Q⟫ = x1 * ⟪P, Q⟫ + x2 * ⟪Q, Q⟫ + x3 * ⟪Q, R⟫ := by
  have h := k32e_ip P Q R hPR x1 x2 x3 0 1 0
  simp only [one_smul, zero_smul, add_zero, zero_add] at h
  rw [h]; simp only [k32e_G]; ring

theorem k32e_ipR (P Q R : ℝ³) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (x1 x2 x3 : ℝ) :
    ⟪x1 • P + x2 • Q + x3 • R, R⟫ = x1 * ⟪P, Q⟫ + x2 * ⟪Q, R⟫ + x3 * ⟪R, R⟫ := by
  have h := k32e_ip P Q R hPR x1 x2 x3 0 0 1
  simp only [one_smul, zero_smul, zero_add] at h
  rw [h]; simp only [k32e_G]; ring

/-- Vector-level core of the β6 = 1 corners (1) and (2). -/
theorem k32e_b4_vec (P Q R : ℝ³) (α β γ : ℝ) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (hpp : 0 < ⟪P, P⟫)
    (hqq : ⟪Q, R⟫ < ⟪Q, Q⟫) (hrr : ⟪Q, R⟫ < ⟪R, R⟫)
    (hrel : α * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2))
    (hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2)
    (hα : 1 < α) (hβ : 1 < β) (hσ : β < 1 + γ) (hγ : 0 < γ)
    (hLp : ⟪α • P + (β - 1) • Q + (-γ) • R, α • P + (0:ℝ) • Q + (β - 1) • R⟫ = 0) :
    ⟪α • P + (β - 1) • Q + (-γ) • R, (α - 1) • P + (0:ℝ) • Q + β • R⟫ < 0 ∧
    (⟪α • P + β • Q + (-1 : ℝ) • R,
        ⟪α • P + (β - 1) • Q + (-γ) • R, R⟫ • P - ⟪α • P + (β - 1) • Q + (-γ) • R, P⟫ • R⟫ < 0 →
      0 < -⟪α • P + (β - 1) • Q + (-γ) • R, Q⟫ + (1 - γ) * ⟪α • P + (β - 1) • Q + (-γ) • R, R⟫) := by
  obtain ⟨hs0, hm1, hm3⟩ := k32e_signs α β γ _ _ _ _ _ hα hβ hσ hγ hpp hqq hrr hrel hD
  have em1 : ⟪α • P + (β - 1) • Q + (-γ) • R, P⟫ = α * ⟪P, P⟫ + (β - 1 - γ) * ⟪P, Q⟫ := by
    rw [k32e_ipP P Q R hPR]; ring
  have em3 : ⟪α • P + (β - 1) • Q + (-γ) • R, R⟫ = α * ⟪P, Q⟫ + (β - 1) * ⟪Q, R⟫ - γ * ⟪R, R⟫ := by
    rw [k32e_ipR P Q R hPR]; ring
  have em2 : ⟪α • P + (β - 1) • Q + (-γ) • R, Q⟫ = α * ⟪P, Q⟫ + (β - 1) * ⟪Q, Q⟫ - γ * ⟪Q, R⟫ := by
    rw [k32e_ipQ P Q R hPR]; ring
  have hLp' : α * (α * ⟪P, P⟫ + (β - 1 - γ) * ⟪P, Q⟫) +
      (β - 1) * (α * ⟪P, Q⟫ + (β - 1) * ⟪Q, R⟫ - γ * ⟪R, R⟫) = 0 := by
    have h := hLp
    rw [k32e_ip P Q R hPR] at h; simp only [k32e_G] at h; linear_combination h
  refine ⟨?_, fun hz => ?_⟩
  · rw [k32e_ip P Q R hPR]; simp only [k32e_G]
    nlinarith [hLp', hm1, hm3]
  · rw [em2, em3]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, k32e_ipP P Q R hPR, em3,
      k32e_ipR P Q R hPR, em1] at hz
    exact k32e_core_b4E α β γ _ _ _ _ _ hα hβ hσ hγ hpp hqq hrr hrel hD hLp' (by linarith)

end Type08Sp
end Minimality
