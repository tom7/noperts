module

public import Minimality.Type08S.C2K31ZA
public import Minimality.Type08S.C2K29ZA

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
open C2

/-- Gram form of a pairing of two frame combinations. -/
def k32e_G (pp s qq qr rr x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  x1*y1*pp + (x1*y2+x2*y1)*s + (x1*y3+x3*y1)*s + x2*y2*qq + (x2*y3+x3*y2)*qr + x3*y3*rr

theorem k32e_ip (P Q R : ℝ³) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • P + x2 • Q + x3 • R, y1 • P + y2 • Q + y3 • R⟫ =
      k32e_G ⟪P, P⟫ ⟪P, Q⟫ ⟪Q, Q⟫ ⟪Q, R⟫ ⟪R, R⟫ x1 x2 x3 y1 y2 y3 := by
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hQP : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial,
    hRP, hRQ, hQP, hPR, k32e_G]
  ring

/-- Signs of the M frame (any β6). -/
theorem k32e_signs (α β γ pp s qq qr rr : ℝ) (hα : 1 < α) (hβ : 1 < β) (hσ : β < 1 + γ)
    (hγ : 0 < γ) (hpp : 0 < pp) (hqq : qr < qq) (hrr : qr < rr)
    (hrel : α * s * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (hD : 0 < qq * rr - qr ^ 2) :
    s < 0 ∧ 0 < α * pp + (β - 1 - γ) * s ∧ α * s + (β - 1) * qr - γ * rr < 0 := by
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have hs : s < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α) hn) hW.le
    nlinarith [mul_pos (sub_pos.2 hβ) hD]
  refine ⟨hs, ?_, ?_⟩
  · nlinarith [mul_pos (by linarith : (0:ℝ) < α) hpp,
      mul_nonneg (by linarith : (0:ℝ) ≤ γ + 1 - β) (by linarith : (0:ℝ) ≤ -s)]
  · rcases le_or_gt 0 qr with h | h
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ γ - (β - 1)) h, mul_pos hγ (sub_pos.2 hrr),
        mul_pos (by linarith : (0:ℝ) < α) (neg_pos.2 hs)]
    · nlinarith [mul_pos (sub_pos.2 hβ) (neg_pos.2 h), mul_pos hγ (by nlinarith : 0 < rr),
        mul_pos (by linarith : (0:ℝ) < α) (neg_pos.2 hs)]

/-- Final inequality. -/
theorem k32e_fin (β γ u v c : ℝ) (hβ : 1 < β) (hγ : 0 < γ) (hu : 0 < u) (hv : 0 < v)
    (hD : 0 < u * v + c * (u + v)) (hq : 0 < (γ - 1) * v * (u + v) - γ * u * v) :
    0 < γ ^ 2 * c * (u + v) + γ * (β - 1) * u * v - (β - 1) * u * (u + v)
      + γ * (γ - 1) * v * (u + v) := by
  have h1 : 0 < (γ - 1) * (u + v) - γ * u := by
    have : 0 < v * ((γ - 1) * (u + v) - γ * u) := by nlinarith
    exact pos_of_mul_pos_right this hv.le
  have h2 : u < (γ - 1) * v := by nlinarith
  have e : γ ^ 2 * c * (u + v) + γ * (β - 1) * u * v - (β - 1) * u * (u + v)
      + γ * (γ - 1) * v * (u + v) = γ ^ 2 * (u * v + c * (u + v)) + (β - 1) * u * (γ * v - (u + v))
      + γ * v * ((γ - 1) * (u + v) - γ * u) := by ring
  rw [e]
  have h3 : 0 < (β - 1) * u * (γ * v - (u + v)) := by
    have : 0 < γ * v - (u + v) := by linarith
    positivity
  have h4 : 0 < γ * v * ((γ - 1) * (u + v) - γ * u) := by positivity
  have h5 : 0 ≤ γ ^ 2 * (u * v + c * (u + v)) := by positivity
  linarith

set_option maxHeartbeats 2000000 in
/-- Core of the `Lz`/`hE` identities (β6 = 1). -/
theorem k32e_core_b4E (α β γ pp s qq qr rr : ℝ) (hα : 1 < α) (hβ : 1 < β) (hσ : β < 1 + γ)
    (hγ : 0 < γ) (hpp : 0 < pp) (hqq : qr < qq) (hrr : qr < rr)
    (hrel : α * s * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (hD : 0 < qq * rr - qr ^ 2)
    (hLp : α * (α * pp + (β - 1 - γ) * s) + (β - 1) * (α * s + (β - 1) * qr - γ * rr) = 0)
    (hz : (α * s + (β - 1) * qr - γ * rr) * (α * pp + (β - 1) * s)
        - (α * pp + (β - 1 - γ) * s) * (α * s + β * qr - rr) < 0) :
    0 < -(α * s + (β - 1) * qq - γ * qr) + (1 - γ) * (α * s + (β - 1) * qr - γ * rr) := by
  obtain ⟨hs0, hm1, hm3⟩ := k32e_signs α β γ pp s qq qr rr hα hβ hσ hγ hpp hqq hrr hrel hD
  have hu0 : 0 < qq - qr := by linarith
  have hv0 : 0 < rr - qr := by linarith
  have hα0 : α ≠ 0 := by linarith
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have hWne : qq + rr - 2 * qr ≠ 0 := hW.ne'
  have hsE : s = -(β - 1) * (qq * rr - qr ^ 2) / (α * (qq + rr - 2 * qr)) := by
    rw [eq_div_iff (by positivity)]; linear_combination hrel
  have hppE : pp = (-(β - 1) * (α * s + (β - 1) * qr - γ * rr) - α * (β - 1 - γ) * s) / α ^ 2 := by
    rw [eq_div_iff (by positivity)]; linear_combination hLp
  have hid : (α * (qq + rr - 2 * qr)) * ((α * s + (β - 1) * qr - γ * rr) * (α * pp + (β - 1) * s)
        - (α * pp + (β - 1 - γ) * s) * (α * s + β * qr - rr))
      = (α * s + (β - 1) * qr - γ * rr) * (β - 1) *
        ((γ - 1) * (rr - qr) * (qq + rr - 2 * qr) - γ * (qq - qr) * (rr - qr)) := by
    rw [hppE, hsE]; field_simp; ring
  have hEid : (-(α * s + (β - 1) * qq - γ * qr) + (1 - γ) * (α * s + (β - 1) * qr - γ * rr)) * (qq + rr - 2 * qr)
      = γ ^ 2 * qr * (qq + rr - 2 * qr) + γ * (β - 1) * (qq - qr) * (rr - qr)
        - (β - 1) * (qq - qr) * (qq + rr - 2 * qr)
        + γ * (γ - 1) * (rr - qr) * (qq + rr - 2 * qr) := by
    linear_combination (-γ) * hrel
  have hq : 0 < (γ - 1) * (rr - qr) * (qq + rr - 2 * qr) - γ * (qq - qr) * (rr - qr) := by
    by_contra hn; push Not at hn
    have h1 : 0 ≤ (β - 1) * (-((γ - 1) * (rr - qr) * (qq + rr - 2 * qr) - γ * (qq - qr) * (rr - qr))) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (α * (qq + rr - 2 * qr)) * ((α * s + (β - 1) * qr - γ * rr) * (α * pp + (β - 1) * s)
        - (α * pp + (β - 1 - γ) * s) * (α * s + β * qr - rr)) := by
      rw [hid]; nlinarith [mul_nonneg (neg_nonneg.2 hm3.le) h1]
    nlinarith [mul_pos (by linarith : (0:ℝ) < α) hW]
  have hD' : 0 < (qq - qr) * (rr - qr) + qr * ((qq - qr) + (rr - qr)) := by nlinarith
  have hf := k32e_fin β γ (qq - qr) (rr - qr) qr hβ hγ hu0 hv0 hD'
    (by have e : (qq - qr) + (rr - qr) = qq + rr - 2 * qr := by ring
        rw [e]; exact hq)
  have e2 : (qq - qr) + (rr - qr) = qq + rr - 2 * qr := by ring
  rw [e2] at hf
  have : 0 < (-(α * s + (β - 1) * qq - γ * qr) + (1 - γ) * (α * s + (β - 1) * qr - γ * rr)) * (qq + rr - 2 * qr) := by
    rw [hEid]; linarith
  exact pos_of_mul_pos_left this hW.le
end Type08Sp
end Minimality
