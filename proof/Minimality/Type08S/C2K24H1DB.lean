module

public import Minimality.Type08S.C2K24H1DA
public import Minimality.Type08S.C2K19C
public import Minimality.Type08S.C2K14D

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k24h1d_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  set u : ℝ³ := ⟪R, R⟫ • Q - ⟪Q, R⟫ • R with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hΔ
    have hQ : Q = (⟪Q, R⟫ / ⟪R, R⟫) • R := by
      have : ⟪R, R⟫ • Q = ⟪Q, R⟫ • R := sub_eq_zero.1 h0
      rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hRR.ne', one_smul]
    rw [hQ]; simp [det3_expand]; ring
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu0
  have e : ⟪u, u⟫ = ⟪R, R⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by
    simp only [hu, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm R Q]; ring
  rw [e] at huu
  nlinarith [(mul_pos_iff_of_pos_left hRR).1 huu]

/-- Real core of cell D: the four depth inequalities and `U1 > 0`. -/
theorem k24h1d_core {α1 β1 β6 γ6 pp qq rr s t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hγ6 : 1 < γ6) (hs : s < 0) (hA : t < qq) (hB : t < rr) (hqq : 0 < qq)
    (hrel : α1 * s * (qq + rr - 2 * t) = -(β1 - 1) * (qq * rr - t ^ 2))
    (htie : (α1 - 1) * s * (β6 + γ6 - 1) + β1 * (γ6 - 1) * rr + β1 * β6 * t = 0)
    (hN : -(α1 - 1) * (β6 - β1) * s - (α1 - 1) * γ6 * s + (α1 - 1) * α1 * pp - β1 * (β6 - β1) * t
      - β1 * γ6 * rr + β1 * α1 * s = 0)
    (hW : γ6 * (rr - t) - (β6 - β1) * (qq - t) ≤ 0) :
    0 < -(α1 - 1) * s - β1 * t ∧
    (-(α1 - 1) * β6 * s - (α1 - 1) * (γ6 - β1) * s + (α1 - 1) * α1 * pp - β1 * β6 * qq
      - β1 * (γ6 - β1) * t + β1 * α1 * s < 0) ∧
    (-(α1 - 1) * (β6 - 1) * s - (α1 - 1) * γ6 * s - β1 * (β6 - 1) * qq - β1 * γ6 * t < 0) ∧
    0 < β1 * qq + (α1 - 1) * s ∧ 0 < (α1 - 1) * pp + β1 * s := by
  have hS : 0 < β6 + γ6 - 1 := by linarith
  have hA' : 0 < qq - t := by linarith
  have hB' : 0 < rr - t := by linarith
  have hb0 : 0 < β1 := by linarith
  have hm : 0 < α1 - 1 := by linarith
  have k1 : (β6 + γ6 - 1) * ((α1 - 1) * s + β1 * t) = -(β1 * (γ6 - 1) * (rr - t)) := by
    linear_combination htie
  have hBpos : 0 < β1 * (γ6 - 1) * (rr - t) := mul_pos (mul_pos hb0 (by linarith)) hB'
  have key1 : (α1 - 1) * s + β1 * t < 0 := by
    by_contra h; push Not at h
    have := mul_nonneg hS.le h
    linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · have e : -(α1 - 1) * β6 * s - (α1 - 1) * (γ6 - β1) * s + (α1 - 1) * α1 * pp - β1 * β6 * qq
      - β1 * (γ6 - β1) * t + β1 * α1 * s = β1 * (γ6 * (rr - t) - β6 * (qq - t)) := by
      linear_combination hN
    rw [e]
    have : γ6 * (rr - t) - β6 * (qq - t) < 0 := by nlinarith
    nlinarith
  · have e : -(α1 - 1) * (β6 - 1) * s - (α1 - 1) * γ6 * s - β1 * (β6 - 1) * qq - β1 * γ6 * t
        = -((β6 + γ6 - 1) * ((α1 - 1) * s + β1 * t)) - β1 * (β6 - 1) * (qq - t) := by ring
    rw [e, k1]
    have : (γ6 - 1) * (rr - t) < (β6 - 1) * (qq - t) := by nlinarith [mul_pos (sub_pos.2 hβ1) hA']
    nlinarith
  · have hW2 : 0 < qq + rr - 2 * t := by linarith
    have hDlt : qq * rr - t ^ 2 < qq * (qq + rr - 2 * t) := by nlinarith [mul_pos hA' hA']
    have e : α1 * (β1 * qq + (α1 - 1) * s) * (qq + rr - 2 * t) =
        α1 * β1 * qq * (qq + rr - 2 * t) - (α1 - 1) * (β1 - 1) * (qq * rr - t ^ 2) := by
      linear_combination (α1 - 1) * hrel
    have h2 : (α1 - 1) * (β1 - 1) * (qq * rr - t ^ 2) < (α1 - 1) * (β1 - 1) * (qq * (qq + rr - 2 * t)) :=
      mul_lt_mul_of_pos_left hDlt (mul_pos hm (by linarith))
    have h3 : 0 < α1 * (β1 * qq + (α1 - 1) * s) * (qq + rr - 2 * t) := by
      rw [e]
      have : 0 < qq * (qq + rr - 2 * t) * (β1 + (α1 - 1)) := mul_pos (mul_pos hqq hW2) (by linarith)
      nlinarith
    have h4 : 0 < α1 * (qq + rr - 2 * t) := mul_pos (by linarith) hW2
    nlinarith
  · have k2 : (β6 + γ6 - 1) * α1 * ((α1 - 1) * pp + β1 * s) =
        β1 * (rr - t) * (β1 * (γ6 - 1) + β6) := by
      linear_combination (β6 + γ6 - 1) * hN + (β6 + γ6 - β1) * htie
    have : 0 < β1 * (rr - t) * (β1 * (γ6 - 1) + β6) :=
      mul_pos (mul_pos hb0 hB') (by nlinarith)
    rw [← k2] at this
    have h5 : 0 < (β6 + γ6 - 1) * α1 := mul_pos hS (by linarith)
    by_contra h; push Not at h
    have := mul_nonpos_of_nonneg_of_nonpos h5.le h
    linarith

end C2
end Type08Sp
end Minimality
