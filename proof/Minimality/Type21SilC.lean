module

public import Minimality.Type21SilB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ : ℝ³}

theorem zmod_ne (hk : 3 ≤ k) : (1 : ZMod k) ≠ 0 ∧ (2 : ZMod k) ≠ 0 := by
  constructor
  · intro h
    have h' : ((1 : ℕ) : ZMod k) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd one_pos h'; omega
  · intro h
    have h' : ((2 : ℕ) : ZMod k) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'; omega

theorem Q_pos (D : SilData k x c u₀) (i : ZMod k) (m : Fin n) (h0 : m ≠ c i) (h1 : m ≠ c (i + 1)) :
    0 < D.fA i (x m) * ⟪D.B i, u₀⟫ - D.fB i (x m) * ⟪D.A i, u₀⟫ := by
  have a := D.nA i m
  have b := D.nB i m
  have hu := D.up i
  have hv := D.dn i
  rcases D.strict i m h0 h1 with h | h <;> nlinarith [mul_pos_of_neg_of_neg h hv, mul_nonneg_of_nonpos_of_nonpos a hv.le,
    mul_nonpos_of_nonpos_of_nonneg b hu.le, mul_neg_of_neg_of_pos h hu]

theorem det_eq (D : SilData k x c u₀) (i : ZMod k) (μ : ℝ)
    (hd : x (c (i + 1)) - x (c i) = μ • cross (D.A i) (D.B i)) (m : Fin n) :
    det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u₀ =
      μ * (D.fA i (x m) * ⟪D.B i, u₀⟫ - D.fB i (x m) * ⟪D.A i, u₀⟫) := by
  rw [h21_bracket (D.A i) (D.B i) _ _ _ _ μ hd]
  have e1 := D.hA i (x m) (x (c i))
  have e2 := D.hB i (x m) (x (c i))
  rw [D.zA0] at e1; rw [D.zB0] at e2
  rw [← e1, ← e2]; ring_nf

theorem exists_mu (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (i : ZMod k) :
    ∃ μ : ℝ, μ ≠ 0 ∧ x (c (i + 1)) - x (c i) = μ • cross (D.A i) (D.B i) := by
  obtain ⟨h1, h2⟩ := zmod_ne hk
  have n1 : c (i + 2) ≠ c i := fun h => h2 (by simpa using hc h)
  have n2 : c (i + 2) ≠ c (i + 1) := fun h => h1 (by
    have := hc h; linear_combination this)
  have hcr : cross (D.A i) (D.B i) ≠ 0 := by
    refine h21_cross_ne (w := x (c (i + 2)) - x (c i)) (D.up i) (D.dn i) ?_ ?_ ?_
    · rw [← D.hA i, D.zA0]; simpa using D.nA i _
    · rw [← D.hB i, D.zB0]; simpa using D.nB i _
    · rw [← D.hA i, ← D.hB i, D.zA0, D.zB0]; simpa using D.strict i _ n1 n2
  have hdne : x (c (i + 1)) - x (c i) ≠ 0 := by
    intro h
    have := hc (hx (sub_eq_zero.1 h))
    exact h1 (by simpa using this)
  obtain ⟨μ, hμ⟩ := h21_mul_cross hcr (d := x (c (i + 1)) - x (c i))
    (by have := D.hA i (x (c (i + 1))) (x (c i)); rw [D.zA1, D.zA0, sub_zero] at this; exact this.symm)
    (by have := D.hB i (x (c (i + 1))) (x (c i)); rw [D.zB1, D.zB0, sub_zero] at this; exact this.symm)
  refine ⟨μ, ?_, hμ⟩
  rintro rfl
  rw [zero_smul] at hμ
  exact hdne hμ

end H21
end Minimality
