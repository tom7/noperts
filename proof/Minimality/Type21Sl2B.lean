module

public import Minimality.Type21Sl2A

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

theorem h21b_cross_ne {A B u v w : ℝ³} (hu : h21b_LP ⟪A, u⟫ ⟪A, v⟫)
    (hd : h21b_LP (-⟪B, u⟫) (-⟪B, v⟫))
    (hA : ⟪A, w⟫ ≤ 0) (hB : ⟪B, w⟫ ≤ 0) (hs : ⟪A, w⟫ < 0 ∨ ⟪B, w⟫ < 0) :
    cross A B ≠ 0 := by
  intro h
  have h1 := h21_binet A B u w
  have h2 := h21_binet A B v w
  rw [h] at h1 h2
  simp only [inner_zero_left] at h1 h2
  have := h21b_Q_scalar hA hB hs hu hd
  unfold h21b_LP at this
  rcases this with h | ⟨h, h'⟩ <;> nlinarith

theorem h21b_det_eq (D : h21b_SilDataL k x c u₀ v) (i : ZMod k) (μ : ℝ)
    (hd : x (c (i + 1)) - x (c i) = μ • cross (D.A i) (D.B i)) (m : Fin n) (w : ℝ³) :
    det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) w =
      μ * (D.fA i (x m) * ⟪D.B i, w⟫ - D.fB i (x m) * ⟪D.A i, w⟫) := by
  rw [h21_bracket (D.A i) (D.B i) _ _ _ _ μ hd]
  have e1 := D.hA i (x m) (x (c i))
  have e2 := D.hB i (x m) (x (c i))
  rw [D.zA0] at e1; rw [D.zB0] at e2
  rw [← e1, ← e2]; ring_nf

theorem h21b_exists_mu (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v) (i : ZMod k) :
    ∃ μ : ℝ, μ ≠ 0 ∧ x (c (i + 1)) - x (c i) = μ • cross (D.A i) (D.B i) := by
  obtain ⟨h1, h2⟩ := zmod_ne hk
  have n1 : c (i + 2) ≠ c i := fun h => h2 (by simpa using hc h)
  have n2 : c (i + 2) ≠ c (i + 1) := fun h => h1 (by
    have := hc h; linear_combination this)
  have hcr : cross (D.A i) (D.B i) ≠ 0 := by
    refine h21b_cross_ne (w := x (c (i + 2)) - x (c i)) (D.up i) (D.dn i) ?_ ?_ ?_
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

theorem h21b_lp_sign {μ μ' a b a' b' : ℝ} (h1 : h21b_LP a b) (h2 : h21b_LP a' b')
    (e0 : μ * a = μ' * a') (e1 : μ * b = μ' * b') (hμ : 0 < μ) (hμ' : μ' ≠ 0) : 0 < μ' := by
  by_contra hn
  have hn' : μ' < 0 := lt_of_le_of_ne (not_lt.1 hn) hμ'
  unfold h21b_LP at h1 h2
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · nlinarith [mul_pos hμ h1, mul_neg_of_neg_of_pos hn' h2]
  · subst h2; nlinarith [mul_pos hμ h1]
  · subst h1; nlinarith [mul_neg_of_neg_of_pos hn' h2]
  · subst h1; subst h2; nlinarith [mul_pos hμ h1', mul_neg_of_neg_of_pos hn' h2']

end H21
end Minimality
