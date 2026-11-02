module

public import Minimality.Type08S.C2K6TAG

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

set_option maxHeartbeats 3200000 in
/-- Cell 1 at the depth tie `⟪P,R⟫ = 0` with a feasible tilt (`hfeas`): pentagon `(a, c', a', c, d)`. -/
theorem k6t1_tie1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0)
    (hfeas : ∃ u1 u2 : ℝ, 0 < u1 ∧ κ * (α1 - 1) * u1 < β1 * u2 ∧ u2 ≠ 0 ∧ u1 * ⟪P, P⟫ + u2 * ⟪P, Q⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  obtain ⟨u1, u2, hu1, hu2c, hu2, hus⟩ := hfeas
  have hP0 : P ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hDb : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  obtain ⟨η, hη⟩ : ∃ η, η = -(u1 * ⟪P, P⟫ + u2 * ⟪P, Q⟫) / (2 * ⟪P, P⟫) := ⟨_, rfl⟩
  have hηp : 0 < η := by rw [hη]; apply div_pos <;> linarith
  have hηD : η * ⟪P, P⟫ = -(u1 * ⟪P, P⟫ + u2 * ⟪P, Q⟫) / 2 := by rw [hη]; field_simp
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
    (k6t1_km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
    (u1 := u1) (u2 := u2) (t1 := η) (t2 := 0) (lo := 0) (hi := 1)
    (by simp only [mul_zero, zero_sub, ne_eq, neg_mul]; rw [neg_eq_zero]; exact mul_ne_zero hu2 hηp.ne') (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2 ∧ v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by nlinarith, ?_, ?_⟩
    · simp only [mul_zero, add_zero]
      nlinarith [mul_pos nk a1, mul_pos hηp h0, mul_pos (mul_pos nk a1) (mul_pos hηp h0)]
    · simp only [mul_zero, add_zero]
      nlinarith [mul_pos hηp h0, mul_pos (mul_pos hηp h0) hDb]
  · intro v1 v2 hvv
    obtain ⟨hv1, hc, -⟩ := hvv
    exact k6t1_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · intro v1 v2 ⟨hv1, hc, hbw⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    have hbw' : ⟪P, v⟫ = v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ := by
      rw [real_inner_comm, hv, inner_fcomb_left]; simp; left; exact real_inner_comm P Q
    refine k6t1_pent1_lexUni _ _ hL (κ := κ) (σ := σ) (α1 := α1) (β1 := β1) (β6 := β6) (bz := ⟪P, R⟫)
      (bw := ⟪P, v⟫) (cz := ⟪Q, R⟫) (cw := ⟪Q, v⟫) (A := ⟪R, R⟫) (uw := ⟪R, v⟫) (Or.inr ⟨by rw [hBz]; simp, by rw [hbw']; linarith⟩) hA hκ hσ hα1.le hβ1
      (by linarith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, inner_fpoint]
    all_goals ring


end C2
end Type08Sp
end Minimality
