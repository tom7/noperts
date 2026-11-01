module

public import Minimality.Type08S.C2K5LF

@[expose] public section


/-!
# K5L / G: K5e `β1 > 1`: the pentagon `(a, d, c, a', c')` at `b' - c` (frame form)
-/
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

theorem kp_inj {m s β6 β1 α1 : ℝ} (hm : m < 0) (hb6 : 0 < β6) (hβ1 : 1 < β1) (hα1 : 0 < α1) :
    ∀ i j : ZMod 5, kpCyc m s β6 β1 α1 i = kpCyc m s β6 β1 α1 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [kpCyc_0, kpCyc_1, kpCyc_2, kpCyc_3, kpCyc_4] at e1 e2; linarith)

set_option maxHeartbeats 3200000 in
theorem k5e_pent_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {m s β6 β1 α1 : ℝ}
    (hm : m < 0) (hs : 0 < s) (hb6 : 0 < β6) (hβ1 : 1 < β1) (hα1 : α1 = m * (1 - β1)) (hα11 : 1 ≤ α1)
    (hBq : ⟪P, R⟫ = 0) (hPQ : ⟪P, Q⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (kpCyc m s β6 β1 α1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, m, s) ∨ y = fpoint P Q R d (β6, m, s) ∨ y = fpoint P Q R d (β1, α1, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, m, s + 1)) :
    HasLexCellAt V R := by
  have hP0 : P ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hN : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hα10 : 0 < α1 := by linarith
  set N := ⟪P, P⟫ with hNdef
  set pq := ⟪P, Q⟫ with hpq
  have hvP : ∀ v1 v2 : ℝ, ⟪P, fcomb P Q R v1 v2 0⟫ = v1 * N + v2 * pq := by
    intro v1 v2; simp only [fcomb, inner_add_right, real_inner_smul_right, inner_zero_right]; ring
  have hc2 : 2 * N / pq < 0 := div_neg_of_pos_of_neg (by linarith) hPQ
  have hc2' : 2 * N / pq * pq = 2 * N := div_mul_cancel₀ _ hPQ.ne
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kpCyc m s β6 β1 α1) (kp_inj hm hb6 hβ1 hα10) hmem
    [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, m, s + 1)] ?_
    (u1 := -1) (u2 := 2 * N / pq) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < 0 ∧ 0 < ⟪P, fcomb P Q R v1 v2 0⟫) ?_ ?_ ?_
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
    refine ⟨by simp, by simp; linarith, ?_⟩
    rw [hvP]; simp only [mul_zero, add_zero]
    nlinarith
  · intro v1 v2 ⟨hv1, hv2, _⟩
    exact kp_tsc hm hs hb6 hβ1 hα1 hα11 hv1 hv2
  · intro v1 v2 ⟨hv1, hv2, hκ⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    set κ := ⟪P, v⟫ with hκdef
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    refine pent_lexUni _ _ hL (e := ⟪Q, R⟫) (f := ⟪Q, v⟫) (A := ⟪R, R⟫) (wR := ⟪R, v⟫) (m := m) (s := s)
      (α1 := α1) (k1 := β6 * κ) (k2 := β1 * κ) hA hm hs hα11 (mul_pos hb6 hκ) (mul_pos (by linarith) hκ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kpCyc_0, kpCyc_1, kpCyc_2, kpCyc_3, kpCyc_4, inner_fpoint, hBq]
    all_goals first | ring | (rw [hκdef]; ring)

end C2
end Type08Sp
end Minimality
