module

public import Minimality.Type08S.C2K6TDA

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
/-- Cell 1 at the depth tie `⟪P,R⟫ = 0` with `ζ(c',c) > 0` (`cz < α1 (κ cz + σ A)`) and `a, d` not tied: pentagon `(a,c',a',c,d)`,
tilt line `(1, λ)`; no sign condition on `⟪P, v⟫`. -/
theorem k6t4_qtc1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0)
    (hZ : κ * ⟪Q, R⟫ + σ * ⟪R, R⟫ ≠ 0) (hζ : ⟪Q, R⟫ < α1 * (κ * ⟪Q, R⟫ + σ * ⟪R, R⟫))
    (hmem : ∀ i, fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
    (k6t1_km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
    (u1 := 1) (u2 := 0) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2) ?_ ?_ ?_
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
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one]
    nlinarith [mul_pos nk a1, mul_pos hβ1 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact k6t1_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    refine k6t4_pent1_lexUni _ _ hL (κ := κ) (σ := σ) (α1 := α1) (β1 := β1) (β6 := β6) (bz := ⟪P, R⟫)
      (bw := ⟪P, v⟫) (cz := ⟪Q, R⟫) (cw := ⟪Q, v⟫) (A := ⟪R, R⟫) (uw := ⟪R, v⟫) hBz hA hκ hσ hα1 hβ1
      (by linarith) hZ hζ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, inner_fpoint]
    all_goals ring

set_option maxHeartbeats 3200000 in
/-- Cell 2 at the depth tie `⟪P,R⟫ = 0` with `ζ(c',c) < 0`: quadrilateral `(b', c', a', c)`, tilt line `(-1, -λ)`. -/
theorem k6t4_qtc2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0)
    (hζ : α1 * (κ * ⟪Q, R⟫ + σ * ⟪R, R⟫) < ⟪Q, R⟫)
    (hmem : ∀ i, fpoint P Q R d (kmCyc2 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ - 1) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, κ, σ) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (kmCyc2 κ σ α1 β1 β6)
    (k6t1_km2_inj hκ hα1 hβ1 hb6) hmem [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)] ?_
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ β1 * v2 < κ * (α1 - 1) * v1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
    nlinarith [mul_pos nk a1, mul_pos hβ1 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact k6t1_km2_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    obtain ⟨s0, s1, s2, s3⟩ := z4_add
    refine k6t4_quad2_lexUni _ _ hL (zd := ⟪d, R⟫) (wd := ⟪d, v⟫) (κ := κ) (σ := σ) (α1 := α1) (β1 := β1)
      (β6 := β6) (bz := ⟪P, R⟫) (bw := ⟪P, v⟫) (cz := ⟪Q, R⟫) (cw := ⟪Q, v⟫) (A := ⟪R, R⟫) (uw := ⟪R, v⟫)
      hBz hA hκ hσ hα1 hβ1 (by linarith) hE hζ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, inner_fpoint]
    all_goals ring

end C2
end Type08Sp
end Minimality
