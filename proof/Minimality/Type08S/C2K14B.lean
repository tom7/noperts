module

public import Minimality.Type08S.C2K14A

@[expose] public section


/-!
# K14 / B: frame cells of the H2 tie (`ζ_{a-b'}(c, a') = 0`, `ζ_{a-b'}(c', a') ≠ 0`)
Pentagon `(a, c', a', c, d)` when `a' < c'` (tilt chosen with `c <lex a'`), quadrilateral `(b', c', a', c)` when `c' < a'`.
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

set_option maxHeartbeats 3200000 in
/-- Pentagon cell of the H2 tie: `ζ(c, a') = 0`, `a' < c'` at the view `R`; the tilt makes `c <lex a'`. -/
theorem k14_hc1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 γ6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hbc : 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1))
    (hcc : 0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1))
    (haa : 0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hmem : ∀ i, fpoint P Q R d (k6mHCyc1 κ σ α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1))
    (htie : ⟪fpoint P Q R d (0, 1, 0), R⟫ = ⟪fpoint P Q R d (β6, γ6, 0), R⟫)
    (hl0 : ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0),
      fcomb P Q R 1 (κ * (α1 - 1) / β1) 0⟫ < 0)
    (h21 : ⟪fpoint P Q R d (β6, γ6, 0), R⟫ < ⟪fpoint P Q R d (β1, κ * α1, α1 * σ), R⟫)
    (h34 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫)
    (h : ⟪fpoint P Q R d (β1, κ * α1, α1 * σ), R⟫ < ⟪fpoint P Q R d (0, κ, σ), R⟫ ∨
      ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (0, κ, σ), R⟫) :
    HasLexCellAt V R := by
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  set m0 : ℝ := κ * (α1 - 1) / β1 with hm0
  have hβm : β1 * m0 = κ * (α1 - 1) := by rw [hm0]; field_simp
  set B : ℝ := ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), Q⟫ with hB
  have hε : 0 < -⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R 1 m0 0⟫ / (|B| + 1) := by
    apply div_pos (by linarith) (by positivity)
  have hlin : ∀ lam : ℝ, ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R 1 (m0 + lam) 0⟫ =
      ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R 1 m0 0⟫ + lam * B := by
    intro lam
    have : fcomb P Q R 1 (m0 + lam) 0 = fcomb P Q R 1 m0 0 + lam • Q := by simp only [fcomb]; module
    rw [this, inner_add_right, inner_smul_right]
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k6mHCyc1 κ σ α1 β1 β6 γ6)
    (k6mH1_inj hκ hα1 hβ1 hb6 hγ6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
    (u1 := 1) (u2 := m0) (t1 := 0) (t2 := 1) (lo := 0)
    (hi := -⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R 1 m0 0⟫ / (|B| + 1))
    (by norm_num) hε
    (fun v1 v2 => (0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2) ∧
      ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R v1 v2 0⟫ < 0) ?_ ?_ ?_
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
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨⟨by norm_num, ?_⟩, ?_⟩
    · nlinarith [mul_pos hβ1 h0]
    · rw [hlin]
      set L0 := ⟪fpoint P Q R d (0, 1, 0) - fpoint P Q R d (β6, γ6, 0), fcomb P Q R 1 m0 0⟫
      have h1' : lam * (|B| + 1) < -L0 := by
        have := (lt_div_iff₀ (by positivity : (0:ℝ) < |B| + 1)).1 h1
        linarith
      have : lam * B ≤ lam * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) h0.le
      nlinarith
  · intro v1 v2 ⟨⟨hv1, hc⟩, hl⟩
    exact k6m_hc1_tsc hκ hσ hα1 hβ1 hb6 hγ6 hγ61 hbc hcc haa hE hv1 hc
  · intro v1 v2 ⟨⟨hv1, hc⟩, hl⟩ hL
    refine k14_pent_uni _ _ hL ?_ ?_ ?_ ?_
    · simp only [k6mHCyc1_2, k6mHCyc1_3, LexLt]
      right
      refine ⟨htie, ?_⟩
      have := hl
      rw [inner_sub_left] at this
      linarith
    · simpa only [k6mHCyc1_1, k6mHCyc1_2] using h21
    · simpa only [k6mHCyc1_3, k6mHCyc1_4] using h34
    · simpa only [k6mHCyc1_0, k6mHCyc1_1, k6mHCyc1_4] using h

set_option maxHeartbeats 3200000 in
/-- Quadrilateral cell of the H2 tie: `b' < c' < a'` at the view `R` (no tie input). -/
theorem k14_hc2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 γ6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hbc : 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1))
    (hcc : 0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1))
    (haa : 0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hmem : ∀ i, fpoint P Q R d (k6mHCyc2 κ σ α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ - 1) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, κ, σ) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0))
    (h01 : ⟪fpoint P Q R d (0, κ, σ - 1), R⟫ < ⟪fpoint P Q R d (β1, κ * α1, α1 * σ), R⟫)
    (h12 : ⟪fpoint P Q R d (β1, κ * α1, α1 * σ), R⟫ < ⟪fpoint P Q R d (β6, γ6, 0), R⟫) :
    HasLexCellAt V R := by
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k6mHCyc2 κ σ α1 β1 β6 γ6)
    (k6mH2_inj hκ hα1 hβ1 hb6 hγ6) hmem [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)] ?_
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
    exact k6m_hc2_tsc hκ hσ hα1 hβ1 hb6 hγ6 hγ61 hbc hcc haa hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    refine k14_quad_uni _ _ hL ?_ ?_
    · simpa only [k6mHCyc2_0, k6mHCyc2_1] using h01
    · simpa only [k6mHCyc2_1, k6mHCyc2_2] using h12

end C2
end Type08Sp
end Minimality
