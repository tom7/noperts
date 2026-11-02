module

public import Minimality.Type08S.C2K6MK

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6mH1_inj {κ σ α1 β1 β6 γ6 : ℝ} (hκ : κ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k6mHCyc1 κ σ α1 β1 β6 γ6 i = k6mHCyc1 κ σ α1 β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have m1 : κ * α1 < 0 := by nlinarith
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k6mHCyc1_0, k6mHCyc1_1, k6mHCyc1_2, k6mHCyc1_3, k6mHCyc1_4] at e1 e2; nlinarith)

theorem k6mH2_inj {κ σ α1 β1 β6 γ6 : ℝ} (hκ : κ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 4, k6mHCyc2 κ σ α1 β1 β6 γ6 i = k6mHCyc2 κ σ α1 β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have m1 : κ * α1 < 0 := by nlinarith
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k6mHCyc2_0, k6mHCyc2_1, k6mHCyc2_2, k6mHCyc2_3] at e1 e2; nlinarith)

set_option maxHeartbeats 3200000 in
/-- H2 cell 1 (frame form): pentagon `(a, c', a', c, d)`; the depth order data is a hypothesis. -/
theorem k6m_hc1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 γ6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hbc : 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1))
    (hcc : 0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1))
    (haa : 0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hmem : ∀ i, fpoint P Q R d (k6mHCyc1 κ σ α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1))
    (h23 : ⟪fpoint P Q R d (β6, γ6, 0), R⟫ < ⟪fpoint P Q R d (0, 1, 0), R⟫)
    (h34 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫)
    (h : ⟪fpoint P Q R d (β1, κ * α1, α1 * σ), R⟫ < ⟪fpoint P Q R d (0, κ, σ), R⟫ ∨
      ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (0, κ, σ), R⟫) :
    HasLexCellAt V R := by
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k6mHCyc1 κ σ α1 β1 β6 γ6)
    (k6mH1_inj hκ hα1 hβ1 hb6 hγ6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
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
    exact k6m_hc1_tsc hκ hσ hα1 hβ1 hb6 hγ6 hγ61 hbc hcc haa hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    refine k6m_pent_uni _ _ hL ?_ ?_ ?_
    · simpa only [k6mHCyc1_2, k6mHCyc1_3] using h23
    · simpa only [k6mHCyc1_3, k6mHCyc1_4] using h34
    · simpa only [k6mHCyc1_0, k6mHCyc1_1, k6mHCyc1_4] using
        (show _ ∨ _ ∨ _ from h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h)))

set_option maxHeartbeats 3200000 in
/-- H2 cell 2 (frame form): quadrilateral `(b', c', a', c)`. -/
theorem k6m_hc2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 γ6 : ℝ}
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
    (h32 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (β6, γ6, 0), R⟫) :
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
    refine k6m_quad_uni _ _ hL ?_ ?_
    · simpa only [k6mHCyc2_0, k6mHCyc2_1] using h01
    · simpa only [k6mHCyc2_2, k6mHCyc2_3] using h32

end C2
end Type08Sp
end Minimality
