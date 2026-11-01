module

public import Minimality.Type08S.C2K5FK

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5f_E1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hζ : -t * m * ⟪P, R⟫ + ⟪Q, R⟫ - t * k * ⟪R, R⟫ < -m * ⟪P, R⟫ - k * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
      y = fpoint P Q R d (-t * m, 1, -t * k) ∨ y = fpoint P Q R d (-m, 0, -k) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, -1) ∨ y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hs : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hmγ : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk (sub_pos.2 hγ4)]
  have hinjX : ∀ i j, k5fE1Cyc m k t α4 γ4 i = k5fE1Cyc m k t α4 γ4 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k5fE1Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k5fE1Cyc m k t α4 γ4) hinjX hmem
    [(1, 0, -1), (0, 1, 0)] ?_ (u1 := -1) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => v1 < 0 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fE1Cyc, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k5fE1Cyc, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k5fE1Cyc, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k5fE1Cyc, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k5fE1Cyc, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    exact ⟨k5f_E1_cyc hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2, k5f_E1_rest hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2⟩
  · intro v1 v2 hv hsep
    exact k5f_E1_lex P Q R d hm hk hk1 ht ht1 hα4 hγ4 hrel hs hζ _ hsep

theorem k5f_E2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hζ : -m * ⟪P, R⟫ - k * ⟪R, R⟫ < -t * m * ⟪P, R⟫ + ⟪Q, R⟫ - t * k * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, -1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
      y = fpoint P Q R d (-t * m, 1, -t * k) ∨ y = fpoint P Q R d (-m, 0, -k) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hs : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hmγ : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk (sub_pos.2 hγ4)]
  have hinjX : ∀ i j, k5fE2Cyc m k t α4 γ4 i = k5fE2Cyc m k t α4 γ4 j → i = j := by
    intro i j h
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [k5fE2Cyc_0, k5fE2Cyc_1, k5fE2Cyc_2, k5fE2Cyc_3, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k5fE2Cyc m k t α4 γ4) hinjX hmem
    [(1, 0, 0), (0, 0, 0), (0, 1, 0)] ?_ (u1 := 1) (u2 := -1) (t1 := -1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => 0 < v1 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fE2Cyc_0]⟩
    · exact Or.inl ⟨1, by simp [k5fE2Cyc_1]⟩
    · exact Or.inl ⟨2, by simp [k5fE2Cyc_2]⟩
    · exact Or.inl ⟨3, by simp [k5fE2Cyc_3]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    exact ⟨k5f_E2_cyc hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2, k5f_E2_rest hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2⟩
  · intro v1 v2 hv hsep
    exact k5f_E2_lex P Q R d hm hk hk1 ht ht1 hα4 hγ4 hrel hs hζ _ hsep

end C2
end Type08Sp
end Minimality
