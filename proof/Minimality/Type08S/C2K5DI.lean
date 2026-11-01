module

public import Minimality.Type08S.C2K5DH
public import Minimality.Type08S.C2K5DF

@[expose] public section


/-!
# K5d / I: cores and frame lemmas for cells 3, 4, 5/8, 6
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

theorem k5d_c4_core (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg61 : γ6 < 1) (hα41 : α4 < 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX4 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6))
    (horc : ∀ k0 U T B : ℝ,
      (∀ s ∈ k5dL α4 γ4 β1 β6 γ6, ∀ t ∈ k5dL α4 γ4 β1 β6 γ6,
        s.1 * ⟪P, R⟫ + s.2.1 * ⟪Q, R⟫ + s.2.2 * ⟪R, R⟫ < t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (k5dX4 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 i).2.2 * B =
        k0 + (k5dX4 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX4 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 i).2.2 * B)) :
    HasLexCellAt V R := by
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k5dX4 α4 γ4 β1 β6 γ6) ?_ hmem
    [(0, γ6, -β6), (0, 0, -1)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧ 0 < γ4 * v1 + (1 - α4) * v2) ?_ ?_
    (k5dL α4 γ4 β1 β6 γ6) ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨by norm_num, by linarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨hv1, hv2, hc1⟩ := hv
    exact k5dX4_tsc hα4 hγ4 hs hβ1 hb6 hγ6 hg61 hv1 hv2 hc1
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    exact horc k0 U T B hfw hinj

theorem k5d_c3_core (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg61 : γ6 < 1) (hbg : 1 < β6 + γ6) (hα41 : α4 < 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX3 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6))
    (horc : ∀ k0 U T B : ℝ,
      (∀ s ∈ k5dL α4 γ4 β1 β6 γ6, ∀ t ∈ k5dL α4 γ4 β1 β6 γ6,
        s.1 * ⟪P, R⟫ + s.2.1 * ⟪Q, R⟫ + s.2.2 * ⟪R, R⟫ < t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (k5dX3 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 i).2.2 * B =
        k0 + (k5dX3 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX3 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 i).2.2 * B)) :
    HasLexCellAt V R := by
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  refine k5d_cell V P Q R d hΔ (k := 6) (by norm_num) (k5dX3 α4 γ4 β1 β6 γ6) ?_ hmem
    [(1, 0, -β1)] ?_
    (u1 := -1) (u2 := 1) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ 0 < v2 ∧ γ4 * v1 + (1 - α4) * v2 < 0) ?_ ?_
    (k5dL α4 γ4 β1 β6 γ6) ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
    refine ⟨by linarith, by linarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨hv1, hv2, hc1⟩ := hv
    exact k5dX3_tsc hα4 hγ4 hs hβ1 hb6 hγ6 hg61 hbg hv1 hv2 hc1
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    exact horc k0 U T B hfw hinj

theorem k5d_c5_core (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX5 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6))
    (horc : ∀ k0 U T B : ℝ,
      (∀ s ∈ k5dL α4 γ4 β1 β6 γ6, ∀ t ∈ k5dL α4 γ4 β1 β6 γ6,
        s.1 * ⟪P, R⟫ + s.2.1 * ⟪Q, R⟫ + s.2.2 * ⟪R, R⟫ < t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B =
        k0 + (k5dX5 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B)) :
    HasLexCellAt V R := by
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k5dX5 α4 γ4 β1 β6 γ6) ?_ hmem
    [(0, 1, 0), (1, 0, -β1)] ?_
    (u1 := -1) (u2 := 1) (t1 := 0) (t2 := -1) (lo := 0) (hi := (α4 + γ4 - 1) / (α4 + γ4 + 1)) (by norm_num) (div_pos hs' (by linarith))
    (fun v1 v2 => v1 < 0 ∧ 0 < v2 ∧ γ4 * v1 + (1 - α4) * v2 < 0 ∧ 0 < (1 - γ4) * v1 + α4 * v2) ?_ ?_
    (k5dL α4 γ4 β1 β6 γ6) ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k5dX5_0, k5dX5_1, k5dX5_2, k5dX5_3, k5dX5_4] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
  · intro lam h0 h1
    have hl : lam * (α4 + γ4 + 1) < α4 + γ4 - 1 := by
      rw [lt_div_iff₀ (by linarith)] at h1; exact h1
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
    refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨hv1, hv2, hc1, hc2⟩ := hv
    exact k5dX5_tsc hα4 hγ4 hs hβ1 hb6 hg6 hv1 hv2 hc1 hc2
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX5_0, k5dX5_1, k5dX5_2, k5dX5_3, k5dX5_4, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    exact horc k0 U T B hfw hinj

theorem k5d_c6_core (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX6 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6))
    (horc : ∀ k0 U T B : ℝ,
      (∀ s ∈ k5dL α4 γ4 β1 β6 γ6, ∀ t ∈ k5dL α4 γ4 β1 β6 γ6,
        s.1 * ⟪P, R⟫ + s.2.1 * ⟪Q, R⟫ + s.2.2 * ⟪R, R⟫ < t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (k5dX6 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 i).2.2 * B =
        k0 + (k5dX6 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX6 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 i).2.2 * B)) :
    HasLexCellAt V R := by
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  refine k5d_cell V P Q R d hΔ (k := 6) (by norm_num) (k5dX6 α4 γ4 β1 β6 γ6) ?_ hmem
    [(0, 0, -1)] ?_
    (u1 := α4) (u2 := γ4) (t1 := 0) (t2 := 1) (lo := 0) (hi := γ4 / (α4 + 1)) (by simp; exact hα4.ne') (div_pos hγ4 (by linarith))
    (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧ 0 < γ4 * v1 + (1 - α4) * v2 ∧ 0 < α4 * v2 + (1 - γ4) * v1) ?_ ?_
    (k5dL α4 γ4 β1 β6 γ6) ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
  · intro lam h0 h1
    have hl : lam * (α4 + 1) < γ4 := by
      rw [lt_div_iff₀ (by linarith)] at h1; exact h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨hα4, by linarith, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨hv1, hv2, hc1, hc2⟩ := hv
    exact k5dX6_tsc hα4 hγ4 hs hβ1 hb6 hg6 hv1 hv2 hc1 hc2
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    exact horc k0 U T B hfw hinj


end C2
end Type08Sp
end Minimality
