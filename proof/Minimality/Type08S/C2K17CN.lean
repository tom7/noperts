module

public import Minimality.Type08S.C2K17CM

@[expose] public section


/-!
# K17C / P3N: frame lemmas and data lemmas of S3.6b (`γ6 ≤ 1`) and S3.4 (`γ6 > 1`) at the view `d - b`.
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
theorem k17cS36b_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β6 γ6 : ℝ}
    (hα1 : 1 < α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hPQ : ⟪P, Q⟫ = 0) (hPR : ⟪P, R⟫ = 0) (hPP : 0 < ⟪P, P⟫)
    (hcb : 0 < ⟪R, R⟫ + ⟪Q, R⟫) (hab : 0 < γ6 * ⟪Q, R⟫ + (1 - β6) * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k17cS36bCyc α1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1, 0, -1) ∨ y = fpoint P Q R d (α1, 1, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, γ6, -β6) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0)) :
    HasLexCellAt V R := by
  have a0 : 0 < α1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k17cS36bCyc α1 β6 γ6)
    (k17cS36b_inj a0 hγ6 hb6) hmem [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0)] ?_
    (u1 := -1) (u2 := -1) (t1 := 1/2) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < 0) ?_ ?_ ?_
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
    refine ⟨by linarith, by linarith⟩
  · rintro v1 v2 ⟨hv1, hv2⟩
    exact k17cS36b_tsc hα1 hb6 hγ6 hγ61 hs hv1 hv2
  · rintro v1 v2 ⟨hv1, hv2⟩ hL
    refine lexUni5_two _ _ hL ?_ ?_ ?_
    · -- b' < c
      right
      simp only [k17cS36bCyc, pc5_1, pc5_2, inner_fpoint, k17c_inner_fcomb_right, hPR, hPQ]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos a0 (mul_pos (neg_pos.2 hv1) hPP)]
    · -- b < a'
      left
      simp only [k17cS36bCyc, pc5_3, pc5_4, inner_fpoint, hPR]
      nlinarith
    · -- c' < b'
      left
      left
      simp only [k17cS36bCyc, pc5_0, pc5_1, inner_fpoint, hPR]
      nlinarith

set_option maxHeartbeats 3200000 in
theorem k17cS34_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β6 γ6 : ℝ}
    (hα1 : 1 < α1) (hb6 : 0 < β6) (hγ6 : 1 < γ6)
    (hPQ : ⟪P, Q⟫ = 0) (hPR : ⟪P, R⟫ = 0) (hPP : 0 < ⟪P, P⟫)
    (hcb : 0 < ⟪R, R⟫ + ⟪Q, R⟫) (hab : 0 < γ6 * ⟪Q, R⟫ + (1 - β6) * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k17cS34Cyc α1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1, 0, -1) ∨ y = fpoint P Q R d (α1, 1, 0) ∨
      y = fpoint P Q R d (0, γ6, -β6) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have a0 : 0 < α1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k17cS34Cyc α1 β6 γ6)
    (k17cS34_inj a0 hγ6) hmem [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)] ?_
    (u1 := -1) (u2 := -1) (t1 := 1/2) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < 0) ?_ ?_ ?_
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
    refine ⟨by linarith, by linarith⟩
  · rintro v1 v2 ⟨hv1, hv2⟩
    exact k17cS34_tsc hα1 hb6 hγ6 hv1 hv2
  · rintro v1 v2 ⟨hv1, hv2⟩ hL
    refine k17c_lexUni4_valley _ _ hL ?_ ?_ ?_
    · -- c' < b'
      left
      simp only [k17cS34Cyc_0, k17cS34Cyc_1, inner_fpoint, hPR]
      nlinarith
    · -- c' < b
      right
      simp only [k17cS34Cyc_0, k17cS34Cyc_3, inner_fpoint, k17c_inner_fcomb_right, hPR, hPQ]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos a0 (mul_pos (neg_pos.2 hv1) hPP)]
    · -- b < a'
      left
      simp only [k17cS34Cyc_3, k17cS34Cyc_2, inner_fpoint, hPR]
      nlinarith

end C2
end Type08Sp
end Minimality
