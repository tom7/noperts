module

public import Minimality.Type08S.C2K17CB

@[expose] public section


/-!
# K17C / P3C: S3.5 frame lemma and the cell lemma (`γ6 ≤ 1`, `α1 ≥ 1`, `⟪b-d, c-d⟫ < 0`).
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
theorem k17cS35_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β6 γ6 : ℝ}
    (hα1 : 1 ≤ α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hPQ : ⟪P, Q⟫ = 0) (hPR : ⟪P, R⟫ = 0) (hPP : 0 < ⟪P, P⟫)
    (hQR : 0 < ⟪Q, R⟫) (hRR : 0 < ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k17cS35Cyc α1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (α1, 0, -1) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have a0 : 0 < α1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k17cS35Cyc α1)
    (k17cS35_inj a0) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)] ?_
    (u1 := 1) (u2 := -1) (t1 := 0) (t2 := 1/2) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ v2 < 0) ?_ ?_ ?_
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
    linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k17cS35_tsc hα1 hb6 hγ6 hγ61 hs hv1 hv2
  · intro v1 v2 ⟨hv1, hv2⟩ hL
    refine lexUni5_adj _ _ hL ?_ ?_ ?_
    · -- c < b'
      right
      simp only [k17cS35Cyc, pc5_0, pc5_1, inner_fpoint, k17c_inner_fcomb_right, hPR, hPQ]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos a0 (mul_pos hv1 hPP)]
    · -- d < c
      left
      simp only [k17cS35Cyc, pc5_1, pc5_2, inner_fpoint, hPR]
      nlinarith
    · -- b < d
      left; left
      simp only [k17cS35Cyc, pc5_2, pc5_3, inner_fpoint, hPR]
      nlinarith

end C2
end Type08Sp
end Minimality
