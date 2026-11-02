module

public import Minimality.Type08S.C2K17B2B
public import Minimality.Type08S.C2K17B2C

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
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
theorem k17b2_p4_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy4 α β β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (-α, 0, -1) ∨ y = fpoint P Q R d0 (0, 0, 0) ∨
      y = fpoint P Q R d0 (β, 0, 0) ∨ y = fpoint P Q R d0 (α * β, β, 0) ∨ y = fpoint P Q R d0 (-α * γ6, β6, -γ6) ∨
      y = fpoint P Q R d0 (0, 0, -β) ∨ y = fpoint P Q R d0 (0, 1, 0))
    (h43 : ⟪fpoint P Q R d0 (-α * γ6, β6, -γ6), R⟫ < ⟪fpoint P Q R d0 (α * β, β, 0), R⟫)
    (h32 : ⟪fpoint P Q R d0 (α * β, β, 0), R⟫ < ⟪fpoint P Q R d0 (β, 0, 0), R⟫)
    (h21 : ⟪fpoint P Q R d0 (β, 0, 0), R⟫ < ⟪fpoint P Q R d0 (0, 0, 0), R⟫)
    (h01 : ⟪fpoint P Q R d0 (-α, 0, -1), R⟫ < ⟪fpoint P Q R d0 (0, 0, 0), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 5) (by norm_num) (k17b2Cy4 α β β6 γ6)
    (k17b2Cy4_inj (by linarith) (by linarith) (by linarith) (by linarith)) hmem
    [((0 : ℝ), (0 : ℝ), -β), ((0 : ℝ), (1 : ℝ), (0 : ℝ))] ?_
    (u1 := 0) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v2) ?_ ?_ ?_
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
    norm_num
  · intro v1 v2 hv2
    exact k17b2_p4_tsc hα hβ hβ6 hγ6 hv2
  · intro v1 v2 _ hL
    refine k17b2_pent_uni2 _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k17b2Cy4_4, k17b2Cy4_3] using h43
    · simpa only [k17b2Cy4_3, k17b2Cy4_2] using h32
    · simpa only [k17b2Cy4_2, k17b2Cy4_1] using h21
    · simpa only [k17b2Cy4_0, k17b2Cy4_1] using h01

set_option maxHeartbeats 3200000 in
theorem k17b2_p5_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy5 α β β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (-α, 0, -1) ∨ y = fpoint P Q R d0 (0, 0, -β) ∨
      y = fpoint P Q R d0 (β, 0, 0) ∨ y = fpoint P Q R d0 (α * β, β, 0) ∨ y = fpoint P Q R d0 (-α * γ6, β6, -γ6) ∨
      y = fpoint P Q R d0 (0, 0, 0) ∨ y = fpoint P Q R d0 (0, 1, 0))
    (h12 : ⟪fpoint P Q R d0 (0, 0, -β), R⟫ < ⟪fpoint P Q R d0 (β, 0, 0), R⟫)
    (h23 : ⟪fpoint P Q R d0 (β, 0, 0), R⟫ < ⟪fpoint P Q R d0 (α * β, β, 0), R⟫)
    (h43 : ⟪fpoint P Q R d0 (-α * γ6, β6, -γ6), R⟫ < ⟪fpoint P Q R d0 (α * β, β, 0), R⟫)
    (h04 : ⟪fpoint P Q R d0 (-α, 0, -1), R⟫ < ⟪fpoint P Q R d0 (-α * γ6, β6, -γ6), R⟫)
    (h10 : ⟪fpoint P Q R d0 (0, 0, -β), R⟫ < ⟪fpoint P Q R d0 (-α, 0, -1), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 5) (by norm_num) (k17b2Cy5 α β β6 γ6)
    (k17b2Cy5_inj (by linarith) (by linarith) (by linarith) (by linarith)) hmem
    [((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ), (0 : ℝ))] ?_
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v2 < 0) ?_ ?_ ?_
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
    norm_num
  · intro v1 v2 hv2
    exact k17b2_p5_tsc hα hβ hβ6 hγ6 hv2
  · intro v1 v2 _ hL
    refine k17b2_pent_uni3 _ _ hL ?_ ?_ ?_ ?_ ?_
    · simpa only [k17b2Cy5_1, k17b2Cy5_2] using h12
    · simpa only [k17b2Cy5_2, k17b2Cy5_3] using h23
    · simpa only [k17b2Cy5_4, k17b2Cy5_3] using h43
    · simpa only [k17b2Cy5_0, k17b2Cy5_4] using h04
    · simpa only [k17b2Cy5_1, k17b2Cy5_0] using h10

end C2
end Type08Sp
end Minimality
