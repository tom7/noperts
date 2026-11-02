module

public import Minimality.Type08S.C2K6TBJ

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

/-- **Cell `(a,c',b',c,d)` at the base view `R`, `γ4 > 1`** (frame form; any `α4 > 0`, `β1 > 0`, `γ6 ≤ 1`).
Only depth hypothesis: `ζ(b',c) < 0` (`α4 ⟪P,R⟫ + γ4 ⟪Q,R⟫ < ⟪Q,R⟫`), or `ζ(b',c) = 0` with `ζ(a,d) < 0`. -/
theorem k6t2_c4g_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1)
    (hw : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪Q, R⟫ ∨
      (α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ = ⟪Q, R⟫ ∧ ⟪P, R⟫ < 0))
    (hmem : ∀ i, fpoint P Q R d (k5dX4 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  have hg : 0 < γ4 - 1 := by linarith
  have hu1 : 0 < α4 / (γ4 - 1) + 1 := by positivity
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k5dX4 α4 γ4 β1 β6 γ6) ?_ hmem
    [(0, γ6, -β6), (0, 0, -1)] ?_
    (u1 := α4 / (γ4 - 1) + 1) (u2 := 0) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1)
    (by simpa using hu1.ne') (by norm_num)
    (fun v1 v2 => 0 < v2 ∧ α4 * v2 < (γ4 - 1) * v1) ?_ ?_
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
    refine ⟨h0, ?_⟩
    have : (γ4 - 1) * (α4 / (γ4 - 1)) = α4 := mul_div_cancel₀ _ hg.ne'
    nlinarith
  · intro v1 v2 hv
    obtain ⟨hv2, hc1⟩ := hv
    exact k6t2_x4_tsc hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hv2 hc1
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at hBd
    have hB : 0 < B := by linarith
    refine k6t2_c4g_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hα4 hγ4 hβ1 hA hB hw ?_ hinj
    intro i j hij
    by_contra hlt
    push Not at hlt
    have := hfw _ (by simpa using k5dX4_mem α4 γ4 β1 β6 γ6 j) _ (by simpa using k5dX4_mem α4 γ4 β1 β6 γ6 i) hlt
    linarith

end C2
end Type08Sp
end Minimality
