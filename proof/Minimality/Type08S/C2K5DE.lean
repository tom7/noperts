module

public import Minimality.Type08S.C2K5DD

@[expose] public section


/-!
# K5d / E: cell 1, the pentagon `(c', b', c, d, b)` at `u0 = d - b` (frame lemmas)
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

/-- the seven frame points (list for the key) -/
def k5dL (α4 γ4 β1 β6 γ6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(1, 0, 0), (0, 1, 0), (0, 0, 0), (0, 0, -1), (α4, γ4, 0), (1, 0, -β1), (0, γ6, -β6)]

theorem k5d_hA {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : 0 < ⟪R, R⟫ := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  exact real_inner_self_pos.2 hR0

/-- Core of cell 1: lex part supplied as an oracle on the key. -/
theorem k5d_c1_core (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6))
    (horc : ∀ k0 U T B : ℝ,
      (∀ s ∈ k5dL α4 γ4 β1 β6 γ6, ∀ t ∈ k5dL α4 γ4 β1 β6 γ6,
        s.1 * ⟪P, R⟫ + s.2.1 * ⟪Q, R⟫ + s.2.2 * ⟪R, R⟫ < t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B =
        k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ))
        (fun i => k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B)) :
    HasLexCellAt V R := by
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  have hhi : 0 < (α4 + γ4 - 1) / (α4 + γ4 + 1) := div_pos hs' (by linarith)
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k5dX1 α4 γ4 β1) ?_ hmem
    [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)] ?_
    (u1 := 1) (u2 := -1) (t1 := 0) (t2 := 1) (lo := 0) (hi := (α4 + γ4 - 1) / (α4 + γ4 + 1)) (by norm_num) hhi
    (fun v1 v2 => 0 < v1 ∧ v2 < 0 ∧ 0 < γ4 * v1 + (1 - α4) * v2 ∧ (1 - γ4) * v1 + α4 * v2 < 0) ?_ ?_
    (k5dL α4 γ4 β1 β6 γ6) ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    have hl : lam * (α4 + γ4 + 1) < α4 + γ4 - 1 := by
      rw [lt_div_iff₀ (by linarith)] at h1; exact h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨by norm_num, by nlinarith, by nlinarith, by nlinarith⟩
  · intro v1 v2 ⟨hv1, hv2, hc1, hc2⟩
    exact k5d_c1_tsc hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hv1 hv2 hc1 hc2
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, k5dL]
  · intro v1 v2 _ k0 U T B hfw hinj
    exact horc k0 U T B hfw hinj

end C2
end Type08Sp
end Minimality
