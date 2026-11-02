module

public import Minimality.Type08S.C2K17CE

@[expose] public section


/-!
# K17C / P3F: frame lemma of the cells at `a - d`: pentagon `(b, a', b', a, d)`, view `R = a - d`, frame `(b - d, c - d, a - d)`.
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

/-- The tilt cone of the pentagon (screen conditions). -/
def K17cCone (β6 γ6 v1 v2 : ℝ) : Prop :=
  0 < v1 ∧ v2 < 0 ∧ β6 * v2 + (1 - γ6) * v1 < 0 ∧ 0 < γ6 * v1 + (1 - β6) * v2

/-- The metric condition on the tilt: the plateau `d, b, a'` is V-shaped. -/
def K17cMet (P Q R : ℝ³) (β6 γ6 v1 v2 : ℝ) : Prop :=
  ⟪P, fcomb P Q R v1 v2 0⟫ ≤ 0 ∨ 0 ≤ (β6 - 1) * ⟪P, fcomb P Q R v1 v2 0⟫ + γ6 * ⟪Q, fcomb P Q R v1 v2 0⟫

set_option maxHeartbeats 3200000 in
theorem k17cA_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β6 γ6 : ℝ}
    (hα1 : 1 ≤ α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hPR : ⟪P, R⟫ = 0) (hQR : ⟪Q, R⟫ = 0) (hRR : 0 < ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k17cACyc α1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (β6, γ6, 0) ∨
      y = fpoint P Q R d (0, 1, α1) ∨ y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (1, 0, α1))
    {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hC : ∀ lam : ℝ, 0 < lam → lam < 1 → K17cCone β6 γ6 (u1 + lam * t1) (u2 + lam * t2))
    (hU : ∀ lam : ℝ, 0 < lam → lam < 1 → K17cMet P Q R β6 γ6 (u1 + lam * t1) (u2 + lam * t2)) :
    HasLexCellAt V R := by
  have a0 : 0 < α1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k17cACyc α1 β6 γ6)
    (k17cA_inj a0 hγ6 hb6) hmem [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, α1)] ?_
    (u1 := u1) (u2 := u2) (t1 := t1) (t2 := t2) (lo := 0) (hi := 1) hut (by norm_num)
    (fun v1 v2 => K17cCone β6 γ6 v1 v2 ∧ K17cMet P Q R β6 γ6 v1 v2) ?_ ?_ ?_
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
    exact ⟨hC lam h0 h1, hU lam h0 h1⟩
  · rintro v1 v2 ⟨⟨hv1, hv2, hc3, hc4⟩, -⟩
    exact k17cA_tsc hα1 hb6 hγ6 hs hv1 hv2 hc3 hc4
  · rintro v1 v2 ⟨-, hmet⟩ hL
    have hRP : ⟪R, P⟫ = 0 := by rw [real_inner_comm]; exact hPR
    have hRQ : ⟪R, Q⟫ = 0 := by rw [real_inner_comm]; exact hQR
    refine lexUni5_two _ _ hL ?_ ?_ ?_
    · -- a' < b'
      left
      simp only [k17cACyc, pc5_1, pc5_2, inner_fpoint, hPR, hQR]
      nlinarith
    · -- d < a
      left
      simp only [k17cACyc, pc5_3, pc5_4, inner_fpoint, hPR, hQR]
      nlinarith
    · -- b < a' or b < d
      unfold K17cMet at hmet
      simp only [k17c_inner_fcomb_right] at hmet
      rcases hmet with h | h
      · right
        have hz : ⟪fpoint P Q R d (k17cACyc α1 β6 γ6 0), R⟫ = ⟪fpoint P Q R d (k17cACyc α1 β6 γ6 4), R⟫ := by
          simp only [k17cACyc, pc5_0, pc5_4, inner_fpoint, hPR, hQR]; ring
        rcases lt_or_eq_of_le h with h' | h'
        · simp only [k17cACyc, pc5_0, pc5_4, inner_fpoint, hPR, hQR, hRP, hRQ, k17c_inner_fcomb_right]
          exact Or.inr ⟨by ring, by linarith⟩
        · exfalso
          have := hL 0 4 hz (by
            simp only [k17cACyc, pc5_0, pc5_4, inner_fpoint, hPR, hQR, hRP, hRQ, k17c_inner_fcomb_right]
            linarith)
          exact absurd this (by decide)
      · left
        have hz : ⟪fpoint P Q R d (k17cACyc α1 β6 γ6 0), R⟫ = ⟪fpoint P Q R d (k17cACyc α1 β6 γ6 1), R⟫ := by
          simp only [k17cACyc, pc5_0, pc5_1, inner_fpoint, hPR, hQR]; ring
        rcases lt_or_eq_of_le h with h' | h'
        · simp only [k17cACyc, pc5_0, pc5_1, inner_fpoint, hPR, hQR, hRP, hRQ, k17c_inner_fcomb_right]
          exact Or.inr ⟨by ring, by linarith⟩
        · exfalso
          have := hL 0 1 hz (by
            simp only [k17cACyc, pc5_0, pc5_1, inner_fpoint, hPR, hQR, hRP, hRQ, k17c_inner_fcomb_right]
            linarith)
          exact absurd this (by decide)

end C2
end Type08Sp
end Minimality
