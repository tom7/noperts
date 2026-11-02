module

public import Minimality.Type08S.C2K6TBC

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

theorem k6t2_c8_tie_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hz : ⟪P, R⟫ = α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫) (hU0 : 0 < ⟪P, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5dX5 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c5_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  have h2 := hfw (0, 0, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h2
  have htu : ⟪Q, R⟫ < ⟪P, R⟫ := by nlinarith
  have h3 := hfw (0, γ6, -β6) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL])
    (by dsimp only; rw [hg6]; nlinarith [mul_pos hb6 hA])
  dsimp only at h3
  have h4 := hfw (0, γ6, -β6) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL])
    (by dsimp only; rw [hg6]; nlinarith [mul_pos hb6 hA])
  dsimp only at h4
  rw [hg6] at h3 h4
  exact k6t2_c8_real hα4 hγ4 hs hβ1 hb6 hg6 hB (by linarith) (by linarith) (by linarith) hinj

theorem k6t2_c1_tt_tie_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1) (hz : ⟪P, R⟫ = α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫) (hz2 : ⟪P, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hB : 0 < B := by
    have := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hU0 : U < 0 := by
    have := hfw (1, 0, 0) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hUb : U - β1 * B < α4 * U + γ4 * T := by
    have := hfw (1, 0, -β1) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL])
      (by dsimp only; nlinarith [mul_pos hβ1 hA])
    dsimp only at this; linarith
  have htu : ⟪P, R⟫ < ⟪Q, R⟫ := by nlinarith
  have hUT : U < T := by
    have := hfw (1, 0, 0) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  exact k6t2_c1_real_tt hα4 hγ4 hs hβ1 hB hU0 hUb hUT hinj

end C2
end Type08Sp
end Minimality
