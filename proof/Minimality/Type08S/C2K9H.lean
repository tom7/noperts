module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9G

@[expose] public section

/-!
# K9H: the stratum L3b (`β6 < 1`, tie `z(b) = z(c')`, `s = 0`) in frame form: cell 1 if `A > C`, cell 2 if `A < C`.
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
theorem k9_L3b_small (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫) (hy : ⟪Q, R⟫ = (1 - β1) * ⟪R, R⟫)
    (hAC : ⟪R, R⟫ < ⟪P, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k9Y2 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  have hA := k9_posR P Q R hΔ
  refine k9_cell2 V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 (-2) (-1) 1 0 (by norm_num) ?_ ?_ hmem hVall
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro lam hl0 hl1
    obtain ⟨z21, z43, z40⟩ := k9_Y2_z P Q R d γ4 β1
    refine ⟨Or.inl (by linarith), Or.inl ?_, Or.inl (Or.inl ?_)⟩
    · have : -γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ = ⟪R, R⟫ - ⟪P, R⟫ := by linarith
      linarith
    · have : 0 < β1 * ⟪R, R⟫ := mul_pos hβ1 hA
      linarith

theorem k9_L3b (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hβ1γ4 : β1 < γ4)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫)
    (hs : ⟪P, Q⟫ = (1 - β1) * ⟪P, R⟫) (hy : ⟪Q, R⟫ = (1 - β1) * ⟪R, R⟫)
    (hmem1 : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall1 : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6))
    (hmem2 : ∀ i, fpoint P Q R d (k9Y2 γ4 β1 i) ∈ V)
    (hVall2 : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  have hA := k9_posR P Q R hΔ
  rcases lt_trichotomy ⟪P, R⟫ ⟪R, R⟫ with h | h | h
  · exact k9_L3b_big V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 hβ1γ4 hC hB hs hy h hmem1 hVall1
  · exfalso
    have h1 : (1 - β1) * ⟪R, R⟫ = (1 - γ4) * ⟪P, R⟫ := by linarith
    rw [h] at h1
    have : (γ4 - β1) * ⟪R, R⟫ = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hA.ne'
    linarith
  · exact k9_L3b_small V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 hC hB hy h hmem2 hVall2

end C2
end Type08Sp
end Minimality
