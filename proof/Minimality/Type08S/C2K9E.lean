module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9D

@[expose] public section

/-!
# K9E: frame-form cells for the strata L2 and L3 at the view `R = b - d` (Gram hypotheses).
Notation: `G11 = ⟪P,P⟫`, `G12 = ⟪P,Q⟫`, `G22 = ⟪Q,Q⟫`, `C = ⟪P,R⟫`, `B = ⟪Q,R⟫`, `A = ⟪R,R⟫`.
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

/-- Depth differences along `k9Y1 = (b, d, c, b', c')`. -/
theorem k9_Y1_z (P Q R d : ℝ³) (γ4 β1 : ℝ) :
    k9z P Q R d (k9Y1 γ4 β1 1) - k9z P Q R d (k9Y1 γ4 β1 0) = -⟪R, R⟫ ∧
    k9z P Q R d (k9Y1 γ4 β1 2) - k9z P Q R d (k9Y1 γ4 β1 1) = ⟪P, R⟫ ∧
    k9z P Q R d (k9Y1 γ4 β1 3) - k9z P Q R d (k9Y1 γ4 β1 2) = (γ4 - 1) * ⟪P, R⟫ + ⟪Q, R⟫ ∧
    k9z P Q R d (k9Y1 γ4 β1 4) - k9z P Q R d (k9Y1 γ4 β1 3) = -γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ ∧
    k9z P Q R d (k9Y1 γ4 β1 4) - k9z P Q R d (k9Y1 γ4 β1 0) = ⟪Q, R⟫ + (β1 - 1) * ⟪R, R⟫ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [k9_zd] <;> simp only [k9Y1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] <;> ring

theorem k9_Y1_w (P Q R d : ℝ³) (γ4 β1 v1 v2 : ℝ) :
    k9w P Q R d v1 v2 (k9Y1 γ4 β1 2) - k9w P Q R d v1 v2 (k9Y1 γ4 β1 1) = v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ ∧
    k9w P Q R d v1 v2 (k9Y1 γ4 β1 3) - k9w P Q R d v1 v2 (k9Y1 γ4 β1 2) =
      v1 * ((γ4 - 1) * ⟪P, P⟫ + ⟪P, Q⟫) + v2 * ((γ4 - 1) * ⟪P, Q⟫ + ⟪Q, Q⟫) ∧
    k9w P Q R d v1 v2 (k9Y1 γ4 β1 4) - k9w P Q R d v1 v2 (k9Y1 γ4 β1 3) =
      -γ4 * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + β1 * (v1 * ⟪P, R⟫ + v2 * ⟪Q, R⟫) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [k9_wd] <;> simp only [k9Y1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] <;> ring

theorem k9_Y2_z (P Q R d : ℝ³) (γ4 β1 : ℝ) :
    k9z P Q R d (k9Y2 γ4 β1 2) - k9z P Q R d (k9Y2 γ4 β1 1) = ⟪P, R⟫ ∧
    k9z P Q R d (k9Y2 γ4 β1 4) - k9z P Q R d (k9Y2 γ4 β1 3) = -γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ ∧
    k9z P Q R d (k9Y2 γ4 β1 4) - k9z P Q R d (k9Y2 γ4 β1 0) = β1 * ⟪R, R⟫ := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [k9_zd] <;> simp only [k9Y2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] <;> ring

/-- Gram data: `G11 A - C² > 0` from `det3 P Q R ≠ 0`. -/
theorem k9_cs (P Q R : ℝ³) (hΔ : det3 P Q R ≠ 0) : 0 < ⟪P, P⟫ * ⟪R, R⟫ - ⟪P, R⟫ ^ 2 := by
  have hR : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR
  set w : ℝ³ := ⟪R, R⟫ • P - ⟪P, R⟫ • R with hw
  have hdet : det3 w Q R = ⟪R, R⟫ * det3 P Q R := by
    simp only [hw, det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : det3 (0 : ℝ³) Q R = 0 := by simp [det3_expand]
    rw [this] at hdet
    rcases mul_eq_zero.mp hdet.symm with h | h
    · linarith
    · exact hΔ h
  have hpos : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hw0
  have e : ⟪w, w⟫ = ⟪R, R⟫ * (⟪P, P⟫ * ⟪R, R⟫ - ⟪P, R⟫ ^ 2) := by
    simp only [hw, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm P R]; ring
  rw [e] at hpos
  exact pos_of_mul_pos_right hpos hA.le

end C2
end Type08Sp
end Minimality
