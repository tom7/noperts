module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9E

@[expose] public section

/-!
# K9F: frame-form cell for the level-face strata L2a/L2b (`C = 0`, `B = 0`, `G12 = σ G11`)
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

theorem k9_posP (P Q R : ℝ³) (hΔ : det3 P Q R ≠ 0) : 0 < ⟪P, P⟫ := by
  have hP : P ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  exact real_inner_self_pos.2 hP

theorem k9_posR (P Q R : ℝ³) (hΔ : det3 P Q R ≠ 0) : 0 < ⟪R, R⟫ := by
  have hP : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  exact real_inner_self_pos.2 hP

set_option maxHeartbeats 1600000 in
theorem k9_L2 (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 σ : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hσ : 0 ≤ σ) (hK : 0 < σ + γ4 - 1) (hC : ⟪P, R⟫ = 0) (hB : ⟪Q, R⟫ = 0)
    (hG : ⟪P, Q⟫ = σ * ⟪P, P⟫)
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  have hG11 := k9_posP P Q R hΔ
  have hA := k9_posR P Q R hΔ
  set G11 := ⟪P, P⟫ with hG11d
  set G22 := ⟪Q, Q⟫ with hG22d
  set K := σ + γ4 - 1 with hKd
  set T := |G22| + |(1 - γ4) * σ| * G11 with hT
  have hKG : 0 < K * G11 := mul_pos hK hG11
  set M := σ + T / (K * G11) + 1 with hMd
  have hTnn : 0 ≤ T := by positivity
  have hM : M * (K * G11) = σ * (K * G11) + T + K * G11 := by
    rw [hMd]; field_simp
  have hMσ : σ < M := by
    have : 0 ≤ T / (K * G11) := div_nonneg hTnn hKG.le
    linarith
  have h0 : 0 ≤ σ * (K * G11) := mul_nonneg hσ hKG.le
  have h1 : T < M * (K * G11) := by rw [hM]; linarith
  have h3 : (γ4 - 1) * (σ * G11) + G22 ≤ T := by
    have a1 : G22 ≤ |G22| := le_abs_self G22
    have a2 : (γ4 - 1) * σ ≤ |(1 - γ4) * σ| := by
      have := neg_le_abs ((1 - γ4) * σ)
      linarith
    have a3 : (γ4 - 1) * σ * G11 ≤ |(1 - γ4) * σ| * G11 := mul_le_mul_of_nonneg_right a2 hG11.le
    have a4 : (γ4 - 1) * (σ * G11) = (γ4 - 1) * σ * G11 := by ring
    rw [hT]; linarith
  refine k9_cell1 V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 M (-1) 1 0 (by norm_num) ?_ ?_ hmem hVall
  · intro lam hl0 hl1
    constructor
    · linarith
    · linarith
  · intro lam hl0 hl1 _hs
    obtain ⟨z10, z21, z32, z43, z40⟩ := k9_Y1_z P Q R d γ4 β1
    obtain ⟨w21, w32, w43⟩ := k9_Y1_w P Q R d γ4 β1 (M + lam * 1) (-1 + lam * 0)
    rw [hC] at z21 z32 z43
    rw [hB] at z32
    have hv1 : σ < M + lam * 1 := by linarith
    refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · right
      refine ⟨by linarith, ?_⟩
      rw [hG] at w21
      have : 0 < G11 * (M + lam * 1 - σ) := mul_pos hG11 (sub_pos.2 hv1)
      linarith
    · right
      refine ⟨by linarith, ?_⟩
      rw [hG] at w32
      have h2 : M * (K * G11) ≤ (M + lam * 1) * (K * G11) :=
        mul_le_mul_of_nonneg_right (by linarith) hKG.le
      have e : (M + lam * 1) * ((γ4 - 1) * G11 + σ * G11) + (-1 + lam * 0) * ((γ4 - 1) * (σ * G11) + G22) =
          (M + lam * 1) * (K * G11) - ((γ4 - 1) * (σ * G11) + G22) := by
        rw [hKd]; ring
      linarith
    · left
      have : 0 < β1 * ⟪R, R⟫ := mul_pos hβ1 hA
      linarith

end C2
end Type08Sp
end Minimality
