module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9F

@[expose] public section

/-!
# K9G: frame-form cells for the strata L3a (`β6 > 1`) and L3b (`β6 < 1`), `C > 0`
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

theorem k9_tiltM (κ1 κ2 lam : ℝ) (hκ1 : 0 < κ1) (hl0 : 0 < lam) :
    0 < (|κ2| / κ1 + 1 + lam * 1) * κ1 + (-1 + lam * 0) * κ2 := by
  have e : (|κ2| / κ1 + 1 + lam * 1) * κ1 = |κ2| + κ1 + lam * κ1 := by field_simp
  have := le_abs_self κ2
  nlinarith [mul_pos hl0 hκ1]

set_option maxHeartbeats 1600000 in
/-- The common tail of the `C > 0` cells with the Q/P trichotomy on `ζ = z(c') - z(b')`. -/
theorem k9_trich (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫)
    (hcb : -γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ ≤ 0 → 0 < ⟪Q, R⟫ + (β1 - 1) * ⟪R, R⟫)
    (hκ1 : 0 < (γ4 - 1) * ⟪P, P⟫ + ⟪P, Q⟫)
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  set κ1 := (γ4 - 1) * ⟪P, P⟫ + ⟪P, Q⟫ with hκ1d
  set κ2 := (γ4 - 1) * ⟪P, Q⟫ + ⟪Q, Q⟫ with hκ2d
  refine k9_cell1 V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 (|κ2| / κ1 + 1) (-1) 1 0 (by norm_num) ?_ ?_ hmem hVall
  · intro lam hl0 hl1
    have : 0 ≤ |κ2| / κ1 := div_nonneg (abs_nonneg _) hκ1.le
    constructor <;> linarith
  · intro lam hl0 hl1 hs
    obtain ⟨z10, z21, z32, z43, z40⟩ := k9_Y1_z P Q R d γ4 β1
    obtain ⟨w21, w32, w43⟩ := k9_Y1_w P Q R d γ4 β1 (|κ2| / κ1 + 1 + lam * 1) (-1 + lam * 0)
    have hi : 0 < k9w P Q R d (|κ2| / κ1 + 1 + lam * 1) (-1 + lam * 0) (k9Y1 γ4 β1 3) -
        k9w P Q R d (|κ2| / κ1 + 1 + lam * 1) (-1 + lam * 0) (k9Y1 γ4 β1 2) := by
      rw [w32]; exact k9_tiltM κ1 κ2 lam hκ1 hl0
    have hz32 : k9z P Q R d (k9Y1 γ4 β1 3) = k9z P Q R d (k9Y1 γ4 β1 2) := by
      rw [hB] at z32; linarith
    refine ⟨Or.inl (by linarith), ?_⟩
    rcases lt_trichotomy (-γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫) 0 with hζ | hζ | hζ
    · left
      have := hcb hζ.le
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · have hne : k9w P Q R d (|κ2| / κ1 + 1 + lam * 1) (-1 + lam * 0) (k9Y1 γ4 β1 4) ≠
          k9w P Q R d (|κ2| / κ1 + 1 + lam * 1) (-1 + lam * 0) (k9Y1 γ4 β1 3) := by
        intro hw
        have := hs 4 3 (by linarith) hw
        exact absurd this (by decide)
      rcases lt_or_gt_of_ne hne with hw | hw
      · left
        have := hcb hζ.le
        exact ⟨Or.inl (by linarith), Or.inr ⟨by linarith, hw⟩⟩
      · right
        exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, hw⟩⟩
    · right
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩

set_option maxHeartbeats 1600000 in
/-- The `C > 0` cell with the P branch only (`ζ < 0`), any tilt in the cone. -/
theorem k9_trichP (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫)
    (hcb : 0 < ⟪Q, R⟫ + (β1 - 1) * ⟪R, R⟫) (hζ : -γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  refine k9_cell1 V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 1 (-1) 1 0 (by norm_num) ?_ ?_ hmem hVall
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro lam hl0 hl1 hs
    obtain ⟨z10, z21, z32, z43, z40⟩ := k9_Y1_z P Q R d γ4 β1
    refine ⟨Or.inl (by linarith), Or.inl ⟨Or.inl (by linarith), Or.inl (by linarith)⟩⟩

set_option maxHeartbeats 3200000 in
theorem k9_L3a (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 1 < β6)
    (hβ1γ4 : β1 < γ4)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫)
    (hs : ⟪P, Q⟫ = γ6 * ⟪P, P⟫ + (β6 - β1) * ⟪P, R⟫)
    (hy : ⟪Q, R⟫ = γ6 * ⟪P, R⟫ + (β6 - β1) * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  have hA := k9_posR P Q R hΔ
  have hG11 := k9_posP P Q R hΔ
  have hCS := k9_cs P Q R hΔ
  have hβ6' : 0 < β6 := by linarith
  set G11 := ⟪P, P⟫ with hG11d
  set G12 := ⟪P, Q⟫ with hG12d
  set C := ⟪P, R⟫ with hCd
  set B := ⟪Q, R⟫ with hBd
  set A := ⟪R, R⟫ with hAd
  have hδ : (β6 - β1) * A = (1 - γ4 - γ6) * C := by linarith
  have hcb : 0 < B + (β1 - 1) * A := by
    have : 0 < γ6 * C := mul_pos hγ6 hC
    have : 0 < (β6 - 1) * A := mul_pos (by linarith) hA
    nlinarith
  rcases lt_trichotomy (γ4 + γ6) 1 with hlt | heq | hgt
  · -- β: `A < C` and `ζ < 0`
    have hδpos : 0 < β6 - β1 := by
      have h1 : 0 < (1 - γ4 - γ6) * C := mul_pos (by linarith) hC
      have : 0 < (β6 - β1) * A := by rw [hδ]; exact h1
      exact pos_of_mul_pos_left this hA.le
    have hAC : A < C := by
      have h1 : 0 < 1 - γ4 := by linarith
      have h2 : (1 - γ4) * A < (β6 - β1) * A := by
        apply mul_lt_mul_of_pos_right _ hA; linarith
      have h3 : (1 - γ4 - γ6) * C < (1 - γ4) * C := by nlinarith [mul_pos hγ6 hC]
      have h4 : (1 - γ4) * A < (1 - γ4) * C := by linarith
      exact lt_of_mul_lt_mul_left h4 h1.le
    have hζ : -γ4 * C + β1 * A < 0 := by
      have h1 : β1 * A < γ4 * A := mul_lt_mul_of_pos_right hβ1γ4 hA
      have h2 : γ4 * A < γ4 * C := mul_lt_mul_of_pos_left hAC hγ4
      linarith
    exact k9_trichP V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6' hC hB hcb hζ hmem hVall
  · exfalso
    have h1 : (β6 - β1) * A = 0 := by rw [hδ, show 1 - γ4 - γ6 = 0 by linarith]; ring
    have h2 : β6 - β1 = 0 := (mul_eq_zero.mp h1).resolve_right hA.ne'
    linarith
  · have hκ1 : 0 < (γ4 - 1) * G11 + G12 := by
      have e : A * ((γ4 - 1) * G11 + G12) = (γ4 + γ6 - 1) * (G11 * A - C ^ 2) := by
        have : G12 = γ6 * G11 + (β6 - β1) * C := hs
        rw [this]
        have h2 : (β6 - β1) * C * A = (1 - γ4 - γ6) * C * C := by
          linear_combination C * hδ
        nlinarith
      have h3 : 0 < A * ((γ4 - 1) * G11 + G12) := by
        rw [e]; exact mul_pos (by linarith) hCS
      exact pos_of_mul_pos_right h3 hA.le
    exact k9_trich V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6' hC hB (fun _ => hcb) hκ1 hmem hVall

set_option maxHeartbeats 3200000 in
theorem k9_L3b_big (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (hβ1γ4 : β1 < γ4)
    (hC : 0 < ⟪P, R⟫) (hB : ⟪Q, R⟫ = (1 - γ4) * ⟪P, R⟫)
    (hs : ⟪P, Q⟫ = (1 - β1) * ⟪P, R⟫) (hy : ⟪Q, R⟫ = (1 - β1) * ⟪R, R⟫)
    (hAC : ⟪P, R⟫ < ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  have hA := k9_posR P Q R hΔ
  have hG11 := k9_posP P Q R hΔ
  have hCS := k9_cs P Q R hΔ
  set G11 := ⟪P, P⟫ with hG11d
  set G12 := ⟪P, Q⟫ with hG12d
  set C := ⟪P, R⟫ with hCd
  set B := ⟪Q, R⟫ with hBd
  set A := ⟪R, R⟫ with hAd
  have hγ41 : 1 < γ4 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 - β1) * A = (1 - γ4) * C := by linarith
    have h2 : 0 < 1 - β1 := by linarith
    have h3 : (1 - β1) * C < (1 - β1) * A := mul_lt_mul_of_pos_left hAC h2
    have h4 : (1 - γ4) * C ≤ (1 - β1) * C := mul_le_mul_of_nonneg_right (by linarith) hC.le
    linarith
  have hκ1 : 0 < (γ4 - 1) * G11 + G12 := by
    have e : A * ((γ4 - 1) * G11 + G12) = (γ4 - 1) * (G11 * A - C ^ 2) := by
      have : G12 = (1 - β1) * C := hs
      rw [this]
      have h2 : (1 - β1) * C * A = (1 - γ4) * C * C := by
        have h1 : (1 - β1) * A = (1 - γ4) * C := by linarith
        calc (1 - β1) * C * A = C * ((1 - β1) * A) := by ring
          _ = (1 - γ4) * C * C := by rw [h1]; ring
      nlinarith
    have h3 : 0 < A * ((γ4 - 1) * G11 + G12) := by
      rw [e]; exact mul_pos (by linarith) hCS
    exact pos_of_mul_pos_right h3 hA.le
  exact k9_trich V P Q R d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 hC hB
    (fun h => by exfalso; linarith) hκ1 hmem hVall

end C2
end Type08Sp
end Minimality
