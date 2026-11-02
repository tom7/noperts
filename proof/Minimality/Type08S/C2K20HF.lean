module

public import Minimality.Type08S.C2K20HE

@[expose] public section


/-!
# K20H5 / F: H5 rule r7 (line view `L14`).
-/
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

/-- The `L14` view as a combination of `a - d` and `c - d`. -/
noncomputable def k20V7 (a c d : ℝ³) (A B : ℝ) : ℝ³ := A • (a - d) + B • (c - d)

set_option maxHeartbeats 6400000 in
theorem k20_r7_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d)
    (hlit0 : (β1 - 1) * (α1 - 1) * γ6 < α1 * β1 * (1 - β6))
    (hlit : 0 < ⟪a' - c, k20V7 a c d (α1 * (1 - β6)) ((β1 - 1) * γ6)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hα0 : 0 < α1 := by linarith
  have hB : 0 < (β1 - 1) * γ6 := mul_pos (by linarith) hγ6
  have hA : 0 < α1 * (1 - β6) := mul_pos hα0 (by linarith)
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * ((β1 - 1) * γ6) = 1 := ⟨1 / ((β1 - 1) * γ6), one_div_mul_cancel hB.ne'⟩
  have hμ0 : 0 < μ := by
    by_contra h; push Not at h; nlinarith
  set w := k20V7 a c d (α1 * (1 - β6)) ((β1 - 1) * γ6) with hw
  have hV : w = (α1 * (1 - β6)) • p + ((β1 - 1) * γ6) • r := by rw [hw, k20V7]
  have hdetV : det3 p q w = ((β1 - 1) * γ6) * det3 p q r := by
    rw [hV]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hΔ : det3 p q w ≠ 0 := by
    rw [hdetV]; exact mul_ne_zero hB.ne' hdet
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m3, h0, hqp, hrp]
  have iP : ⟪p, w⟫ = (α1 * (1 - β6)) * ⟪p, p⟫ + ((β1 - 1) * γ6) * ⟪p, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right]
  have iQ : ⟪q, w⟫ = (α1 * (1 - β6)) * ⟪p, r⟫ + ((β1 - 1) * γ6) * ⟪q, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right, hqp, hm1]
  have iR : ⟪r, w⟫ = (α1 * (1 - β6)) * ⟪p, r⟫ + ((β1 - 1) * γ6) * ⟪r, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right, hrp]
  have zqr : ⟪q, w⟫ < ⟪r, w⟫ := by
    rw [iQ, iR]; nlinarith [mul_pos hB (sub_pos.2 hRT)]
  have hlit' : (1 - γ6) * ⟪r, w⟫ < β6 * ⟪q, w⟫ := by
    have e : a' - c = β6 • q + (γ6 - 1) • r := by rw [ha', hq, hr]; module
    rw [e, inner_add_left, inner_smul_left, inner_smul_left] at hlit
    simp only [RCLike.conj_to_real] at hlit
    linarith
  have zr : 0 < ⟪r, w⟫ := by
    by_contra h; push Not at h
    have h1 := mul_lt_mul_of_pos_left zqr hβ6
    have h2 : 0 ≤ (β6 + γ6 - 1) * (-⟪r, w⟫) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have zq : 0 < ⟪q, w⟫ := by
    have := mul_pos (by linarith : (0:ℝ) < 1 - γ6) zr
    nlinarith
  -- the points
  have eO : fpoint p q w d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q w d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q w d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC' : fpoint p q w d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eC : fpoint p q w d (-(α1 * (1 - β6) * μ), 0, μ) = c := by
    simp only [fpoint, fcomb]
    have : d + ((-(α1 * (1 - β6) * μ)) • p + (0:ℝ) • q + μ • w) = d + (μ * ((β1 - 1) * γ6)) • r := by
      rw [hV]; module
    rw [this, hμ, one_smul, hr]; abel
  have eB' : fpoint p q w d (α1 - β1 * (α1 * (1 - β6)) * μ, 0, β1 * μ) = b' := by
    simp only [fpoint, fcomb]
    have : d + ((α1 - β1 * (α1 * (1 - β6)) * μ) • p + (0:ℝ) • q + (β1 * μ) • w) =
        d + α1 • p + β1 • ((μ * ((β1 - 1) * γ6)) • r) := by
      rw [hV]; module
    rw [this, hμ, one_smul, hb', hp, hr]
  have hνβ : (γ6 * μ) * (β1 - 1) = 1 := by
    have : γ6 * μ * (β1 - 1) = μ * ((β1 - 1) * γ6) := by ring
    rw [this, hμ]
  have eA' : fpoint p q w d (-(α1 * (1 - β6) * (γ6 * μ)), β6, γ6 * μ) = a' := by
    simp only [fpoint, fcomb]
    have : d + ((-(α1 * (1 - β6) * (γ6 * μ))) • p + β6 • q + (γ6 * μ) • w) = d + β6 • q + (γ6 * (μ * ((β1 - 1) * γ6))) • r := by
      rw [hV]; module
    rw [this, hμ, ha', hq, hr]; simp
  have hb : α1 - β1 * (α1 * (1 - β6)) * μ < 1 := by
    have key : (β1 - 1) * (α1 - 1) * γ6 * μ = α1 - 1 := by linear_combination (α1 - 1) * hμ
    nlinarith [mul_lt_mul_of_pos_right hlit0 hμ0]
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, w⟫ → ⟪X, w⟫ < ⟪Y, w⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  refine ⟨w, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k20_r7_frame (V8 a a' b b' c c' d) p q w d hΔ hα1 hβ1 hβ6 hβ61 hγ6 hγ61 hσ hμ0
    (mul_pos hγ6 hμ0) rfl hνβ hb ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k20R7Cyc_0, eC]; simp [V8]
    · simp only [k20R7Cyc_1, eO]; simp [V8]
    · simp only [k20R7Cyc_2, eA]; simp [V8]
    · simp only [k20R7Cyc_3, eC']; simp [V8]
    · simp only [k20R7Cyc_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eO, eA, eC', eA', eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eC, eA']
    exact inner_lt _ _ hlit
  · rw [eO, eC]
    apply inner_lt
    have : c - d = r := hr.symm
    rw [this]; exact zr
  · rw [eA, eO, eC']
    by_cases hpw : ⟪p, w⟫ < 0
    · left
      have : 0 < ⟪d - a, w⟫ := by
        have e : d - a = -p := by rw [hp]; abel
        rw [e, inner_neg_left]; linarith
      rw [inner_sub_left] at this; linarith
    · right
      push Not at hpw
      have e : c' - a = (α1 - 1) • p + β1 • q := by rw [hc', hp, hq]; module
      have : 0 < ⟪c' - a, w⟫ := by
        rw [e, inner_add_left, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1 - 1) hpw, mul_pos (by linarith : (0:ℝ) < β1) zq]
      rw [inner_sub_left] at this; linarith

end C2
end Type08Sp
end Minimality
