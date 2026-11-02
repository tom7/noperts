module

public import Minimality.Type08S.C2K16L

@[expose] public section


/-!
# K16 / M: H5 rule r2 (`ζ_{c'-a'}(d, b) > 0`), and by the swap r0 (`ζ_{b'-a'}(d, c) > 0`); no Coll5 relation needed.
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

set_option maxHeartbeats 6400000 in
/-- **H5 rule r2**: `α1, β1 > 1`, `β6, γ6 < 1`, `σ > β1`, `⟪d - b, c' - a'⟫ > 0` (view `c' - a'`). -/
theorem k16_r2_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hlit : 0 < ⟪d - b, c' - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g * γ6 = 1 := ⟨1 / γ6, by field_simp⟩
  set V0 := c' - a' with hV0
  have hV : V0 = α1 • p + (β1 - β6) • q + (-γ6) • r := by rw [hV0, hc', ha', hp, hq, hr]; module
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hdetV : det3 p q V0 = -γ6 * det3 p q r := by
    rw [hV]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hΔ : det3 p q V0 ≠ 0 := by
    rw [hdetV]; exact mul_ne_zero (by linarith) hdet
  have hV0ne : V0 ≠ 0 := by
    intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m3, h0, hqp, hrp]
  -- depth data at the view V0
  have zq : ⟪q, V0⟫ < 0 := by
    have : d - b = -q := by rw [hq]; abel
    rw [this, inner_neg_left] at hlit; linarith
  have hzqr : ⟪q, V0⟫ - ⟪r, V0⟫ = (β1 - β6) * (⟪q, q⟫ - ⟪q, r⟫) + γ6 * (⟪r, r⟫ - ⟪q, r⟫) := by
    rw [← inner_sub_left, hV]
    simp only [inner_add_right, inner_smul_right, inner_sub_left]
    linear_combination α1 * hqp - α1 * hrp + α1 * hm1 - (β1 - β6) * hrq
  have hD2 : 0 < (β1 - β6) * (⟪q, q⟫ - ⟪q, r⟫) + γ6 * (⟪r, r⟫ - ⟪q, r⟫) := by
    have h1 : 0 < β1 - β6 := by linarith
    nlinarith [mul_pos h1 (sub_pos.2 hQR), mul_pos hγ6 (sub_pos.2 hRT)]
  have zr : ⟪r, V0⟫ < 0 := by linarith
  have i12 : 0 < ⟪b - a', V0⟫ := by
    have e : b - a' = (1 - β6) • q + (-γ6) • r := by rw [ha', hq, hr]; module
    rw [e, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    nlinarith [mul_pos (by linarith : (0:ℝ) < β6 + γ6 - 1) (neg_pos.2 zq), mul_pos hγ6 hD2]
  have i34 : ⟪a - d, V0⟫ ≤ 0 → ⟪b' - a, V0⟫ < 0 := by
    intro h
    have e : b' - a = (α1 - 1) • p + β1 • r := by rw [hb', hp, hr]; module
    rw [e, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have : (α1 - 1) * ⟪p, V0⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (neg_pos.2 zr)]
  -- the points
  have eO : fpoint p q V0 d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q V0 d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q V0 d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC' : fpoint p q V0 d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eA' : fpoint p q V0 d (α1, β1, -1) = a' := by
    simp only [fpoint, fcomb]
    have : a' = c' - V0 := by rw [hV0]; abel
    rw [this, hc', hp, hq]; module
  have eC : fpoint p q V0 d (α1 * g, (β1 - β6) * g, -g) = c := by
    simp only [fpoint, fcomb]
    have h1 : g • (γ6 • r) = r := by rw [smul_smul, hg, one_smul]
    have h2 : g • V0 = α1 • g • p + (β1 - β6) • g • q - r := by
      rw [hV]
      calc g • (α1 • p + (β1 - β6) • q + (-γ6) • r)
          = α1 • g • p + (β1 - β6) • g • q - g • (γ6 • r) := by module
        _ = _ := by rw [h1]
    have h3 : c = d + r := by rw [hr]; abel
    rw [h3]
    have : (-g) • V0 = -(g • V0) := by rw [neg_smul]
    rw [this, h2]; module
  have eB' : fpoint p q V0 d (α1 * (1 + β1 * g), β1 * (β1 - β6) * g, -(β1 * g)) = b' := by
    simp only [fpoint, fcomb]
    have h1 : g • (γ6 • r) = r := by rw [smul_smul, hg, one_smul]
    have h2 : g • V0 = α1 • g • p + (β1 - β6) • g • q - r := by
      rw [hV]
      calc g • (α1 • p + (β1 - β6) • q + (-γ6) • r)
          = α1 • g • p + (β1 - β6) • g • q - g • (γ6 • r) := by module
        _ = _ := by rw [h1]
    have : (-(β1 * g)) • V0 = -(β1 • (g • V0)) := by rw [neg_smul, mul_smul]
    rw [this, h2, hb', hp]
    module
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, V0⟫ → ⟪X, V0⟫ < ⟪Y, V0⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hgp : 0 < g := by
    by_contra h; push Not at h; nlinarith
  refine ⟨V0, hV0ne, ?_⟩
  refine k16_r2_frame (V8 a a' b b' c c' d) p q V0 d hΔ hα1 hβ1 hβ6 hβ61 hγ6 hγ61 hσ hg ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k16R2Cyc_0, eB']; simp [V8]
    · simp only [k16R2Cyc_1, eA']; simp [V8]
    · simp only [k16R2Cyc_2, eB]; simp [V8]
    · simp only [k16R2Cyc_3, eO]; simp [V8]
    · simp only [k16R2Cyc_4, eA]; simp [V8]
  · intro y hy
    rw [eB', eA', eB, eO, eA, eC', eC]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eA', eB]; exact inner_lt _ _ i12
  · rw [eB, eO]
    apply inner_lt
    have : d - b = -q := by rw [hq]; abel
    rw [this, inner_neg_left]; linarith
  · rw [eA, eO, eB']
    intro h1 h2
    have := i34 (by rw [inner_sub_left]; linarith)
    rw [inner_sub_left] at this
    linarith

end C2
end Type08Sp
end Minimality
