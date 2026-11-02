module

public import Minimality.Type08S.C2K16G

@[expose] public section


/-!
# K16 / H: H5 rule r1 as a lemma on the slice data.
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
/-- **H5 rule r1** (`ζ_{d-c}(c, a') < 0`): `α1, β1 > 1`, `β6, γ6 < 1`, `σ > β1`, the Coll5 relation `K16Rel`. -/
theorem k16_r1_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1) (hlit : ⟪c - a', d - c⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqr : ⟪q, r⟫ = ⟪r, q⟫ := real_inner_comm _ _
  have hpr : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (α1, 0, β1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have key : ∀ x y z : ℝ, ⟪x • p + y • q + z • r, r⟫ = x * ⟪p, r⟫ + y * ⟪q, r⟫ + z * ⟪r, r⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, r⟫ → ⟪X, r⟫ < ⟪Y, r⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  -- Gram data of the slice
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hpr]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m3, h0, hqp, hpr]
  set s := ⟪p, q⟫ with hs
  set Q := ⟪q, q⟫ with hQ
  set T := ⟪r, r⟫ with hT
  set R := ⟪q, r⟫ with hR
  have hW : 0 < Q + T - 2 * R := by linarith
  have hspr : ⟪p, r⟫ = s := hm1.symm
  -- the three metric inequalities
  have i1 : 0 < α1 * s + (β1 - 1) * T := by
    have : 0 < (α1 * s + (β1 - 1) * T) * (Q + T - 2 * R) := by
      have hTR : 0 < (T - R) ^ 2 := by
        have : 0 < T - R := by linarith
        positivity
      have e : (α1 * s + (β1 - 1) * T) * (Q + T - 2 * R) = (β1 - 1) * (T - R) ^ 2 := by
        linear_combination hr1
      rw [e]; exact mul_pos (by linarith) hTR
    exact (mul_pos_iff_of_pos_right hW).1 this
  have i2 : 0 < -(α1 * s) - (β1 - 1) * R := by
    have : 0 < (-(α1 * s) - (β1 - 1) * R) * (Q + T - 2 * R) := by
      have e : (-(α1 * s) - (β1 - 1) * R) * (Q + T - 2 * R) = (β1 - 1) * ((Q - R) * (T - R)) := by
        linear_combination (-1 : ℝ) * hr1
      rw [e]; exact mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
    exact (mul_pos_iff_of_pos_right hW).1 this
  have i3 : 0 < (β6 - 1) * R + γ6 * T := by
    rcases le_or_gt R 0 with h | h
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - β6) (by linarith : (0:ℝ) ≤ -R), mul_pos hγ6 hrr]
    · nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - β6) h, mul_pos hγ6 (by linarith : (0:ℝ) < T - R)]
  have i4 : 0 < T - β6 * R - γ6 * T := by
    have e : ⟪c - a', d - c⟫ = -(T - β6 * R - γ6 * T) := by
      have e1 : c - a' = (-β6) • q + (1 - γ6) • r := by rw [ha', hq, hr]; module
      have e2 : d - c = -r := by rw [hr]; abel
      rw [e1, e2, inner_neg_right, inner_add_left, inner_smul_left, inner_smul_left]
      simp only [RCLike.conj_to_real]; rw [← hT, ← hR]; ring
    linarith
  refine ⟨r, hr0, ?_⟩
  refine k16_r1_frame (V8 a a' b b' c c' d) p q r d hdet hα1 hβ1 hβ6 hβ61 hγ6 hγ61 hσ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k16R1Cyc_0, eC']; simp [V8]
    · simp only [k16R1Cyc_1, eB]; simp [V8]
    · simp only [k16R1Cyc_2, eA']; simp [V8]
    · simp only [k16R1Cyc_3, eC]; simp [V8]
    · simp only [k16R1Cyc_4, eB']; simp [V8]
  · intro y hy
    rw [eC', eB, eA', eC, eB', eA, eO]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eC', eB]
    apply inner_lt
    have : b - c' = (-α1) • p + (1 - β1) • q + (0:ℝ) • r := by rw [hc', hp, hq]; module
    rw [this, key, hspr]
    linarith
  · rw [eB, eA']
    apply inner_lt
    have : a' - b = (0:ℝ) • p + (β6 - 1) • q + γ6 • r := by rw [ha', hq, hr]; module
    rw [this, key, hspr]
    linarith
  · rw [eA', eC]
    apply inner_lt
    have : c - a' = (0:ℝ) • p + (-β6) • q + (1 - γ6) • r := by rw [ha', hq, hr]; module
    rw [this, key, hspr]
    linarith
  · rw [eC, eB']
    apply inner_lt
    have : b' - c = (α1) • p + (0:ℝ) • q + (β1 - 1) • r := by rw [hb', hp, hr]; module
    rw [this, key, hspr]
    linarith

end C2
end Type08Sp
end Minimality
