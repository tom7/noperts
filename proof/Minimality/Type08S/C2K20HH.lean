module

public import Minimality.Type08S.C2K20HG

@[expose] public section


/-!
# K20H5 / H: H5 rule r8 (view `a - b'`): frame lemma and `k20_r8_hasLexCell`.
Rule: `α1 β1 (1-β6) < γ6 (α1-1)(β1-1)` and `⟪c - a', a - b'⟫ > 0` (the sign-normalized sampler rule 8, chirality-free).
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

set_option maxHeartbeats 3200000 in
theorem k20_r8_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 μ ν : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β < β6 + γ6) (hμ : 0 < μ) (hν : 0 < ν) (hνμ : ν = γ6 * μ) (hμβ : μ * β = 1)
    (hlit : α * β * (1 - β6) < γ6 * (α - 1) * (β - 1))
    (hmem : ∀ i, fpoint P Q R d (k20R8Cyc α β β6 μ ν i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (-((α - 1) * μ), 0, μ) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α, β, 0) ∨
      y = fpoint P Q R d (-((α - 1) * ν), β6, ν) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (1, 0, 1))
    (h0 : ⟪fpoint P Q R d (-((α - 1) * μ), 0, μ), R⟫ < ⟪fpoint P Q R d (-((α - 1) * ν), β6, ν), R⟫)
    (h1 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (-((α - 1) * μ), 0, μ), R⟫)
    (h2 : ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫ ∨
      ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (α, β, 0), R⟫) :
    HasLexCellAt V R := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k20R8Cyc α β β6 μ ν)
    (k20R8_inj hα hβ0 hb6 hμ hν) hmem [(0, (1 : ℝ), (0 : ℝ)), (1, (0 : ℝ), (1 : ℝ))] ?_
    (u1 := -((α - 1) * μ)) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num)
    (by norm_num)
    (fun v1 v2 => v2 < 0 ∧ 0 < β * v1 - (α - 1) * v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0' h1'
    refine ⟨by norm_num, ?_⟩
    have : β * (-((α - 1) * μ) + lam * 1) - (α - 1) * (-1 + lam * 0) = β * lam := by
      linear_combination (-(α - 1)) * hμβ
    rw [this]; exact mul_pos hβ0 h0'
  · intro v1 v2 ⟨hc1, hc2⟩
    exact k20R8_tsc hα hβ hb6 hb61 hγ6 hγ61 hσ hμ hμβ hνμ hlit hc1 hc2
  · intro v1 v2 ⟨hc1, hc2⟩ hL
    refine k20_pent_uni3 _ _ hL ?_ ?_ ?_
    · left; simpa only [k20R8Cyc_0, k20R8Cyc_4] using h0
    · left; simpa only [k20R8Cyc_1, k20R8Cyc_0] using h1
    · simpa only [k20R8Cyc_2, k20R8Cyc_1, k20R8Cyc_3] using h2

set_option maxHeartbeats 6400000 in
theorem k20_r8_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d)
    (hlit0 : α1 * β1 * (1 - β6) < γ6 * (α1 - 1) * (β1 - 1))
    (hlit : 0 < ⟪c - a', a - b'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hA : 0 < α1 - 1 := by linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * β1 = 1 := ⟨1 / β1, one_div_mul_cancel hβ0.ne'⟩
  have hμ0 : 0 < μ := by
    by_contra h; push Not at h; nlinarith
  set w := b' - a with hw
  have hV : w = (α1 - 1) • p + β1 • r := by rw [hw, hb', hp, hr]; module
  have hdetV : det3 p q w = β1 * det3 p q r := by
    rw [hV]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hΔ : det3 p q w ≠ 0 := by
    rw [hdetV]; exact mul_ne_zero hβ0.ne' hdet
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
  have iP : ⟪p, w⟫ = (α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right]
  have iQ : ⟪q, w⟫ = (α1 - 1) * ⟪p, r⟫ + β1 * ⟪q, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right, hqp, hm1]
  have iR : ⟪r, w⟫ = (α1 - 1) * ⟪p, r⟫ + β1 * ⟪r, r⟫ := by
    rw [hV]; simp only [inner_add_right, inner_smul_right, hrp]
  have zqr : ⟪q, w⟫ < ⟪r, w⟫ := by
    rw [iQ, iR]; nlinarith [mul_pos hβ0 (sub_pos.2 hRT)]
  have hlit' : (1 - γ6) * ⟪r, w⟫ < β6 * ⟪q, w⟫ := by
    have e : a' - c = β6 • q + (γ6 - 1) • r := by rw [ha', hq, hr]; module
    have e2 : a' - c = -(c - a') := by abel
    have e3 : a - b' = -w := by rw [hw]; abel
    rw [e3, inner_neg_right] at hlit
    have h4 : 0 < ⟪a' - c, w⟫ := by
      rw [e2, inner_neg_left]; linarith
    rw [e, inner_add_left, inner_smul_left, inner_smul_left] at h4
    simp only [RCLike.conj_to_real] at h4
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
  have eC : fpoint p q w d (-((α1 - 1) * μ), 0, μ) = c := by
    simp only [fpoint, fcomb]
    have : d + ((-((α1 - 1) * μ)) • p + (0:ℝ) • q + μ • w) = d + (μ * β1) • r := by
      rw [hV]; module
    rw [this, hμ, one_smul, hr]; abel
  have eB' : fpoint p q w d (1, 0, 1) = b' := by
    simp only [fpoint, fcomb]
    have : d + ((1:ℝ) • p + (0:ℝ) • q + (1:ℝ) • w) = d + α1 • p + β1 • r := by
      rw [hV]; module
    rw [this, hb', hp, hr]
  have eA' : fpoint p q w d (-((α1 - 1) * (γ6 * μ)), β6, γ6 * μ) = a' := by
    simp only [fpoint, fcomb]
    have : d + ((-((α1 - 1) * (γ6 * μ))) • p + β6 • q + (γ6 * μ) • w) = d + β6 • q + (γ6 * (μ * β1)) • r := by
      rw [hV]; module
    rw [this, hμ, ha', hq, hr]; simp
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, w⟫ → ⟪X, w⟫ < ⟪Y, w⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  refine ⟨w, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k20_r8_frame (V8 a a' b b' c c' d) p q w d hΔ hα1 hβ1 hβ6 hβ61 hγ6 hγ61 hσ hμ0
    (mul_pos hγ6 hμ0) rfl hμ hlit0 ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k20R8Cyc_0, eC]; simp [V8]
    · simp only [k20R8Cyc_1, eO]; simp [V8]
    · simp only [k20R8Cyc_2, eA]; simp [V8]
    · simp only [k20R8Cyc_3, eC']; simp [V8]
    · simp only [k20R8Cyc_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eO, eA, eC', eA', eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eC, eA']
    apply inner_lt
    have e2 : a' - c = -(c - a') := by abel
    have e3 : a - b' = -w := by rw [hw]; abel
    rw [e3, inner_neg_right] at hlit
    rw [e2, inner_neg_left]; linarith
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
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1 - 1) hpw, mul_pos hβ0 zq]
      rw [inner_sub_left] at this; linarith

end C2
end Type08Sp
end Minimality
