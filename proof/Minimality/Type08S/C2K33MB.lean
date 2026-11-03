module

public import Minimality.Type08S.C2K33MA
public import Minimality.Type08S.C2K25Tie

@[expose] public section

set_option maxHeartbeats 1000000

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

set_option maxHeartbeats 12800000 in
theorem k24b2m_tieM {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hMneg : ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ < ⟪a - d, b - d⟫ ^ 2) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hdet' : det3 q r p ≠ 0 := by
    intro h; apply hdet; simp only [det3_expand] at h ⊢; linarith
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
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
    have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  -- s = <p,q> < 0 from Rel
  have hs : ⟪p, q⟫ < 0 := by
    have hr1 := hr1
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have h1 : 0 < (β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) :=
      mul_pos (by linarith) hr2
    by_contra hh; push Not at hh
    have h2 : 0 ≤ α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) :=
      mul_nonneg (mul_nonneg hα1'.le hh) hW.le
    nlinarith [hr1]
  have hLe : ⟪p, p⟫ - α1 * ⟪p, p⟫ - β1 * ⟪p, q⟫ = 0 := by
    have e : a - c' = (1 - α1) • p - β1 • q := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp] at hL
    linarith
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint q r p d (0, 0, 1) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint q r p d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r p d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint q r p d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint q r p d (0, β1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint q r p d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have key : ∀ x y z : ℝ, ⟪x • q + y • r + z • p, p⟫ = x * ⟪p, q⟫ + y * ⟪p, r⟫ + z * ⟪p, p⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hqp, hrp]
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, p⟫ → ⟪X, p⟫ < ⟪Y, p⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hspr : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  have hMn : ⟪p, p⟫ * ⟪q, r⟫ < ⟪p, q⟫ ^ 2 := hMneg
  have hcr : cross p q ≠ 0 := by
    intro h0; apply hdet'
    have : det3 q r p = ⟪r, cross p q⟫ := by
      simp only [det3, det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]; simp; ring
    rw [this, h0]; simp
  have hQ : ⟪p, q⟫ ^ 2 < ⟪p, p⟫ * ⟪q, q⟫ := by
    have h1 : 0 < ⟪cross p q, cross p q⟫ := real_inner_self_pos.2 hcr
    have h2 : ⟪cross p q, cross p q⟫ = ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
      simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]; simp; ring
    linarith
  have eca : c' - a = (α1 - 1) • p + β1 • q := by rw [hc', hp, hq]; module
  have eab : a - b' = (1 - α1) • p - β1 • r := by rw [hb', hp, hr]; module
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hf1 : 0 < ⟪c' - a, q⟫ := by
    have e : ⟪c' - a, q⟫ = (α1 - 1) * ⟪p, q⟫ + β1 * ⟪q, q⟫ := by
      rw [eca]; simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hqp]
    have : 0 < ⟪p, p⟫ * ⟪c' - a, q⟫ := by rw [e]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (sub_pos.2 hQ)]
    exact (pos_iff_pos_of_mul_pos this).1 hpp
  have hf2 : 0 < ⟪a - b', q⟫ := by
    have e : ⟪a - b', q⟫ = (1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫ := by
      rw [eab]; simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp, hrq]
    have : 0 < ⟪p, p⟫ * ⟪a - b', q⟫ := by rw [e]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (sub_pos.2 hMn)]
    exact (pos_iff_pos_of_mul_pos this).1 hpp
  have hT : ∀ v1 v2 : ℝ, k18Cone [((1:ℝ), (0:ℝ)), (0, 1), (⟪a - b', q⟫, ⟪a - b', r⟫), (⟪c' - a, q⟫, ⟪c' - a, r⟫)] v1 v2 →
      0 < v1 ∧ 0 < v2 := by
    intro v1 v2 hv
    have h1 := hv (1, 0) (by simp)
    have h2 := hv (0, 1) (by simp)
    simp only at h1 h2
    exact ⟨by linarith, by linarith⟩
  have hpq : ⟪fpoint q r p d (β1, 0, α1), p⟫ = ⟪fpoint q r p d (0, 0, 1), p⟫ := by
    rw [eC', eA]
    have : ⟪c' - a, p⟫ = (α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, q⟫ := by
      rw [eca]; simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hqp]
    rw [inner_sub_left] at this; linarith
  refine ⟨p, hp0, ?_⟩
  refine k25_tie_cell (V8 a a' b b' c c' d) q r p d hdet' (k := 4) (by norm_num) (k24b2mCyc α1 β1 β6 γ6)
    (k24b2m_inj hβ hβ6' hγ6') ?_
    [((1:ℝ), (0:ℝ)), (0, 1), (⟪a - b', q⟫, ⟪a - b', r⟫), (⟪c' - a, q⟫, ⟪c' - a, r⟫)] (by simp) ?_ ?_
    (1 : ZMod 4) ?_ ?_ ?_ (ρ1 := 1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k24b2mCyc_0, eA]; simp [V8]
    · simp only [k24b2mCyc_1, eC']; simp [V8]
    · simp only [k24b2mCyc_2, eA']; simp [V8]
    · simp only [k24b2mCyc_3, eB']; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    obtain ⟨hv1, hv2⟩ := hT v1 v2 hv
    exact tsc_scale hD ((k24b2m_tsc hβ hβ6' hγ6' hα1' hσ hv1 hv2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint q r p d (0, 0, 1) ∨ y = fpoint q r p d (β1, 0, α1) ∨ y = fpoint q r p d (β6, γ6, 0) ∨
        y = fpoint q r p d (0, β1, α1) ∨ y = fpoint q r p d (0, 0, 0) ∨ y = fpoint q r p d (1, 0, 0) ∨
        y = fpoint q r p d (0, 1, 0) := by
      rw [eA, eC', eA', eB', eO, eB, eC]; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24b2mCyc_0])).elim
    · exact (hyx 1 (by rw [k24b2mCyc_1])).elim
    · exact (hyx 2 (by rw [k24b2mCyc_2])).elim
    · exact (hyx 3 (by rw [k24b2mCyc_3])).elim
    all_goals
      refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      obtain ⟨hv1, hv2⟩ := hT v1 v2 hv
      refine tsc_scale hD ((k24b2m_tsc hβ hβ6' hγ6' hα1' hσ hv1 hv2).2 _ ?_ i)
      simp
  · -- Y0 -> Y1 : a <= c'
    have e0 : (1 : ZMod 4) - 1 = 0 := by decide
    rw [e0]
    refine ⟨?_, fun _ v1 v2 hv => ?_⟩
    · exact hpq.symm.le
    · have := hv (⟪c' - a, q⟫, ⟪c' - a, r⟫) (by simp)
      simp only [k24b2mCyc_0, k24b2mCyc_1, eA, eC']
      simpa using this
  · -- Y2 -> Y1 : a' < c'
    have e0 : (1 : ZMod 4) + 1 = 2 := by decide
    rw [e0]
    refine ⟨?_, fun h => ?_⟩
    · simp only [k24b2mCyc_2, k24b2mCyc_1, inner_fpoint, hqp, hrp, hspr]
      nlinarith
    · exfalso; revert h
      simp only [k24b2mCyc_2, k24b2mCyc_1, inner_fpoint, hqp, hrp, hspr]
      intro h; nlinarith
  · intro i hi
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · right
      rw [show (0 : ZMod 4) + 1 = 1 by decide]
      refine ⟨?_, fun _ v1 v2 hv => ?_⟩
      · simp only [k24b2mCyc_0, k24b2mCyc_1]; exact hpq.symm.le
      · have := hv (⟪c' - a, q⟫, ⟪c' - a, r⟫) (by simp)
        simp only [k24b2mCyc_0, k24b2mCyc_1, eA, eC']
        simpa using this
    · exact absurd rfl hi
    · left
      rw [show (2 : ZMod 4) - 1 = 1 by decide]
      refine ⟨?_, fun h => ?_⟩
      · simp only [k24b2mCyc_2, k24b2mCyc_1, inner_fpoint, hqp, hrp, hspr]
        nlinarith
      · exfalso; revert h
        simp only [k24b2mCyc_2, k24b2mCyc_1, inner_fpoint, hqp, hrp, hspr]
        intro h; nlinarith
    · right
      rw [show (3 : ZMod 4) + 1 = 0 by decide]
      refine ⟨?_, fun _ v1 v2 hv => ?_⟩
      · simp only [k24b2mCyc_3, k24b2mCyc_0, inner_fpoint, hqp, hrp, hspr]
        nlinarith
      · have := hv (⟪a - b', q⟫, ⟪a - b', r⟫) (by simp)
        simp only [k24b2mCyc_3, k24b2mCyc_0, eA, eB']
        simpa using this
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; simp
    · right; simp
    · left; simpa using hf2
    · left; simpa using hf1

end C2
end Type08Sp
end Minimality
