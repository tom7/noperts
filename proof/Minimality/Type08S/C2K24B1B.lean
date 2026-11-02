module

public import Minimality.Type08S.C2K24B1A

@[expose] public section


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

set_option maxHeartbeats 6400000 in
theorem k24b1_cell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ}
    (W : Norm08w a a' b b' c c' d) (hC : K6mCoords a a' b b' c c' d 1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d 1 β1)
    (hβ : 1 < β1) (hβs : β1 < β6 + γ6) :
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
    have e : c' - d = (1:ℝ) • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : (1:ℝ) * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = (1:ℝ) • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : (1:ℝ) * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  -- s = <p,q> < 0 from Rel
  have hs : ⟪p, q⟫ < 0 := by
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have e : ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) =
        -(β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) := by
      have := hr1
      simp only [one_mul] at this
      exact this
    have : ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) < 0 := by
      rw [e]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1 - 1) hr2]
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hh hW.le]
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint q r p d (0, 0, 1) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint q r p d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r p d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint q r p d (β1, 0, 1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint q r p d (0, β1, 1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint q r p d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have key : ∀ x y z : ℝ, ⟪x • q + y • r + z • p, p⟫ = x * ⟪p, q⟫ + y * ⟪p, r⟫ + z * ⟪p, p⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hqp, hrp]
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, p⟫ → ⟪X, p⟫ < ⟪Y, p⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hspr : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  refine ⟨p, hp0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) q r p d hdet' (k := 4) (by norm_num) (k24b1Cyc β1 β6 γ6)
    (k24b1_inj hβ hβ6' hγ6') ?_ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)] ?_
    (u1 := 1) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k24b1Cyc_0, eA]; simp [V8]
    · simp only [k24b1Cyc_1, eC']; simp [V8]
    · simp only [k24b1Cyc_2, eA']; simp [V8]
    · simp only [k24b1Cyc_3, eB']; simp [V8]
  · intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨(0, 0, 0), by simp, eO.symm⟩
    · exact Or.inl ⟨0, by rw [k24b1Cyc_0, eA]⟩
    · exact Or.inl ⟨2, by rw [k24b1Cyc_2, eA']⟩
    · exact Or.inr ⟨(1, 0, 0), by simp, eB.symm⟩
    · exact Or.inl ⟨3, by rw [k24b1Cyc_3, eB']⟩
    · exact Or.inr ⟨(0, 1, 0), by simp, eC.symm⟩
    · exact Or.inl ⟨1, by rw [k24b1Cyc_1, eC']⟩
  · intro lam h0 h1
    exact ⟨by simp only [mul_one, mul_zero, add_zero]; linarith, by simp⟩
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k24b1_tsc hβ hβ6' hγ6' hβs hv1 hv2
  · intro v1 v2 ⟨hv1, hv2⟩ hL
    refine k14_quad_uni_h5 _ _ hL ?_ ?_ ?_ ?_
    · simp only [k24b1Cyc_1, k24b1Cyc_0, inner_fpoint, hqp, hrp, hspr]
      nlinarith
    · simp only [k24b1Cyc_3, k24b1Cyc_0, inner_fpoint, hqp, hrp, hspr]
      nlinarith
    · simp only [k24b1Cyc_2, k24b1Cyc_1, inner_fpoint, hqp, hrp, hspr]
      nlinarith
    · simp only [k24b1Cyc_2, k24b1Cyc_3, inner_fpoint, hqp, hrp, hspr]
      nlinarith

end C2
end Type08Sp
end Minimality
