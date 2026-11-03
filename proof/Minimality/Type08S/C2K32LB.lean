module

public import Minimality.Type08S.C2K32LA

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

set_option maxHeartbeats 6400000 in
theorem k24b2_lt {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hdet' : det3 q r p ≠ 0 := by
    intro h; apply hdet; simp only [det3_expand] at h ⊢; linarith
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    obtain ⟨m1, -, -⟩ := hM
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hspr : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  -- W > 0
  have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by
    have hne : q - r ≠ 0 := by
      intro h0
      have : q = r := sub_eq_zero.1 h0
      rw [this] at hr2
      nlinarith [hr2]
    have := real_inner_self_pos.2 hne
    simp only [inner_sub_left, inner_sub_right, hrq] at this
    linarith
  have hs : ⟪p, q⟫ < 0 := by
    have : ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) < 0 := by
      have h' : α1 * (⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫)) < 0 := by
        have := hr1
        rw [← mul_assoc]; rw [this]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1 - 1) hr2]
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hα1'.le hh]
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hh hW.le]
  have hLs : (1 - α1) * ⟪p, p⟫ - β1 * ⟪p, q⟫ < 0 := by
    have e : a - c' = (1 - α1) • p - β1 • q := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real] at hL
    rw [hqp] at hL
    linarith
  have hα : 1 < α1 := by nlinarith [mul_neg_of_pos_of_neg hβ1' hs]
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint q r p d (0, 0, 1) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint q r p d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r p d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint q r p d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint q r p d (0, β1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint q r p d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have zd : ⟪fpoint q r p d (0, 0, 0), p⟫ = ⟪d, p⟫ := by
    simp only [inner_fpoint]; ring
  have za : ⟪fpoint q r p d (0, 0, 1), p⟫ = ⟪d, p⟫ + ⟪p, p⟫ := by
    simp only [inner_fpoint]; ring
  have zc' : ⟪fpoint q r p d (β1, 0, α1), p⟫ = ⟪d, p⟫ + β1 * ⟪p, q⟫ + α1 * ⟪p, p⟫ := by
    simp only [inner_fpoint, hqp]; ring
  have zb' : ⟪fpoint q r p d (0, β1, α1), p⟫ = ⟪d, p⟫ + β1 * ⟪p, q⟫ + α1 * ⟪p, p⟫ := by
    simp only [inner_fpoint, hrp, hspr]; ring
  have zc : ⟪fpoint q r p d (0, 1, 0), p⟫ = ⟪d, p⟫ + ⟪p, q⟫ := by
    simp only [inner_fpoint, hrp, hspr]; ring
  have hmem : ∀ i, fpoint q r p d (k24b2Cyc α1 β1 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases K.z5c i with rfl | rfl | rfl | rfl | rfl
    · simp only [k24b2Cyc, K.c5_0, eO]; simp [V8]
    · simp only [k24b2Cyc, K.c5_1, eA]; simp [V8]
    · simp only [k24b2Cyc, K.c5_2, eC']; simp [V8]
    · simp only [k24b2Cyc, K.c5_3, eB']; simp [V8]
    · simp only [k24b2Cyc, K.c5_4, eC]; simp [V8]
  refine ⟨p, hp0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) q r p d hdet' (k := 5) (by norm_num) (k24b2Cyc α1 β1)
    (k24b2_inj hα hβ) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (β6, γ6, 0)] ?_
    (u1 := -2) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v2 ∧ v1 + v2 < 0) ?_ ?_ ?_
  · intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp only [k24b2Cyc, K.c5_0, eO]⟩
    · exact Or.inl ⟨1, by simp only [k24b2Cyc, K.c5_1, eA]⟩
    · exact Or.inr ⟨(β6, γ6, 0), by simp, eA'.symm⟩
    · exact Or.inr ⟨(1, 0, 0), by simp, eB.symm⟩
    · exact Or.inl ⟨3, by simp only [k24b2Cyc, K.c5_3, eB']⟩
    · exact Or.inl ⟨4, by simp only [k24b2Cyc, K.c5_4, eC]⟩
    · exact Or.inl ⟨2, by simp only [k24b2Cyc, K.c5_2, eC']⟩
  · intro lam h0 h1
    exact ⟨by linarith, by linarith⟩
  · intro v1 v2 ⟨hv2, hv12⟩
    exact k24b2_tsc hα hβ hβ6' hγ6' hσ hv2 hv12
  · intro v1 v2 ⟨hv2, hv12⟩ hL'
    have e1 : (fun i => ⟪fpoint q r p d (k24b2Cyc α1 β1 i), p⟫) =
        K.cyc5 ⟪fpoint q r p d (0, 0, 0), p⟫ ⟪fpoint q r p d (0, 0, 1), p⟫
          ⟪fpoint q r p d (β1, 0, α1), p⟫ ⟪fpoint q r p d (0, β1, α1), p⟫ ⟪fpoint q r p d (0, 1, 0), p⟫ := by
      funext i; rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e2 : (fun i => ⟪fpoint q r p d (k24b2Cyc α1 β1 i), fcomb q r p v1 v2 0⟫) =
        K.cyc5 ⟪fpoint q r p d (0, 0, 0), fcomb q r p v1 v2 0⟫ ⟪fpoint q r p d (0, 0, 1), fcomb q r p v1 v2 0⟫
          ⟪fpoint q r p d (β1, 0, α1), fcomb q r p v1 v2 0⟫ ⟪fpoint q r p d (0, β1, α1), fcomb q r p v1 v2 0⟫
          ⟪fpoint q r p d (0, 1, 0), fcomb q r p v1 v2 0⟫ := by
      funext i; rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e1, e2]
    have zlt : ∀ X Y : ℝ, X < Y → (X, (0:ℝ)) ≠ (Y, 0) := fun X Y h e => by
      have := congrArg Prod.fst e; simp at this; linarith
    apply R2.lexUni_cyc5
    · left; show _ < _
      rw [za, zc']; nlinarith
    · left; show _ < _
      rw [zc, zb']; nlinarith
    · left; left; show _ < _
      rw [zd, za]; linarith
    · refine R2.pair_ne fun hz => ?_
      rw [zd, zc'] at hz; exfalso; nlinarith
    · refine R2.pair_ne fun hz => ?_
      rw [zd, zb'] at hz; exfalso; nlinarith
    · refine R2.pair_ne fun hz => ?_
      rw [zd, za] at hz; exfalso; linarith
    · refine R2.pair_ne fun hz => ?_
      rw [zd, zc] at hz; exfalso; linarith
    · refine R2.pair_ne fun hz => ?_
      rw [za, zb'] at hz; exfalso; nlinarith
    · refine R2.pair_ne fun hz => ?_
      rw [za, zc] at hz; exfalso; linarith
    · refine R2.pair_ne fun hz => ?_
      rw [zc, zc'] at hz; exfalso; nlinarith
    · intro e
      have h := hL' 2 3 (congrArg Prod.fst e) (congrArg Prod.snd e)
      exact absurd h (by decide)

end C2
end Type08Sp
end Minimality
