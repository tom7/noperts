module

public import Minimality.Type08S.C2K17GD3B

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

set_option maxHeartbeats 3200000 in
/-- **K6tTaA41, generic part**: a lex cell, or the leftover `⟪b-d,c-d⟫ = 0` (`ζ(d,b) = 0`).  Needs `hfar := k5z_far2 W hT hT'`
(from `K5ZsTa`).  Covers `β6 ≥ 1` including `β6 = 1`; the `ζ(d,b) = 0` tie is the only leftover. -/
theorem k17gd_taA41 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6tTaA41 a a' b b' c c' d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨hT, hκc, hβ1p, hα4, hβ6p⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 hα4 with h | h
    · linarith
    · exact absurd h hdet
  subst hα41
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  rw [k5f_det_beta6 ha'] at hβ6p
  have hβ61 : 1 ≤ β6 := by nlinarith
  have hE0 : 0 ≤ 1 - β1 - α1 + α1 * γ4 := by linarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hq0 : q ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hΔ' : det3 p r q ≠ 0 := by
    have : det3 p r q = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hdet
  have hfp : ∀ (u v w : ℝ³) (x y z : ℝ), fpoint u v w d (x, y, z) = d + x • u + y • v + z • w := by
    intro u v w x y z; simp only [fpoint, fcomb]; module
  have A_a : fpoint p q r d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have A_c' : fpoint p q r d (α1, β1, 0) = c' := by rw [hfp, hc']; simp only [hp, hq]; module
  have A_a' : fpoint p q r d (0, β6, 1) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  have A_c : fpoint p q r d (0, 0, 1) = c := by rw [hfp]; simp only [hr]; module
  have A_d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have A_b : fpoint p q r d (0, 1, 0) = b := by rw [hfp]; simp only [hq]; module
  have A_b' : fpoint p q r d (1, 0, γ4) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have B_c' : fpoint p r q d (α1, 0, β1) = c' := by rw [hfp, hc']; simp only [hp, hq]; module
  have B_b' : fpoint p r q d (1, γ4, 0) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have B_c : fpoint p r q d (0, 1, 0) = c := by rw [hfp]; simp only [hr]; module
  have B_d : fpoint p r q d (0, 0, 0) = d := by rw [hfp]; module
  have B_b : fpoint p r q d (0, 0, 1) = b := by rw [hfp]; simp only [hq]; module
  have B_a : fpoint p r q d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have B_a' : fpoint p r q d (0, 1, β6) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  have hmemA : ∀ i, fpoint p q r d (k17gdC1 α1 β1 β6 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gdC1, pc5_0, A_a]; simp [V8]
    · simp only [k17gdC1, pc5_1, A_c']; simp [V8]
    · simp only [k17gdC1, pc5_2, A_a']; simp [V8]
    · simp only [k17gdC1, pc5_3, A_b]; simp [V8]
    · simp only [k17gdC1, pc5_4, A_d]; simp [V8]
  have hVA : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6, 1) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (1, 0, γ4) := by
    intro y hy
    rw [A_a, A_c', A_a', A_b, A_d, A_c, A_b']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hmemB : ∀ i, fpoint p r q d (k17gdB α1 β1 γ4 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gdB, pc5_0, B_c']; simp [V8]
    · simp only [k17gdB, pc5_1, B_b']; simp [V8]
    · simp only [k17gdB, pc5_2, B_c]; simp [V8]
    · simp only [k17gdB, pc5_3, B_d]; simp [V8]
    · simp only [k17gdB, pc5_4, B_b]; simp [V8]
  have hVB : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p r q d (α1, 0, β1) ∨ y = fpoint p r q d (1, γ4, 0) ∨
      y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨ y = fpoint p r q d (0, 0, 1) ∨
      y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (0, 1, β6) := by
    intro y hy
    rw [B_c', B_b', B_c, B_d, B_b, B_a, B_a']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hqr : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  rcases lt_trichotomy ⟪q, r⟫ 0 with hneg | hzero | hpos
  · refine Or.inl ⟨q, hq0, k17gdB_frame6 (V8 a a' b b' c c' d) p q r d hΔ' hα11 hβ1 hγ4 hβ6 hE0 hrr
      (max 0 (1 - γ4) + 1) (by linarith) (Or.inl (by rw [hqr]; exact hneg)) hmemB hVB⟩
  · exact Or.inr hzero
  · exact Or.inl ⟨r, hr0, k17gdC1_frame (V8 a a' b b' c c' d) p q r d hdet hα11 hβ1 hβ61 hγ4 hpos hmemA hVA⟩

end C2
end Type08Sp
end Minimality
