module

public import Minimality.Type08S.C2K17GD4B

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
/-- **K14TaC, generic part**: a lex cell, or the leftover `⟪a-d,b-d⟫ = 0` (`ζ(a,d) = 0`).  Needs `hfar := k5z_far2 W hT hT'`. -/
theorem k17gd_taC {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K14TaC a a' b b' c c' d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, b - d⟫ = 0 := by
  obtain ⟨hT, hκc, hβ1p, hα4p, hβ6p, hDc⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκc
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  rw [det_beta1 hc'] at hβ1p
  rw [det_alpha4 hb'] at hα4p
  rw [k5f_det_beta6 ha'] at hβ6p
  have hβ11 : 1 < β1 := by nlinarith
  have hα41 : α4 < 1 := by nlinarith
  have hβ61 : 1 < β6 := by nlinarith
  have hγ41 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ 1 - γ4), mul_pos hα4 (sub_pos.2 hβ11)]
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hq0 : q ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
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
  have A_b' : fpoint p q r d (α4, 0, γ4) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have D_a : fpoint p r q d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have D_c' : fpoint p r q d (α1, 0, β1) = c' := by rw [hfp, hc']; simp only [hp, hq]; module
  have D_b' : fpoint p r q d (α4, γ4, 0) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have D_c : fpoint p r q d (0, 1, 0) = c := by rw [hfp]; simp only [hr]; module
  have D_d : fpoint p r q d (0, 0, 0) = d := by rw [hfp]; module
  have D_b : fpoint p r q d (0, 0, 1) = b := by rw [hfp]; simp only [hq]; module
  have D_a' : fpoint p r q d (0, 1, β6) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
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
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4) := by
    intro y hy
    rw [A_a, A_c', A_a', A_b, A_d, A_c, A_b']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hmemD : ∀ i, fpoint p r q d (k17gdD α1 β1 α4 γ4 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gdD, pc5_0, D_a]; simp [V8]
    · simp only [k17gdD, pc5_1, D_c']; simp [V8]
    · simp only [k17gdD, pc5_2, D_b']; simp [V8]
    · simp only [k17gdD, pc5_3, D_c]; simp [V8]
    · simp only [k17gdD, pc5_4, D_d]; simp [V8]
  have hVD : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (α1, 0, β1) ∨
      y = fpoint p r q d (α4, γ4, 0) ∨ y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨
      y = fpoint p r q d (0, 0, 1) ∨ y = fpoint p r q d (0, 1, β6) := by
    intro y hy
    rw [D_a, D_c', D_b', D_c, D_d, D_b, D_a']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hqr : ⟪q, r⟫ = 0 := hDc
  have hrq : ⟪r, q⟫ = 0 := by rw [real_inner_comm]; exact hDc
  rcases lt_trichotomy ⟪p, q⟫ 0 with hneg | hzero | hpos
  · exact Or.inl ⟨r, hr0, k17gdC1b_frame (V8 a a' b b' c c' d) p q r d hdet hα11 hβ1 hβ61 hα4 hα41 hγ4 hqr hneg hmemA hVA⟩
  · exact Or.inr hzero
  · exact Or.inl ⟨q, hq0, k17gdD_frame (V8 a a' b b' c c' d) p q r d hΔ' hα11 hβ1 hα4 hα41 hγ41 hβ61 hrq hpos hmemD hVD⟩

end C2
end Type08Sp
end Minimality
