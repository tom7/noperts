module

public import Minimality.Type08S.P2RR4i3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R4a / R4i: `lexCell_TpA1_i` — `α4 = 1` at `T'` with `QacTop` and `C = ⟪c - d, b - d⟫ < 0` (case (i)).
Cell: the 5-cycle `R5 = (c', b', c, d, b)` at the base view `b - d` (R4a/HANDOFF.md).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem lexCell_TpA1_i {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hq : QacTop a b b' c d) (h1 : Al4One a b b' c d) (hC : ⟪c - d, b - d⟫ < 0) :
    HasLexCellAt (V8 a a' b b' c c' d) (b - d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set p := a - d with hp
  set q := c - d with hq'
  set r := b - d with hr
  have hΔ : det3 p q r ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = - det3 p q r := by
      simp only [hp, hq', hr, det3_expand]; ring
    rw [e, h, neg_zero]
  -- α4 = 1
  have hα : α4 = 1 := by
    have h := det_alpha (a := a) (b := b) (c := c) (d := d) hb'
    unfold Al4One at h1
    rw [h1] at h
    have : (α4 - 1) * det3 p q r = 0 := h.symm
    have := (mul_eq_zero.mp this).resolve_right hΔ
    linarith
  subst hα
  -- A = ⟪p, r⟫ = 0 from QacTop
  have hpr : ⟪p, r⟫ = 0 := by
    have hC' : ⟪c, r⟫ < ⟪d, r⟫ := by
      have := hC; rw [hq', hr] at this
      simp only [inner_sub_left] at this; linarith
    have eA : ⟪a, r⟫ = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hp, inner_sub_left]; ring
    have eB : ⟪b', r⟫ = ⟪d, r⟫ + ⟪p, r⟫ + γ4 * ⟪q, r⟫ := by
      rw [hb', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      simp only [one_smul, hp, hq', inner_sub_left]; ring
    have hg : γ4 * ⟪q, r⟫ < 0 := mul_neg_of_pos_of_neg hγ4 hC
    unfold QacTop at hq
    rw [max_eq_left hC'.le, eA, eB, max_eq_left (by linarith)] at hq
    linarith
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (1, γ4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hq']; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq']; module
  have eB1 : fpoint p q r d (0, 0, 1) = b := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, 0, β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, γ6, β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq', hr]; module
  refine r5_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hpr hC hβ1 hγ4 hγ6 hγ61 hβ6 ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [r5Cyc, pc5_0, eC']; simp [V8]
    · simp only [r5Cyc, pc5_1, eB]; simp [V8]
    · simp only [r5Cyc, pc5_2, eC]; simp [V8]
    · simp only [r5Cyc, pc5_3, eO]; simp [V8]
    · simp only [r5Cyc, pc5_4, eB1]; simp [V8]
  · intro y hy
    rw [eO, eA, eB, eC, eB1, eC', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end Type08Sp
end Minimality

