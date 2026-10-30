module

public import Minimality.Type08S.P2RQ3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R5a / R5: `lexCell_P3Tp_n` — tpq's P3 tie at `T'` with `D_c = ⟪c - d, b - d⟫ < 0`.
Cell: the 5-cycle `(c', b', c, d, b)` at the base view `b - d`, tilt `(-1, μ, 0)`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem lexCell_P3Tp_n {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : StP3Tp a b b' c c' d)
    (h1 : ¬ Al4One a b b' c d) (hC : ⟪c - d, b - d⟫ < 0) :
    HasLexCellAt (V8 a a' b b' c c' d) (b - d) := by
  have hT' := h.1
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
  have hpr : ⟪p, r⟫ = 0 := by
    obtain ⟨-, -, he, -⟩ := h
    simp only [hp, hr, inner_sub_left] at he ⊢; linarith
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (α4, γ4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hq']; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq']; module
  have eB1 : fpoint p q r d (0, 0, 1) = b := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, 0, β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, γ6, β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq', hr]; module
  refine r5A_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hpr hC hα4 hαγ hβ1 hγ4 hγ6 hγ61 hβ6 ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [r5CycA, pc5_0, eC']; simp [V8]
    · simp only [r5CycA, pc5_1, eB]; simp [V8]
    · simp only [r5CycA, pc5_2, eC]; simp [V8]
    · simp only [r5CycA, pc5_3, eO]; simp [V8]
    · simp only [r5CycA, pc5_4, eB1]; simp [V8]
  · intro y hy
    rw [eO, eA, eB, eC, eB1, eC', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end Type08Sp
end Minimality

