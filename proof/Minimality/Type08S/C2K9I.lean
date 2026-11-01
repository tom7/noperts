module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9H

@[expose] public section

/-!
# K9I: coordinates of a `TpA1ii` shape at the view `b - d` (frame `(P, Q, R) = (c - d, a - d, b - d)`)
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

theorem k9_setup {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : TpA1ii a a' b b' c c' d) :
    ∃ β1 γ4 β6 γ6 : ℝ, det3 (c - d) (a - d) (b - d) ≠ 0 ∧ 0 < γ4 ∧ 0 < β1 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 0 < β6 ∧
      1 < β6 + γ6 ∧ β1 < γ4 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      ⟪a - d, b - d⟫ = (1 - γ4) * ⟪c - d, b - d⟫ := by
  obtain ⟨hT', hQ, hAl, hCnn, -, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6p, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have hα41 : α4 = 1 := by
    have e1 := det_alpha (b := b) hb'
    have : (α4 - 1) * D = 0 := by rw [hD]; rw [hAl] at e1; linarith
    have := (mul_eq_zero.mp this).resolve_right hD0
    linarith
  subst hα41
  have hΔ : det3 (c - d) (a - d) (b - d) ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 (c - d) (a - d) (b - d) := by simp only [det3_expand]; ring
    rw [e, h0]
  -- the Gale data: `β1 < γ4`
  obtain ⟨μ, h1, h2⟩ := gale_coords_gen N.G hdet hc' hb' ha' (by linarith)
  have hμ : 0 < μ := by
    have : 0 < μ * (β6 * (1 - 1) + β1 * (1 - γ6)) := h2 ▸ N.hκb
    have h3 : 0 < β1 * (1 - γ6) := mul_pos hβ1 (by linarith)
    have : 0 < μ * (β1 * (1 - γ6)) := by simpa using this
    exact pos_of_mul_pos_left this h3.le
  have hβγ : β1 < γ4 := by
    have : 0 < μ * (1 - 1 * β1 - 1 + 1 * γ4) := h1 ▸ N.hκa
    have h3 : 0 < γ4 - β1 := by
      have : 0 < μ * (γ4 - β1) := by nlinarith
      exact pos_of_mul_pos_right this hμ.le
    linarith
  -- the tie from `QacTop`
  have htie : ⟪a - d, b - d⟫ = (1 - γ4) * ⟪c - d, b - d⟫ := by
    have eb' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
      rw [hb']; simp only [inner_add_left, real_inner_smul_left]; ring
    have ea : ⟪a, b - d⟫ = ⟪d, b - d⟫ + ⟪a - d, b - d⟫ := by
      nth_rewrite 1 [show a = d + (a - d) by abel]; rw [inner_add_left]
    have ec : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := by
      nth_rewrite 1 [show c = d + (c - d) by abel]; rw [inner_add_left]
    unfold QacTop at hQ
    rw [ea, eb', ec, max_eq_right (by linarith), max_eq_right (by nlinarith [mul_nonneg hγ4.le hCnn])] at hQ
    · linarith
  exact ⟨β1, γ4, β6, γ6, hΔ, hγ4, hβ1, hγ6, hγ61, hβ6p, hcv, hβγ, hc', hb', ha', htie⟩

theorem k9_pts {a a' b b' c c' d : ℝ³} {β1 γ4 β6 γ6 : ℝ}
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) :
    (∀ i, fpoint (c - d) (a - d) (b - d) d (k9Y1 γ4 β1 i) ∈ V8 a a' b b' c c' d) ∧
    (∀ y ∈ V8 a a' b b' c c' d, y = fpoint (c - d) (a - d) (b - d) d (0, 0, 1) ∨
      y = fpoint (c - d) (a - d) (b - d) d (0, 0, 0) ∨ y = fpoint (c - d) (a - d) (b - d) d (1, 0, 0) ∨
      y = fpoint (c - d) (a - d) (b - d) d (γ4, 1, 0) ∨ y = fpoint (c - d) (a - d) (b - d) d (0, 1, β1) ∨
      y = fpoint (c - d) (a - d) (b - d) d (0, 1, 0) ∨ y = fpoint (c - d) (a - d) (b - d) d (γ6, 0, β6)) ∧
    (∀ i, fpoint (c - d) (a - d) (b - d) d (k9Y2 γ4 β1 i) ∈ V8 a a' b b' c c' d) ∧
    (∀ y ∈ V8 a a' b b' c c' d, y = fpoint (c - d) (a - d) (b - d) d (0, 1, 0) ∨
      y = fpoint (c - d) (a - d) (b - d) d (0, 0, 0) ∨ y = fpoint (c - d) (a - d) (b - d) d (1, 0, 0) ∨
      y = fpoint (c - d) (a - d) (b - d) d (γ4, 1, 0) ∨ y = fpoint (c - d) (a - d) (b - d) d (0, 1, β1) ∨
      y = fpoint (c - d) (a - d) (b - d) d (0, 0, 1) ∨ y = fpoint (c - d) (a - d) (b - d) d (γ6, 0, β6)) := by
  have eO : fpoint (c - d) (a - d) (b - d) d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint (c - d) (a - d) (b - d) d (0, 0, 1) = b := by simp only [fpoint, fcomb]; module
  have eC : fpoint (c - d) (a - d) (b - d) d (1, 0, 0) = c := by simp only [fpoint, fcomb]; module
  have eA : fpoint (c - d) (a - d) (b - d) d (0, 1, 0) = a := by simp only [fpoint, fcomb]; module
  have eB' : fpoint (c - d) (a - d) (b - d) d (γ4, 1, 0) = b' := by
    rw [hb']; simp only [fpoint, fcomb]; module
  have eC' : fpoint (c - d) (a - d) (b - d) d (0, 1, β1) = c' := by
    rw [hc']; simp only [fpoint, fcomb]; module
  have eA' : fpoint (c - d) (a - d) (b - d) d (γ6, 0, β6) = a' := by
    rw [ha']; simp only [fpoint, fcomb]; module
  have hV : ∀ y ∈ V8 a a' b b' c c' d, y = b ∨ y = d ∨ y = c ∨ y = b' ∨ y = c' ∨ y = a ∨ y = a' := by
    intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k9Y1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, eO, eB, eC, eB', eC', V8]
  · intro y hy
    rw [eO, eB, eC, eB', eC', eA, eA']
    exact hV y hy
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k9Y2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, eO, eA, eC, eB', eC', V8]
  · intro y hy
    rw [eO, eB, eC, eB', eC', eA, eA']
    rcases hV y hy with h | h | h | h | h | h | h <;> simp [h]

end C2
end Type08Sp
end Minimality
