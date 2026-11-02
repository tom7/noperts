module

public import Minimality.Type08S.C2K17GB0

@[expose] public section


/-!
# K17GB / GB1: T-frame preliminaries, A41 frame lemma, and S1.3b
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

theorem k17gb_det_beta6 {a a' b c d : ℝ³} {β6 : ℝ} (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) :
    det3 (a' - b) (c - d) (a - d) = (β6 - 1) * det3 (a - d) (b - d) (c - d) := by
  rw [ha']
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- T frame with planarity and the far end. -/
theorem k17gb_Tframe {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : ¬ IsT' a b c' d) (hκ : det3 (c - b) (b' - b) (c' - b) = 0) :
    ∃ α1 α4 β1 γ4 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧ c' = d + α1 • (a - d) + β1 • (b - d) ∧
      b' = d + α4 • (a - d) + γ4 • (c - d) ∧ a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
      1 < α1 ∧ 0 < β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 0 < β6 ∧ α4 * (1 - β1) = α1 * (1 - γ4) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  exact ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hfa (k5z_far2 W hT hT'), hβ1, hα4p, hγ4, hβ6,
    (planar_a_iff hdet hc' hb').1 hκ⟩

/-- A41 frame (`K6tTaA41` with the tie `ζ(d,b) = 0`): `α4 = 1`, `β1 > 1`, `γ4 > 1`, `β6 ≥ 1`, `⟪q,r⟫ = 0`,
and the literal `ζ_{a-c'}(a,b') = γ4 (α1-1) ⟪p,r⟫`.  Extra hypothesis `hT' : ¬ IsT' a b c' d` (far end `α1 > 1`). -/
theorem k17gb_a41_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hz : ⟪d - b, a - b'⟫ = 0) :
    ∃ α1 β1 γ4 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧ c' = d + α1 • (a - d) + β1 • (b - d) ∧
      b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d) ∧ a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
      1 < α1 ∧ 1 < β1 ∧ 1 < γ4 ∧ 1 ≤ β6 ∧ ⟪b - d, c - d⟫ = 0 ∧
      ⟪a - b', a - c'⟫ = γ4 * (α1 - 1) * ⟪a - d, c - d⟫ := by
  obtain ⟨hT, hκ, hP1, hP4, hP6⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hβ1p, hα4p, hγ4p, hβ6p, hpl⟩ :=
    k17gb_Tframe W hT hT' hκ
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_alpha4 hb'] at hP4
  have hα4 : α4 = 1 := by
    rcases mul_eq_zero.1 hP4 with h | h
    · linarith
    · exact absurd h hdet
  subst hα4
  rw [det_beta1 hc'] at hP1
  have hβ1 : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hγ4 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) (by linarith : (0:ℝ) ≤ α1)]
  rw [k17gb_det_beta6 ha'] at hP6
  have hβ6 : 1 ≤ β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh.le) hΔ2.le]
  have e1 : a - b' = (-γ4) • (c - d) := by rw [hb']; module
  have e2 : d - b = -(b - d) := by abel
  have e3 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) := by rw [hc']; module
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    rw [e1, e2, inner_smul_right, inner_neg_left] at hz
    have : γ4 * ⟪b - d, c - d⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  refine ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα11, hβ1, hγ4, hβ6, hqr, ?_⟩
  rw [e1, e3, inner_smul_left, inner_add_right, inner_smul_right, inner_smul_right]
  have : ⟪c - d, b - d⟫ = 0 := by rw [real_inner_comm]; exact hqr
  simp only [conj_trivial]
  rw [real_inner_comm (c - d) (a - d), this]; ring

end C2
end Type08Sp
end Minimality
