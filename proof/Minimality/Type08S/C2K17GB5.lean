module

public import Minimality.Type08S.C2K17GB4

@[expose] public section


/-!
# K17GB / GB5: S1.8a (TaC, `D_c = ⟪b-d,c-d⟫ = 0`, `⟪a-d,b-d⟫ = 0`, `ζ_{a-c'}(a,b') > 0 ⟺ pr > 0`):
cycle `(c',b',c,d,b)` at `d - b`, frame `(a-d, c-d, d-b)`, tilt `(rr, -λ pr)`; plateau `b', c, d` at depth 0 (`pq = qr = 0`).
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

/-- TaC frame (`K14TaC` with `pq = 0`): `α4 < 1 < β1, β6, γ4`, `α1 > 1`, `qr = 0`, and the literal
`ζ_{a-c'}(a,b') = (α1-1)(γ4 pr - (1-α4) pp)`. -/
theorem k17gb_tac_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K14TaC a a' b b' c c' d) (hpq : ⟪a - d, b - d⟫ = 0) :
    ∃ α1 α4 β1 γ4 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧ c' = d + α1 • (a - d) + β1 • (b - d) ∧
      b' = d + α4 • (a - d) + γ4 • (c - d) ∧ a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
      1 < α1 ∧ 1 < β1 ∧ 0 < α4 ∧ α4 < 1 ∧ 1 < γ4 ∧ 1 < β6 ∧ α4 * (1 - β1) = α1 * (1 - γ4) ∧
      ⟪b - d, c - d⟫ = 0 ∧
      ⟪a - b', a - c'⟫ = (α1 - 1) * (γ4 * ⟪a - d, c - d⟫ - (1 - α4) * ⟪a - d, a - d⟫) := by
  obtain ⟨hT, hκ, hP1, hP4, hP6, hqr⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hβ1p, hα4p, hγ4p, hβ6p, hpl⟩ :=
    k17gb_Tframe W hT hT' hκ
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_alpha4 hb'] at hP4
  have hα4 : α4 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  rw [det_beta1 hc'] at hP1
  have hβ1 : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hγ4 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) (by linarith : (0:ℝ) ≤ α1), mul_pos hα4p (sub_pos.2 hβ1)]
  rw [k17gb_det_beta6 ha'] at hP6
  have hβ6 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have e1 : a - b' = (1 - α4) • (a - d) + (-γ4) • (c - d) := by rw [hb']; module
  have e3 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) := by rw [hc']; module
  have hqr' : ⟪c - d, b - d⟫ = 0 := by rw [real_inner_comm]; exact hqr
  have hpq' : ⟪b - d, a - d⟫ = 0 := by rw [real_inner_comm]; exact hpq
  refine ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hβ1, hα4p, hα4, hγ4, hβ6, hpl, hqr, ?_⟩
  rw [e1, e3]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
  rw [hqr', hpq, real_inner_comm (c - d) (a - d)]
  ring

end C2
end Type08Sp
end Minimality
