module

public import Minimality.Type08S.C2K17GB11

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **S1.9**: `K6tTaE` (with `¬ T'`) plus the second tie `⟪b-b',a-c'⟫ = 0`: a lex cell (no literal, no leftover). -/
theorem k17gb_s19 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaE a a' b b' c c' d) (h2 : ⟪b - b', a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT, hκ, hP1, hP4, hP6, hE⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1p, hα4p, hγ4p, hβ6p, hpl⟩ :=
    k17gb_Tframe W hT hT' hκ
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_alpha4 hb'] at hP4
  have hα4 : 1 < α4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  rw [det_beta1 hc'] at hP1
  have hβ1 : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  rw [k17gb_det_beta6 ha'] at hP6
  have hβ6 : β6 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hγ4 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) (by linarith : (0:ℝ) ≤ α1), mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ1)]
  exact k17gb_s19_cell hdet hc' hb' ha' hα1 hβ1 hα4 hβ6p hβ6 hγ4 hpl hE h2

end C2
end Type08Sp
end Minimality
