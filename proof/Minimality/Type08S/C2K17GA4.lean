module

public import Minimality.Type08S.C2K17GA3
public import Minimality.Type08S.C2K17GA1

@[expose] public section

/-!
# K17GA / GA4: R3 wrappers (Ta and Tc), cell `(a,d,b,a',b')@a-c'`
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

/-- Coordinates of the Zdb(i) Tc context. -/
theorem k17ga_tc_coords {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d) :
    ∃ α1 α4 β1 γ4 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧ c' = d + α1 • (a - d) + β1 • (b - d) ∧
      b' = d + α4 • (a - d) + γ4 • (c - d) ∧ a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
      1 < α1 ∧ 1 < α4 ∧ 0 < β1 ∧ 0 < γ4 ∧ 1 ≤ β6 ∧ α4 - 1 = γ4 * (β6 - 1) ∧
      0 ≤ α4 - α4 * β1 - α1 + α1 * γ4 := by
  obtain ⟨⟨hT, hT', hκc, -⟩, hα4, hζ0, -⟩ := h
  have hfar := k5z_far2 W hT hT'
  have hκb := k5z_kb_pos W hT hT'
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  obtain ⟨μ, hμa, hμb⟩ := gale_pt W hdet hc' hb' ha' (by linarith)
  have hμ : 0 < μ := by
    rw [hμb] at hκb
    have : 0 < β6 * (α1 - 1) := mul_pos hβ6 (by linarith)
    by_contra hh; push Not at hh
    nlinarith
  have hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4 := by
    have := W.hκa
    rw [hμa] at this
    exact nonneg_of_mul_nonneg_right this hμ
  have hb6 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (by linarith : 0 ≤ 1 - β6)]
  exact ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6.le, by linarith, hE0⟩

end C2
end Type08Sp
end Minimality
