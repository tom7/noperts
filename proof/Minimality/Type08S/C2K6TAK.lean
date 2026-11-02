module

public import Minimality.Type08S.C2K6TAJ

@[expose] public section


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

set_option maxHeartbeats 3200000 in
/-- **Task 4g: QTa box D (`β1 > 1`, `α4 > 1`, `β6 > 1`), `ζ_D = ζ(d,b) = 0`.**  Same as 2b: a cell at `a - b'` or `K6tLeftZdb`. -/
theorem k6t1_Ta_zD {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκa : det3 (c - b) (b' - b) (c' - b) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hζ : ⟪d - b, a - b'⟫ = 0)
    (hβ1d : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hα4 : 0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d))
    (hβ6d : 0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d)) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftZdb a a' b b' c c' d := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκa
  have hD2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by nlinarith
  rw [det_beta1 hc'] at hβ1d
  have hβ11 : 1 < β1 := by nlinarith
  rw [k5f_det_beta6 ha'] at hβ6d
  have hb6 : 1 ≤ β6 := by nlinarith
  have hE0 : α4 - α4 * β1 - α1 + α1 * γ4 = 0 := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -γ4 / w := ⟨_, rfl⟩
  have hκ0 : κ < 0 := by rw [hκ]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6) := by
    rw [← hwdef, ← hκ]
    have : 0 ≤ κ * α1 * (1 - β6) := by
      have h1 : κ * α1 < 0 := by nlinarith
      nlinarith
    linarith
  by_cases hfeas : ∃ u1 u2 : ℝ, 0 < u1 ∧ (-γ4 / (α4 - 1)) * (α1 - 1) * u1 < β1 * u2 ∧ u2 ≠ 0 ∧
      u1 * ⟪b - d, b - d⟫ + u2 * ⟪b - d, c - d⟫ < 0
  · exact Or.inl (k6t1_zdb_core hdet hc' hb' ha' hα11 hα41 hβ1 hγ4 hb6 hbc0 hE0.ge hζ hfeas)
  · exact Or.inr ⟨α1, α4, β1, γ4, β6, hc', hb', ha', hα41, hζ, hfeas⟩

end C2
end Type08Sp
end Minimality
