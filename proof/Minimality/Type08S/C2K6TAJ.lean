module

public import Minimality.Type08S.C2K6TAI

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
/-- **Task 2b: QTc, `α4 > 1`, `ζ(d,b) = ⟪d - b, a - b'⟫ = 0`** (`T`, `κ_c = 0`, T4 far end, `κ_b > 0`).  Either a cell at `a - b'`
(the pentagon `(a,d,c,a',c')` with a tilt chosen so that `d` is below `b` at the depth tie) or `K6tLeftZdb`.  The literal
`ζ_{a-b'}(c',c)` of the spec is not needed: both cells work iff the tilt is feasible. -/
theorem k6t1_Tc_zdb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκc : det3 (b - a) (a' - a) (b' - a) = 0)
    (hα4 : 0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d))
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hκb : 0 < galeD W.G.l W.G.m b b')
    (hζ : ⟪d - b, a - b'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftZdb a a' b b' c c' d := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  -- Gale: `E ≥ 0`
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
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = -1 / w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -γ4 / w := ⟨_, rfl⟩
  have hσw : σ * w = -1 := by rw [hσ]; field_simp
  have hκw : κ * w = -γ4 := by rw [hκ]; field_simp
  have hσ0 : σ < 0 := by rw [hσ]; exact div_neg_of_neg_of_pos (by norm_num) hw
  have hκ0 : κ < 0 := by rw [hκ]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hκσ : κ = σ * γ4 := by
    have : (κ - σ * γ4) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hb6 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (by linarith : 0 ≤ 1 - β6)]
  have hκ6 : κ * (1 - β6) = 1 := by
    have : (κ * (1 - β6) - 1) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ) := by
    have : ((σ - 1) * (1 - β1) - α1 * (σ - κ)) * w ≤ 0 := by nlinarith
    by_contra hh; push Not at hh
    nlinarith [mul_pos (sub_pos.2 hh) hw]
  have hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6) := by
    have : κ * α1 * (1 - β6) = α1 := by
      calc κ * α1 * (1 - β6) = (κ * (1 - β6)) * α1 := by ring
        _ = α1 := by rw [hκ6]; ring
    rw [← hwdef, ← hκ]; linarith
  by_cases hfeas : ∃ u1 u2 : ℝ, 0 < u1 ∧ (-γ4 / (α4 - 1)) * (α1 - 1) * u1 < β1 * u2 ∧ u2 ≠ 0 ∧
      u1 * ⟪b - d, b - d⟫ + u2 * ⟪b - d, c - d⟫ < 0
  · exact Or.inl (k6t1_zdb_core hdet hc' hb' ha' hα11 hα41 hβ1 hγ4 hb6.le hbc0 hE0 hζ hfeas)
  · exact Or.inr ⟨α1, α4, β1, γ4, β6, hc', hb', ha', hα41, hζ, hfeas⟩

end C2
end Type08Sp
end Minimality
