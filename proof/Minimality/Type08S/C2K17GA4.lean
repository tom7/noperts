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

/-- **S1.1 R3, Ta regime**: `ζ_{a-c'}(c',a') > 0` gives the cell `(a,d,b,a',b')@a-c'`. -/
theorem k17ga_s11_r3_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) (hL : 0 < ⟪c' - a', a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hbc0, hE0⟩ :=
    k17ga_ta_coords W h
  have hg : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ1), mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
  exact k17ga_r3_core hdet hc' hb' ha' hα11 (by linarith) hα41 hg hb6
    (by nlinarith [mul_nonneg (mul_pos hγ4 (by linarith : (0:ℝ) < α1)).le (sub_nonneg.2 hb6), mul_pos (sub_pos.2 hα41) (sub_pos.2 hβ1)])
    hζ0 hz1 hL

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

set_option maxHeartbeats 3200000 in
/-- **S1.1 R3, Tc regime**: with `qr = ⟪b-d,c-d⟫ ≥ 0`, `ζ_{c'-b}(d,b) < 0` and `ζ_{a-c'}(c',a') > 0`,
the cell `(a,d,b,a',b')@a-c'`. -/
theorem k17ga_s11_r3_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) (hq : 0 ≤ ⟪b - d, c - d⟫) (h3 : ⟪d - b, c' - b⟫ < 0)
    (hL : 0 < ⟪c' - a', a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hpl, hE0⟩ :=
    k17ga_tc_coords W h
  have hqq : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 (by
    intro h0; apply hdet
    have : b - d = 0 := h0
    rw [this]; simp [det3_expand])
  have v3 : d - b = (0 : ℝ) • (a - d) + (-1 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have v2 : a - b' = (-(α4 - 1)) • (a - d) + (0 : ℝ) • (b - d) + (-γ4) • (c - d) := by rw [hb']; module
  have v6 : c' - b = α1 • (a - d) + (β1 - 1) • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have E1' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v2
  have h3' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v6
  rw [E1'] at hζ0
  rw [h3'] at h3
  have hpq : ⟪a - d, b - d⟫ ≤ 0 := by
    have hqr : ⟪b - d, c - d⟫ = -((α4 - 1) * ⟪a - d, b - d⟫) / γ4 := by
      field_simp; rw [real_inner_comm (b - d) (a - d)] at *; nlinarith [hζ0]
    rw [hqr] at hq
    have : 0 ≤ -((α4 - 1) * ⟪a - d, b - d⟫) := by
      by_contra hh; push Not at hh
      have := div_neg_of_neg_of_pos hh hγ4; linarith
    nlinarith
  have hβ : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1) (neg_nonneg.2 hpq), mul_nonneg (sub_nonneg.2 hh) hqq.le]
  have hg : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ), mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
  exact k17ga_r3_core hdet hc' hb' ha' hα11 (by linarith) hα41 hg hb6
    (by nlinarith [mul_nonneg (mul_pos hγ4 (by linarith : (0:ℝ) < α1)).le (sub_nonneg.2 hb6), mul_pos (sub_pos.2 hα41) (sub_pos.2 hβ)])
    (by rw [E1'] ; linarith) hz1 hL

end C2
end Type08Sp
end Minimality
