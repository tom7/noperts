module

public import Minimality.Type08S.C2K17GA5

@[expose] public section


/-!
# K17GA / GA6: R2 wrapper (S1.1a, Tc)
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

set_option maxHeartbeats 3200000 in
/-- **S1.1 R2 (K15 S1.1a), Tc regime**: with `ζ_{c'-b}(d,b) = ⟪d-b,c'-b⟫ > 0` the cell `(c',b',c,a',b)@d-b`. -/
theorem k17ga_s11_r2_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) (hl : 0 < ⟪d - b, c' - b⟫) : HasLexCell (V8 a a' b b' c c' d) := by
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
  have v7 : a - d = (1 : ℝ) • (a - d) + (0 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have v8 : c - d = (0 : ℝ) • (a - d) + (0 : ℝ) • (b - d) + (1 : ℝ) • (c - d) := by module
  have E1' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v2
  have h3' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v6
  have i1 := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v7 v3
  have i2 := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v8 v3
  have i3 := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v3
  rw [E1'] at hζ0
  rw [h3'] at hl
  have hw : 0 < α4 - 1 := by linarith
  have hb61 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (sub_nonneg.2 hh)]
  -- qr = -(β6-1) pq
  have hqr : ⟪b - d, c - d⟫ = -(β6 - 1) * ⟪a - d, b - d⟫ := by
    have : γ4 * (⟪b - d, c - d⟫ + (β6 - 1) * ⟪a - d, b - d⟫) = 0 := by linear_combination hζ0 - ⟪a - d, b - d⟫ * hpl
    have := (mul_eq_zero.1 this).resolve_left hγ4.ne'
    linarith
  have hpq : ⟪a - d, b - d⟫ < ⟪b - d, b - d⟫ := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh), mul_pos hqq (by linarith : (0:ℝ) < α1 + β1 - 1)]
  have hcv : 0 < α4 - α1 + α1 * γ4 := by nlinarith [mul_pos (by linarith : (0:ℝ) < α4) hβ1]
  refine k17ga_r2_cell hdet hc' hb' ha' hα11 hβ1 (by linarith) hγ4 hb6 hcv ?_ ?_ ?_
  · rw [i2, i3, hqr]; nlinarith [mul_pos (by linarith : (0:ℝ) < β6 - 1) (sub_pos.2 hpq)]
  · rw [i1, i3]; nlinarith
  · rw [i1, i2, i3, hqr]
    rcases lt_or_ge ⟪a - d, b - d⟫ 0 with hh | hh
    · right; nlinarith [mul_pos (by linarith : (0:ℝ) < β6) (neg_pos.2 hh)]
    · left; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1 - 1) hh, mul_pos hβ1 hqq]

end C2
end Type08Sp
end Minimality
