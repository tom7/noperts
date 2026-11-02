module

public import Minimality.Type08S.C2K17GA7

@[expose] public section


/-!
# K17GA / GA8: S1.3a wrapper (TaA41, `ζ(d,b) = 0`, `ζ_{a-c'}(a,b') > 0`): cell `(a,d,b,a',b')@a-c'`
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
/-- **S1.3a**: `K6tTaA41`, `ζ(d,b) = ⟪d-b,a-b'⟫ = 0`, `ζ_{a-c'}(a,b') = ⟪a-b',a-c'⟫ > 0` (and `¬ IsT' a b c' d`, which
`K6tTaA41` does not carry) give the cell `(a,d,b,a',b')@a-c'`. -/
theorem k17ga_s13a {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hζ0 : ⟪d - b, a - b'⟫ = 0) (hl : 0 < ⟪a - b', a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT, hκa, hβ1d, hα4, hβ6d⟩ := h
  have hfar := k5z_far2 W hT hT'
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκa
  have hD2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  rw [det_beta1 hc'] at hβ1d
  have hβ11 : 1 < β1 := by nlinarith
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 = 1 := by
    have : (α4 - 1) * det3 (a - d) (b - d) (c - d) = 0 := hα4
    have := (mul_eq_zero.1 this).resolve_right hdet
    linarith
  rw [k5f_det_beta6 ha'] at hβ6d
  have hb6 : 1 ≤ β6 := by nlinarith
  have hg : 1 < γ4 := by
    subst hα41
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
  have hUne : (α1 - 1) • (a - d) + β1 • (b - d) ≠ 0 := by
    intro h0
    have e : det3 ((α1 - 1) • (a - d) + β1 • (b - d)) (b - d) (c - d) = (α1 - 1) * det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0] at e
    have : (α1 - 1) * det3 (a - d) (b - d) (c - d) = 0 := by rw [← e]; simp [det3_expand]
    exact hdet ((mul_eq_zero.1 this).resolve_left (by linarith))
  have v1 : a - c' = (-(α1 - 1)) • (a - d) + (-β1) • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have v2 : a - b' = (-(α4 - 1)) • (a - d) + (0 : ℝ) • (b - d) + (-γ4) • (c - d) := by rw [hb']; module
  have v3 : d - b = (0 : ℝ) • (a - d) + (-1 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have vp : a - d = (1 : ℝ) • (a - d) + (0 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have vq : b - d = (0 : ℝ) • (a - d) + (1 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have vr : c - d = (0 : ℝ) • (a - d) + (0 : ℝ) • (b - d) + (1 : ℝ) • (c - d) := by module
  have vU : (α1 - 1) • (a - d) + β1 • (b - d) = (α1 - 1) • (a - d) + β1 • (b - d) + (0 : ℝ) • (c - d) := by module
  have E1 := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v2
  have Lh := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v2 v1
  have cp := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ vp v1
  have cq := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ vq v1
  have cr := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ vr v1
  have cU := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ vU v1
  have cUU := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ vU vU
  have hUU : 0 < ⟪(α1 - 1) • (a - d) + β1 • (b - d), (α1 - 1) • (a - d) + β1 • (b - d)⟫ :=
    real_inner_self_pos.2 hUne
  rw [E1] at hζ0
  rw [Lh] at hl
  subst hα41
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    have : γ4 * ⟪b - d, c - d⟫ = 0 := by nlinarith [hζ0]
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have hpr : 0 < ⟪a - d, c - d⟫ := by
    have : 0 < γ4 * ((α1 - 1) * ⟪a - d, c - d⟫) := by nlinarith [hl, hqr]
    have := pos_of_mul_pos_right this hγ4.le
    exact pos_of_mul_pos_right (by linarith) (by linarith : (0:ℝ) ≤ α1 - 1)
  refine k17ga_a41_cell hdet hc' hb' ha' hα11 (by linarith) le_rfl hg hb6 rfl ?_ ?_ ?_
  · rw [cr]; nlinarith
  · rw [cp, cq]
    rw [cU] at *
    nlinarith
  · intro hx
    rw [cq] at hx ⊢
    rw [cr]
    nlinarith [mul_nonneg (sub_nonneg.2 hb6) (neg_nonneg.2 hx)]

end C2
end Type08Sp
end Minimality
