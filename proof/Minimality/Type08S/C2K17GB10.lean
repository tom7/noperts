module

public import Minimality.Type08S.C2K17GB9

@[expose] public section


/-!
# K17GB / GB10: S1.9 Gram facts.
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
/-- S1.9 depth facts for `R = b' - a'`, `u = a - c'` (two ties). -/
theorem k17gb_s19_facts {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 1 < α4)
    (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ4 : 1 < γ4) (hpl : α4 * (1 - β1) = α1 * (1 - γ4))
    (E1 : ⟪b - a', a - c'⟫ = 0) (E2 : ⟪b - b', a - c'⟫ = 0) :
    ⟪c', b' - a'⟫ = ⟪a, b' - a'⟫ ∧ (⟪c, b' - a'⟫ < ⟪b', b' - a'⟫ ∨ ⟪c, b' - a'⟫ < ⟪d, b' - a'⟫) ∧
      (⟪d, b' - a'⟫ < ⟪c, b' - a'⟫ ∨ ⟪d, b' - a'⟫ < ⟪a, b' - a'⟫) ∧
      ⟪a - c', b - d⟫ < 0 ∧ ⟪a - c', b - a'⟫ = 0 := by
  have hR : b' - a' = α4 • (a - d) + (-β6) • (b - d) + (γ4 - 1) • (c - d) := by rw [hb', ha']; module
  have hu : a - c' = (-(α1 - 1)) • (a - d) + (-β1) • (b - d) := by rw [hc']; module
  have hw : b - a' = (1 - β6) • (b - d) + (-1 : ℝ) • (c - d) := by rw [ha']; module
  have hcd : c - d = (1 - β6) • (b - d) + (-1 : ℝ) • (b - a') := by rw [ha']; module
  have hbc : b' - c = (b' - a') + β6 • (b - d) := by rw [hb', ha']; module
  have E1' : ⟪a - c', b - a'⟫ = 0 := by rw [real_inner_comm]; exact E1
  have hE1 : ⟪a - c', b - a'⟫ = 0 := by rw [real_inner_comm]; exact E1
  have hE2 : ⟪a - c', b' - a'⟫ = 0 := by
    rw [show b' - a' = (b - a') - (b - b') by abel, inner_sub_right, hE1, real_inner_comm, E2]; ring
  have hE2c : ⟪b' - a', a - c'⟫ = 0 := by rw [real_inner_comm]; exact hE2
  have E1c : ⟪b - a', a - c'⟫ = 0 := E1
  set h := α1 - 1 with hh
  set g := γ4 - 1 with hg
  have hh0 : 0 < h := by linarith
  have hg0 : 0 < g := by linarith
  set K := h * (β6 - g * (1 - β6)) + α4 * β1 with hKdef
  have hK : K = h * β6 + g * (1 - β6) + α4 * (1 + (β1 - 1) * β6) := by
    rw [hKdef, hh, hg]; linear_combination (-(1 - β6)) * hpl
  have hK0 : 0 < K := by
    rw [hK]
    have := mul_pos hh0 hβ6
    have := mul_pos hg0 (sub_pos.2 hβ61)
    have := mul_pos (by linarith : (0:ℝ) < α4) (by nlinarith : (0:ℝ) < 1 + (β1 - 1) * β6)
    linarith
  have vK : K • (b - d) = (-α4) • (a - c') + (-h) • (b' - a') + (-(h * g)) • (b - a') := by
    rw [hR, hu, hw, hKdef, hh, hg]; module
  have z0 : det3 (0 : ℝ³) (b - d) (c - d) = 0 := by simp [det3_expand]
  have hRR : 0 < ⟪b' - a', b' - a'⟫ := by
    apply real_inner_self_pos.2
    intro h0
    have e : det3 (b' - a') (b - d) (c - d) = α4 * det3 (a - d) (b - d) (c - d) := by
      rw [hR]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0, z0] at e
    exact mul_ne_zero (by linarith) hdet e.symm
  have huu : 0 < ⟪a - c', a - c'⟫ := by
    apply real_inner_self_pos.2
    intro h0
    have e : det3 (a - c') (b - d) (c - d) = (-h) * det3 (a - d) (b - d) (c - d) := by
      rw [hu]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0, z0] at e
    exact mul_ne_zero (by linarith) hdet e.symm
  -- Gram relations
  have hKY : K * ⟪b - d, b' - a'⟫ = -h * ⟪b' - a', b' - a'⟫ - (h * g) * ⟪b - a', b' - a'⟫ := by
    have := congrArg (fun v => ⟪v, b' - a'⟫) vK
    simp only [inner_smul_left, inner_add_left, conj_trivial] at this
    simp only [hE2, hE2c] at this
    linarith
  have hC : ⟪c - d, b' - a'⟫ = (1 - β6) * ⟪b - d, b' - a'⟫ - ⟪b - a', b' - a'⟫ := by
    rw [hcd]; simp only [inner_smul_left, inner_add_left, conj_trivial]; ring
  have hX : h * ⟪a - d, b' - a'⟫ + β1 * ⟪b - d, b' - a'⟫ = 0 := by
    have := congrArg (fun v => ⟪v, b' - a'⟫) hu
    simp only [inner_smul_left, inner_add_left, conj_trivial] at this
    linarith
  have hB : ⟪b', b' - a'⟫ - ⟪c, b' - a'⟫ = ⟪b' - a', b' - a'⟫ + β6 * ⟪b - d, b' - a'⟫ := by
    rw [← inner_sub_left, hbc]; simp only [inner_smul_left, inner_add_left, conj_trivial]
  have hcz : ⟪c, b' - a'⟫ - ⟪d, b' - a'⟫ = ⟪c - d, b' - a'⟫ := by rw [inner_sub_left]
  have haz : ⟪a, b' - a'⟫ - ⟪d, b' - a'⟫ = ⟪a - d, b' - a'⟫ := by rw [inner_sub_left]
  have hA : (h * g) * ⟪c - d, b' - a'⟫ = h * ⟪b' - a', b' - a'⟫ + (K + h * g * (1 - β6)) * ⟪b - d, b' - a'⟫ := by
    rw [hC]; linarith
  have hN : 0 < K + h * g * (1 - β6) := by
    have := mul_pos (mul_pos hh0 hg0) (sub_pos.2 hβ61); linarith
  have hNK : K + h * g * (1 - β6) - h * β6 > 0 := by
    rw [hK]
    have := mul_pos hg0 (sub_pos.2 hβ61)
    have := mul_pos (by linarith : (0:ℝ) < α4) (by nlinarith : (0:ℝ) < 1 + (β1 - 1) * β6)
    have := mul_pos (mul_pos hh0 hg0) (sub_pos.2 hβ61)
    linarith
  refine ⟨?_, ?_, ?_, ?_, hE1⟩
  · have : ⟪a, b' - a'⟫ - ⟪c', b' - a'⟫ = 0 := by rw [← inner_sub_left]; exact hE2
    linarith
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    set G := ⟪b' - a', b' - a'⟫
    set Y := ⟪b - d, b' - a'⟫
    set C := ⟪c - d, b' - a'⟫
    have hC0 : 0 ≤ C := by linarith
    have hGY : G + β6 * Y ≤ 0 := by linarith
    have h3 : 0 ≤ h * G + (K + h * g * (1 - β6)) * Y := by
      have := mul_nonneg (mul_pos hh0 hg0).le hC0; linarith
    nlinarith [mul_nonneg hβ6.le h3, mul_nonneg hN.le (neg_nonneg.2 hGY), mul_pos hNK hRR]
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    set G := ⟪b' - a', b' - a'⟫
    set Y := ⟪b - d, b' - a'⟫
    set C := ⟪c - d, b' - a'⟫
    have hC0 : C ≤ 0 := by linarith
    have hX0 : ⟪a - d, b' - a'⟫ ≤ 0 := by linarith
    have hY0 : 0 ≤ Y := by nlinarith [mul_nonneg hh0.le (neg_nonneg.2 hX0)]
    have := mul_nonneg hN.le hY0
    nlinarith [mul_pos hh0 hRR, mul_pos (mul_pos hh0 hg0) (by linarith : (0:ℝ) < 1), mul_nonpos_of_nonneg_of_nonpos (mul_pos hh0 hg0).le hC0]
  · have := congrArg (fun v => ⟪v, a - c'⟫) vK
    simp only [inner_smul_left, inner_add_left, conj_trivial] at this
    simp only [hE2, hE2c, E1c, E1'] at this
    rw [real_inner_comm]
    nlinarith [mul_pos hK0 huu]

end C2
end Type08Sp
end Minimality
