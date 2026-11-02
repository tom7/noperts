module

public import Minimality.Type08S.C2K6HD1
public import Minimality.Type08S.C2K6HD2

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Leaf L4 of the H1 tree (`ζ_{d-a'}(a, c') ≤ 0`): the literal forces `ζ_{a-c'}(b, a') < 0`, then H4's second
cell `(c', b', a', b)` (the `b ↔ c` mirror of H2's cell 2). -/
theorem k6mh1_L4 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hl : ⟪a - c', d - a'⟫ ≤ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hm2 : 0 < ⟪q, q⟫ - ⟪q, r⟫ := by
    have e : ⟪c' - d, b - c⟫ = α1 * (⟪p, q⟫ - ⟪p, r⟫) + β1 * (⟪q, q⟫ - ⟪q, r⟫) := by
      have : c' - d = α1 • p + β1 • q + (0:ℝ) • r := by rw [hc']; simp only [hp, hq]; module
      have h2 : b - c = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by rw [hq, hr]; module
      rw [this, h2, k6m_ip]; ring
    rw [hm1] at e
    nlinarith
  have e1 : a - c' = (1 - α1) • p + (-β1) • q + (0:ℝ) • r := by rw [hc', hp, hq]; module
  have e2 : b - a' = (0:ℝ) • p + (1 - β6) • q + (-γ6) • r := by rw [ha', hq, hr]; module
  have e3 : d - a' = (0:ℝ) • p + (-β6) • q + (-γ6) • r := by rw [ha', hq, hr]; module
  rw [e1, e3, k6m_ip] at hl
  have hneg : ⟪b - a', a - c'⟫ < 0 := by
    rw [e2, e1, k6m_ip, ← hm1]
    rw [← hm1] at hl
    rcases le_or_gt 0 ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, q⟫) with h0 | h0
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β6 - 1) h0, mul_nonneg (by linarith : (0:ℝ) ≤ γ6) h0,
        mul_pos (by linarith : (0:ℝ) < γ6) (mul_pos (by linarith : (0:ℝ) < β1) hm2)]
    · nlinarith [mul_pos (by linarith : (0:ℝ) < β6) (neg_pos.2 h0)]
  have := k6mh1_cell2 (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hβ6
    (k6m_M_swap ⟨m1, m2, m3⟩) hneg
  rwa [k6m_V8_swap] at this

end C2
end Type08Sp
end Minimality
