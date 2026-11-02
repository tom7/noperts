module

public import Minimality.Type08S.C2K6MO

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6m_V8_swap (a a' b b' c c' d : ℝ³) : V8 a a' c c' b b' d = V8 a a' b b' c c' d := by
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem k6m_M_swap {a a' b b' c c' d : ℝ³} (h : K6sM a a' b b' c c' d) : K6sM a a' c c' b b' d := by
  obtain ⟨m1, m2, m3⟩ := h
  have e : c - b = -(b - c) := by abel
  refine ⟨?_, ?_, ?_⟩
  · rw [e, inner_neg_right, m1]; simp
  · rw [e, inner_neg_right]; linarith
  · rw [e, inner_neg_right]; linarith

/-- **Box H4** (`α1, β1 > 1`, `0 < β6 < 1 < γ6`; view `a - c'`): the `b ↔ c` mirror of H2 (`K6sM` is symmetric). -/
theorem k6m_H4_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hlit : ⟪b - a', a - c'⟫ ≠ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have := k6m_H2_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hβ6 hβ61
    (k6m_M_swap hM) hlit
  rwa [k6m_V8_swap] at this

end C2
end Type08Sp
end Minimality
