module

public import Minimality.Type08S.C2K16H

@[expose] public section


/-!
# K16 / I: H5 rule r9 (`ζ_{d-b}(b, a') < 0`) by the `b ↔ c` swap; the two rules as one step on `K14mH5`.
-/
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

theorem k16_rel_swap {a b c d : ℝ³} {α1 β1 : ℝ} (hρ : ⟪a - d, b - c⟫ = 0)
    (h : K16Rel a b c d α1 β1) : K16Rel a c b d α1 β1 := by
  unfold K16Rel at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hs : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
    have : ⟪a - d, b - c⟫ = ⟪a - d, b - d⟫ - ⟪a - d, c - d⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    linarith
  have hc := real_inner_comm (b - d) (c - d)
  refine ⟨?_, ?_⟩
  · rw [hs, hc]; linear_combination h1
  · rw [hc]; linarith [h2]

/-- **H5 rule r9** (`ζ_{d-b}(b, a') < 0`). -/
theorem k16_r9_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1) (hlit : ⟪b - a', d - b⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have := k16_r1_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hγ61 hβ6 hβ61
    (by linarith) (k6m_M_swap hM) (k16_rel_swap hM.1 hrel) hlit
  rwa [k6m_V8_swap] at this

end C2
end Type08Sp
end Minimality
