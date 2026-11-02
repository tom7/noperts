module

public import Minimality.Type08S.C2K16M

@[expose] public section


/-!
# K16 / N: H5 rule r0 (`ζ_{b'-a'}(d, c) > 0`) by the swap; the H5 leftover cut by r1, r9, r2, r0.
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

/-- **H5 rule r0** (`ζ_{b'-a'}(d, c) > 0`, view `b' - a'`). -/
theorem k16_r0_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hlit : 0 < ⟪d - c, b' - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have := k16_r2_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hγ61 hβ6 hβ61
    (by linarith) (k6m_M_swap hM) hlit
  rwa [k6m_V8_swap] at this

/-- `K16mH5` with the rules r2 (`ζ_{c'-a'}(d, b) > 0`) and r0 (`ζ_{b'-a'}(d, c) > 0`) removed as well. -/
def K16mH5b (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K16mH5 a a' b c c' d α1 β1 β6 γ6 ∧ ⟪d - b, c' - a'⟫ ≤ 0 ∧ ⟪d - c, b' - a'⟫ ≤ 0

theorem k16_h5_step2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K14mH5 a c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16mH5b a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  have hC' : K6mCoords a a' b b' c c' d α1 β1 β6 γ6 := ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩
  obtain ⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl4⟩ := h
  by_cases l2 : 0 < ⟪d - b, c' - a'⟫
  · exact Or.inl (k16_r2_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l2)
  by_cases l0 : 0 < ⟪d - c, b' - a'⟫
  · exact Or.inl (k16_r0_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l0)
  rcases k16_h5_step hC' hM hrel ⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl4⟩ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, not_lt.1 l2, not_lt.1 l0⟩

end C2
end Type08Sp
end Minimality
