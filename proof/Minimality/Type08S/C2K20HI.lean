module

public import Minimality.Type08S.C2K20HH
public import Minimality.Type08S.C2K20HF

@[expose] public section


/-!
# K20H5 / I: H5 rule r6 (swap of r7) and the step `k20h_h5 : K16mH5b → HasLexCell ∨ K20mH5c`.
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

/-- **H5 rule r6** (line view `L06`): the `b <-> c` swap of r7. -/
theorem k20_r6_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d)
    (hlit0 : (β1 - 1) * (α1 - 1) * β6 < α1 * β1 * (1 - γ6))
    (hlit : 0 < ⟪a' - b, k20V7 a b d (α1 * (1 - γ6)) ((β1 - 1) * β6)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have := k20_r7_hasLexCell (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d)
    (α1 := α1) (β1 := β1) (β6 := γ6) (γ6 := β6) hdet' hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hγ61 hβ6 hβ61
    (by linarith) (k6m_M_swap hM) hlit0 hlit
  rwa [k6m_V8_swap] at this

/-- `K16mH5b` with the rules r3 (`L15`), r7 (`L14`), r8 (`a-b'`), r6 (`L06`) removed as well. -/
def K20mH5c (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K16mH5b a a' b b' c c' d α1 β1 β6 γ6 ∧
    ⟪b' - a, k20V3 a c d α1 (β6 + γ6 - β1)⟫ ≤ 0 ∧
    ((β1 - 1) * (α1 - 1) * γ6 < α1 * β1 * (1 - β6) →
      ⟪a' - c, k20V7 a c d (α1 * (1 - β6)) ((β1 - 1) * γ6)⟫ ≤ 0) ∧
    (α1 * β1 * (1 - β6) < γ6 * (α1 - 1) * (β1 - 1) → ⟪c - a', a - b'⟫ ≤ 0) ∧
    ((β1 - 1) * (α1 - 1) * β6 < α1 * β1 * (1 - γ6) →
      ⟪a' - b, k20V7 a b d (α1 * (1 - γ6)) ((β1 - 1) * β6)⟫ ≤ 0)

theorem k20h_h5 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : K16mH5b a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K20mH5c a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  have hh := h
  obtain ⟨⟨⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl4⟩, _, _⟩, _, _⟩ := hh
  by_cases l3 : 0 < ⟪b' - a, k20V3 a c d α1 (β6 + γ6 - β1)⟫
  · exact Or.inl (k20_r3_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l3)
  by_cases l7 : (β1 - 1) * (α1 - 1) * γ6 < α1 * β1 * (1 - β6) ∧
      0 < ⟪a' - c, k20V7 a c d (α1 * (1 - β6)) ((β1 - 1) * γ6)⟫
  · exact Or.inl (k20_r7_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l7.1 l7.2)
  by_cases l8 : α1 * β1 * (1 - β6) < γ6 * (α1 - 1) * (β1 - 1) ∧ 0 < ⟪c - a', a - b'⟫
  · exact Or.inl (k20_r8_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l8.1 l8.2)
  by_cases l6 : (β1 - 1) * (α1 - 1) * β6 < α1 * β1 * (1 - γ6) ∧
      0 < ⟪a' - b, k20V7 a b d (α1 * (1 - γ6)) ((β1 - 1) * β6)⟫
  · exact Or.inl (k20_r6_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hM l6.1 l6.2)
  refine Or.inr ⟨h, not_lt.1 l3, fun hl => not_lt.1 (fun hh => l7 ⟨hl, hh⟩),
    fun hl => not_lt.1 (fun hh => l8 ⟨hl, hh⟩), fun hl => not_lt.1 (fun hh => l6 ⟨hl, hh⟩)⟩

end C2
end Type08Sp
end Minimality
