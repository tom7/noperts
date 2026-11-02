module

public import Minimality.Type08S.C2K6HE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover of the H1 tree: the literal `ζ_{d-a'}(a, c') > 0` and either the tie `ζ_{a-b'}(c, a') = 0` or the
leaf `L2` (`ζ_{a-b'}(c, a') > 0`, `ζ_{a-b'}(a, c') ≤ 0`; new cell `(a, b', a', c')` at `b' - c`, NOT proved: its depth
facts do not follow from `K6sM` and the literals alone). -/
def K6mH1Left (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K6mH1 α1 β1 β6 γ6 ∧ 0 < ⟪a - c', d - a'⟫ ∧
    (⟪c - a', a - b'⟫ = 0 ∨ (0 < ⟪c - a', a - b'⟫ ∧ ⟪a - c', a - b'⟫ ≤ 0))

/-- **Box H1** (QN2 on M): leaves `L1` (a-b'), `L3` (a-b'), `L4` (a-c') closed; the tie and leaf `L2` stay. -/
theorem k6mh1_close {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (hs : K6sMN2 a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hH : K6mH1 α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨-, -, hM⟩ := hs
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  obtain ⟨hα1, hβ1, -, hβ6, hγ6⟩ := id hH
  rcases le_or_gt ⟪a - c', d - a'⟫ 0 with h1 | h1
  · exact Or.inl (k6mh1_L4 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hM h1)
  rcases lt_trichotomy ⟪c - a', a - b'⟫ 0 with h2 | h2 | h2
  · exact Or.inl (k6mh1_cell2 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hM h2)
  · exact Or.inr ⟨hH, h1, Or.inl h2⟩
  rcases lt_or_ge 0 ⟪a - c', a - b'⟫ with h3 | h3
  · exact Or.inl (k6mh1_cell1 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hM h2 h3)
  · exact Or.inr ⟨hH, h1, Or.inr ⟨h2, h3⟩⟩

/-- `K6sMLeftN2` without the open H1 disjunct (replaced by the tie / leaf-`L2` leftover `K6mH1Left`). -/
def K6sMLeftN2' (a a' b b' c c' d : ℝ³) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (K6mBoundary α1 β1 β6 γ6 ∨ K6mTie a a' b b' c c' α1 β1 β6 γ6 ∨ K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∨
      K6mH5 α1 β1 β6 γ6)

theorem k6mh1_left {a a' b b' c c' d : ℝ³} (h : K6sMLeftN2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sMLeftN2' a a' b b' c c' d := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, h0 | h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inl h0)⟩
  · rcases k6mh1_close hs hC h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inr (Or.inl h1))⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inr (Or.inr h0))⟩

end C2
end Type08Sp
end Minimality
