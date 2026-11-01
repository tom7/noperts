module

public import Minimality.Type08S.C2K5BB

@[expose] public section


/-!
# K5b / C: the two cells at `b - c` in frame form.
`k5b_cell1_hasLexCellAt`: `(a, b', a', b, d)` (= `(a,d,b,a',b')`), `k5b_cell2_hasLexCellAt`: `(a, c', a', c, d)`
(= `(a,d,c,a',c')`).  Both take the five strict-depth peak exclusions `k5b_ex5` for the cycle depths.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Peak exclusions for the five depths `z0..z4` of a 5-cycle: for each pair `(i, i+2)` a strict inequality. -/
def k5b_ex5 (z0 z1 z2 z3 z4 : ℝ) : Prop :=
  (z0 < z4 ∨ z0 < z1 ∨ z2 < z1 ∨ z2 < z3) ∧ (z1 < z0 ∨ z1 < z2 ∨ z3 < z2 ∨ z3 < z4) ∧
  (z2 < z1 ∨ z2 < z3 ∨ z4 < z3 ∨ z4 < z0) ∧ (z3 < z2 ∨ z3 < z4 ∨ z0 < z4 ∨ z0 < z1) ∧
  (z4 < z3 ∨ z4 < z0 ∨ z1 < z0 ∨ z1 < z2)

theorem k5b_ex_of (z : ZMod 5 → ℝ) (h : k5b_ex5 (z 0) (z 1) (z 2) (z 3) (z 4)) :
    ∀ i : ZMod 5, z i < z (i - 1) ∨ z i < z (i + 1) ∨ z (i + 2) < z (i + 2 - 1) ∨
      z (i + 2) < z (i + 2 + 1) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have e1 : (0 : ZMod 5) - 1 = 4 := by decide
  have e2 : (1 : ZMod 5) - 1 = 0 := by decide
  have e3 : (2 : ZMod 5) - 1 = 1 := by decide
  have e4 : (3 : ZMod 5) - 1 = 2 := by decide
  have e5 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have g0 : (0 : ZMod 5) + 2 = 2 := by decide
  have g1 : (1 : ZMod 5) + 2 = 3 := by decide
  have g2 : (2 : ZMod 5) + 2 = 4 := by decide
  have g3 : (3 : ZMod 5) + 2 = 0 := by decide
  have g4 : (4 : ZMod 5) + 2 = 1 := by decide
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, g0, g1, g2, g3, g4] <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

end C2
end Type08Sp
end Minimality
