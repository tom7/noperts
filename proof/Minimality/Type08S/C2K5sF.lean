module

public import Minimality.Type08S.C2K5sE

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexUni6_gen (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h50 : LexLt (z 5, w 5) (z 0, w 0))
    (h3 : LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4))
    (h4 : LexLt (z 4, w 4) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 5, w 5)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 6 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g => Fin.sum_univ_six (f := g)
  rw [hs]
  have e0 : (0 : ZMod 6) - 1 = 5 := by decide
  have e1 : (1 : ZMod 6) - 1 = 0 := by decide
  have e2 : (2 : ZMod 6) - 1 = 1 := by decide
  have e3 : (3 : ZMod 6) - 1 = 2 := by decide
  have e4 : (4 : ZMod 6) - 1 = 3 := by decide
  have e5 : (5 : ZMod 6) - 1 = 4 := by decide
  have f0 : (0 : ZMod 6) + 1 = 1 := by decide
  have f1 : (1 : ZMod 6) + 1 = 2 := by decide
  have f2 : (2 : ZMod 6) + 1 = 3 := by decide
  have f3 : (3 : ZMod 6) + 1 = 4 := by decide
  have f4 : (4 : ZMod 6) + 1 = 5 := by decide
  have f5 : (5 : ZMod 6) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) +
    (if LexLt (z (5 - 1), w (5 - 1)) (z 5, w 5) ∧ LexLt (z (5 + 1), w (5 + 1)) (z 5, w 5) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5]
  have a01 := lexLt_asymm h01
  have a21 := lexLt_asymm h21
  have a50 := lexLt_asymm h50
  rcases h3 with h3 | h3 <;> have a3 := lexLt_asymm h3 <;>
    rcases h4 with h4 | h4 <;> have a4 := lexLt_asymm h4 <;>
    first | exact (a3 h4).elim | simp [h01, a01, h21, a21, h50, a50, h3, a3, h4, a4]

end C2
end Type08Sp
end Minimality
